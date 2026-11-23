#!/usr/bin/env python3
"""Fail a pull request that adds a risky construct to the proof sources.

`verification/static-scan.txt` lists constructs the proof must not need, such as `sorry`, a
declared axiom or `native_decide`. The full build does not notice them: a `sorry` only warns,
and an added axiom compiles silently. This check fails a pull request that adds one.

The workflow runs this from its trusted checkout. The pull request's commits are fetched as
git objects and read. Nothing from the pull request is checked out or run.

For every Lean file under `src/` that the pull request adds or changes, comments and string
literals are removed and each construct is counted where the pull request branched off and at
its head. A count that went up fails the check. `src/Challenge.lean` is left out: it states the
theorems with `sorry`, and challenge-files.yml keeps it unchanged.

A text search is not a proof. It catches the accident. It does not catch a term that
metaprogramming builds under another name; the axiom check in Comparator does.
"""
from __future__ import annotations

import argparse
import bisect
import re
import secrets
import subprocess
import sys

# Lean modules live under this directory.
SOURCE, LEAN = b"src/", b".lean"
# States the theorems with `sorry`. challenge-files.yml keeps it unchanged.
EXEMPT = {b"src/Challenge.lean"}
# The constructs, as (name, pattern). They are the rows of verification/static-scan.txt for
# which these patterns find nothing on main today (three of them, addDecl, modifyEnv and
# run_cmd, had entries in the original files), and two more ways to write the first rows: the
# `stop` tactic and `native := true`. Each pattern is matched against the text of a Lean file
# with comments and string literals removed.
#
# `stop` closes the goal with `sorry`, and a field or a hypothesis may have the same name. So
# it is only counted where a tactic stands: alone on its line, or right after `by`, `=>`, `;`,
# `<;>`, a bullet, `try`, `all_goals`, `any_goals`, `then`, `else`, `<|>` or the `|` of `first`.
# A `stop` followed by tactics at the start of a line is not seen.
NOT_A_NAME = r"\b(?!')(?![ \t]*(?:=>|:|\.|,|\)|\]|\}|\||with\b))"
STOP = (r"^[ \t]+stop[ \t]*$"
        r"|(?:(?<![\w'.])(?:by|try|all_goals|any_goals|then|else)|decreasing_by|=>|;|<;>|·|^[ \t]*\.|<\|>)"
        r"[ \t]+stop" + NOT_A_NAME +
        # After `|` it is a tactic in `first | stop ... | ...`, and a pattern in `| stop h => ...`.
        r"|\|[ \t]+stop" + NOT_A_NAME + r"(?![^|\n]*=>)")
CONSTRUCTS = (
    ("sorry", r"\b(?:sorry|sorryAx)\b"),
    ("stop", STOP),
    ("admit", r"\badmit\b"),
    ("axiom", r"\baxiom\b"),
    ("native_decide",
     r"\b(?:native_decide|ofReduceBool|trustCompiler|bv_decide)\b|\+native\b|\bnative\s*:=\s*true\b"),
    ("implemented_by or extern", r"\b(?:implemented_by|extern)\b"),
    ("unsafe", r"\bunsafe\b"),
    ("opaque", r"\bopaque\b"),
    ("set_option debug", r"\bset_option\s+debug\."),
    ("skipKernelTC", r"\bskipKernelTC\b"),
    ("addDecl or addAndCompile", r"\b(?:addDecl|addAndCompile)\b"),
    ("modifyEnv or setEnv", r"\b(?:modifyEnv|setEnv)\b"),
    ("run_cmd, run_elab, run_meta or #eval", r"\b(?:run_cmd|run_elab|run_meta)\b|#eval\b"),
    ("initialize", r"\b(?:initialize|builtin_initialize)\b"),
)
PATTERNS = tuple((name, re.compile(pattern, re.MULTILINE)) for name, pattern in CONSTRUCTS)
# A word that every pattern needs. Nearly every file has none of them and is not read more
# closely. This looks at the raw text, comments included, so it must not ask for more than a word.
ANY = re.compile(r"sorry|stop|admit|axiom|native|ofReduceBool|trustCompiler|bv_decide|implemented_by|extern|unsafe"
                 r"|opaque|debug|skipKernelTC|addDecl|addAndCompile|modifyEnv|setEnv|run_cmd|run_elab|run_meta"
                 r"|#eval|initialize")
# Files read from git in one process.
BATCH = 2000
# Most lines listed for one construct in one file.
LISTED = 5

# A character literal, as opposed to the prime of a name such as `h'`.
CHARACTER = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
# The opening of a raw string: r"..." or r#"..."#.
RAW = re.compile(r'r(#*)"')
# Where a comment, a string or a character literal may begin.
OPENING = re.compile(r"""--|/-|"|'|r#*\"""")
# The next opening or closing of a block comment. Block comments nest.
NESTING = re.compile(r"/-|-/")
# A string literal with its escapes.
QUOTE = re.compile(r'"(?:[^"\\]|\\.)*"', re.DOTALL)


def run(args, *, data=None, ok=(0,)):
    """Run a command and return (exit code, stdout). Any exit code outside `ok` is an error."""
    done = subprocess.run(args, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode not in ok:
        sys.stderr.write(done.stderr.decode("utf-8", "replace"))
        raise RuntimeError(f"{args[0]} failed with exit code {done.returncode}")
    return done.returncode, done.stdout


def git(repo, *args, data=None, ok=(0,), config=()):
    settings = [part for item in config for part in ("-c", item)]
    return run(["git", "-C", str(repo), *settings, *args], data=data, ok=ok)


# ---------------------------------------------------------------------------------------------
# Reading one Lean file.


def code(text):
    """`text` with comments and string literals blanked out. Line breaks stay where they are."""
    out, at, end = [], 0, len(text)
    while at < end:
        opening = OPENING.search(text, at)
        if not opening:
            out.append(text[at:])
            break
        start = opening.start()
        out.append(text[at:start])
        if text.startswith("--", start):
            stop = text.find("\n", start)
            stop = end if stop < 0 else stop
        elif text.startswith("/-", start):
            # `/--` opens a comment as a whole: after `/--/` the comment is still open.
            depth, stop = 1, start + (3 if text.startswith("/--", start) else 2)
            while depth:
                nested = NESTING.search(text, stop)
                if not nested:
                    stop = end
                    break
                depth += 1 if nested.group() == "/-" else -1
                stop = nested.end()
        elif text[start] == '"':
            closing = QUOTE.match(text, start)
            stop = closing.end() if closing else end
        elif text[start] == "r" and not name_before(text, start):
            close = '"' + RAW.match(text, start).group(1)
            stop = text.find(close, text.index('"', start) + 1)
            stop = end if stop < 0 else stop + len(close)
        elif text[start] == "'" and not name_before(text, start) and (literal := CHARACTER.match(text, start)):
            stop = literal.end()
        else:  # the prime of a name, or an `r` inside one
            out.append(text[start])
            at = start + 1
            continue
        out.append("".join(char if char == "\n" else " " for char in text[start:stop]))
        at = stop
    return "".join(out)


def name_before(text, at):
    """Whether the character before `at` can end a name, so that `'` or `r` continues it."""
    return at > 0 and (text[at - 1].isalnum() or text[at - 1] in "_'!?.")


def scan(contents):
    """The constructs in one Lean file, as {name: [line numbers]}."""
    found = {}
    text = contents.decode("utf-8", "replace")
    if not ANY.search(text):
        return found
    text = code(text)
    breaks = [at for at, char in enumerate(text) if char == "\n"]
    for name, pattern in PATTERNS:
        # A match that runs over a line break is counted where it begins.
        lines = [bisect.bisect_left(breaks, match.start()) + 1 for match in pattern.finditer(text)]
        if lines:
            found[name] = lines
    return found


# ---------------------------------------------------------------------------------------------
# Comparing two commits in a local repository.


def lean_files(repo, fork, head):
    """Lean files under src/ that `head` adds or changes relative to `fork`. Reads trees only."""
    _, out = git(repo, "diff", "--name-only", "--no-renames", "--diff-filter=AM", "-z", fork, head)
    return sorted(path for path in out.split(b"\0")
                  if path.startswith(SOURCE) and path.endswith(LEAN) and path not in EXEMPT)


def all_lean_files(repo, commit):
    """Every Lean file under src/ at `commit`. Reads trees only."""
    _, out = git(repo, "ls-tree", "-r", "-z", "--name-only", commit, "--", SOURCE.decode())
    return sorted(path for path in out.split(b"\0") if path.endswith(LEAN) and path not in EXEMPT)


def blob_ids(repo, commit, paths):
    """The blob of each of `paths` that exists at `commit`, as {path: id}. Reads trees only."""
    found = {}
    paths = sorted(paths)
    for start in range(0, len(paths), 200):
        chunk = paths[start:start + 200]
        _, out = git(repo, "--literal-pathspecs", "ls-tree", "-r", "-z", commit, "--", *chunk)
        for entry in out.split(b"\0"):
            meta, _, path = entry.partition(b"\t")
            meta = meta.split()
            if len(meta) == 3 and meta[1] == b"blob":
                found[path] = meta[2]
    return found


def fetch_ids(repo, wanted):
    """Fetch blobs by id in one request, for a clone without blobs."""
    if wanted:
        git(repo, "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "--recurse-submodules=no",
            "--filter=blob:none", "--stdin", "origin", data=b"\n".join(sorted(wanted)) + b"\n",
            config=("fetch.negotiationAlgorithm=noop",))


def read_blobs(repo, ids):
    """The contents of blobs that are already here, as {id: contents}, from one git process."""
    ids = sorted(set(ids))
    if not ids:
        return {}
    _, out = git(repo, "cat-file", "--batch", data=b"\n".join(ids) + b"\n")
    found, at = {}, 0
    for wanted in ids:
        end = out.index(b"\n", at)
        header = out[at:end].split()
        at = end + 1
        if len(header) == 3:  # "<id> <type> <size>"; a blob that is not here gives "<id> missing"
            size = int(header[2])
            found[wanted] = out[at:at + size]
            at += size + 1
    return found


def scan_files(repo, commit, paths, *, fetch):
    """The constructs in `paths` at `commit`, as {path: {name: [line numbers]}}. Clean files are left out."""
    found = {}
    ids = blob_ids(repo, commit, paths)
    if fetch:
        fetch_ids(repo, set(ids.values()))
    paths = sorted(ids)
    for start in range(0, len(paths), BATCH):
        chunk = paths[start:start + BATCH]
        contents = read_blobs(repo, [ids[path] for path in chunk])
        for path in chunk:
            if ids[path] not in contents:
                raise RuntimeError(f"could not read {show(path)} at {commit}")
            constructs = scan(contents[ids[path]])
            if constructs:
                found[path] = constructs
    return found


def added(repo, fork, head, *, fetch=False):
    """What `head` adds relative to `fork`, as [(path, name, count before, [line numbers at head])].

    A construct counts as added in a file when the file has more of it at `head` than at `fork`.
    """
    after = scan_files(repo, head, lean_files(repo, fork, head), fetch=fetch)
    before = scan_files(repo, fork, after, fetch=fetch) if after else {}
    findings = []
    for path in sorted(after):
        for name, lines in after[path].items():
            earlier = len(before.get(path, {}).get(name, ()))
            if len(lines) > earlier:
                findings.append((path, name, earlier, lines))
    return findings


def everything(repo, commit, *, fetch=False):
    """Every construct under src/ at `commit`, in the form `added` returns."""
    found = scan_files(repo, commit, all_lean_files(repo, commit), fetch=fetch)
    return [(path, name, 0, lines) for path in sorted(found) for name, lines in found[path].items()]


# ---------------------------------------------------------------------------------------------
# Reporting.


def show(path):
    """A path for printing. Control characters are escaped, so that a file name cannot begin a new line."""
    text = path.decode("utf-8", "replace")
    return "".join(char if char.isprintable() else f"\\x{ord(char):02x}" for char in text)


def escaped(text, *, properties=False):
    """`text` as the message of a workflow command, or as the value of one of its properties."""
    pairs = [("%", "%25"), ("\r", "%0D"), ("\n", "%0A")] + ([(":", "%3A"), (",", "%2C")] if properties else [])
    for char, replacement in pairs:
        text = text.replace(char, replacement)
    return text


def report(findings, *, resume=None):
    """Print the findings, one line per construct and file. Returns the exit code.

    `resume` is the token that switches workflow commands back on. With it, one error annotation
    per finding follows the listing. The listing itself is printed while commands are off, since
    file names come from the pull request.
    """
    for path, name, earlier, lines in findings:
        listed = ", ".join(str(line) for line in lines[:LISTED]) + (", ..." if len(lines) > LISTED else "")
        was = f" (this file had {earlier} before)" if earlier else ""
        print(f"{show(path)}: {name}: line {listed}{was}")
    if findings:
        print()
        print("The proof must not need these constructs (verification/NOTES.md, Static scan).")
        print("A maintainer who means to allow one has to say so and change scripts/risky-constructs.py.")
    else:
        print("No risky construct was added.")
    if resume:
        print(f"::{resume}::")
        for path, name, _, lines in findings:
            said = escaped(f"This pull request adds `{name}` to {show(path)}.")
            print(f"::error file={escaped(show(path), properties=True)},line={lines[0]}::{said}")
    return 1 if findings else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--work", required=True, help="a git repository; created and filled when --remote is given")
    parser.add_argument("--remote", help="fetch the commits from this URL into --work, without file contents")
    parser.add_argument("--base", help="the commit the pull request is to be merged into")
    parser.add_argument("--head", help="the pull request's head commit")
    parser.add_argument("--all", metavar="COMMIT", help="scan every Lean file under src/ at this commit instead")
    parser.add_argument("--annotate", action="store_true",
                        help="run as a workflow step: print error annotations, and keep everything else from being read as a workflow command")
    args = parser.parse_args()
    if bool(args.all) == bool(args.base and args.head):
        parser.error("give either --base and --head, or --all")

    resume = None
    if args.annotate:
        # File names, and what git says about them, come from the pull request. A line with
        # `::name::` or `##[name]` in it is a workflow command, so commands are switched off
        # until the annotations are printed. The token is random: the pull request cannot know it.
        resume = secrets.token_hex(16)
        print(f"::stop-commands::{resume}")
    commits = [args.all] if args.all else [args.base, args.head]
    if args.remote:
        run(["git", "init", "--quiet", args.work])
        git(args.work, "remote", "add", "origin", args.remote, ok=(0, 3))  # 3: it is there already
        # Commits and trees, without file contents. The history comes with it, so the commit
        # where the pull request branched off is worked out here.
        git(args.work, "fetch", "--quiet", "--filter=blob:none", "--no-tags", "--recurse-submodules=no",
            "origin", *commits)
    if args.all:
        findings = everything(args.work, args.all, fetch=bool(args.remote))
    else:
        code_, out = git(args.work, "merge-base", args.base, args.head, ok=(0, 1))
        if code_:
            raise RuntimeError("the pull request and its base branch have no common commit")
        fork = out.decode().strip()
        print(f"branched off at {fork}, head {args.head}")
        findings = added(args.work, fork, args.head, fetch=bool(args.remote))
    return report(findings, resume=resume)


if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)  # keep stdout and git's stderr in order in the log
    try:
        sys.exit(main())
    except RuntimeError as error:
        sys.exit(f"risky-constructs: {error}")
