#!/usr/bin/env python3
"""Fail a pull request that adds a risky construct to the proof sources.

`verification/static-scan.txt` lists constructs the proof must not need, such as `sorry`, a
declared axiom or `native_decide`. The full build does not notice them: a `sorry` only warns,
and an added axiom compiles silently. This check fails a pull request that adds one.

The workflow runs this from its trusted checkout. The pull request's commits are fetched as
git objects and read. Nothing from the pull request is checked out or run.

It is a plain search of the text. For every Lean file under `src/` that the pull request adds
or changes, the whole text is searched for the words of the list below, comments and strings
included. A line that holds a word is reported, unless the file had the same line, apart from
blanks, at the commit where the pull request branched off. Nothing of the text is left out, so
no mistake in this script can hide a word behind what stands before it. The price: a word in a
comment or inside a longer name is reported like one in a proof, and a renamed file counts as a
new one. `src/Challenge.lean` is not read: it states the theorems with `sorry`, and
challenge-files.yml keeps it unchanged. A symbolic link or a submodule under `src/` is
reported too: git has the path of its target there, not the text Lean would read.

A line that is meant to stand goes into `scripts/risky-constructs-allowed.txt`. The workflow
reads that file from the default branch, so a pull request cannot allow itself.

This catches the accident. What it does not see:
- a line that was in the file already and means something else now: a `sorry` in a comment
  block is not reported when a later pull request removes the comment's ends;
- a name that a macro puts together from pieces;
- Mathlib's `hint` tactic, which closes a goal with `sorry` when nothing else does: `hint` is
  the name of a hypothesis on thousands of lines of the tree;
- a `decide` whose config stands on another line;
- grind's trace mode where a config switches it on through a field path
  (`c.trace := true`), or with a type or a comment between `trace` and `:=`
  (`trace : Bool := true`);
- anything outside `src/`.
The axiom check and the kernel replay in Comparator are what counts.
"""
from __future__ import annotations

import argparse
import bisect
import collections
from pathlib import Path
import re
import secrets
import subprocess
import sys

# Lean modules live under this directory.
SOURCE, LEAN = b"src/", b".lean"
# States the theorems with `sorry`. challenge-files.yml keeps it unchanged.
EXEMPT = {b"src/Challenge.lean"}
# No name character follows. Where one does, Lean reads a longer name: `stopping`, `admits`,
# `axioms`, `external`, `impossible_case`. What stands before a word is not looked at, because
# Lean does not look either: it reads `2axiom cheat : False` as a number and an axiom.
END = r"(?![A-Za-z0-9_])"
# The words, as (name, pattern). The name is what a report says.
#
# sorry          in any case and inside any name: `sorryAx`, `mkSorry`, `warn.sorry`
# stop, admit    tactics that close a goal with `sorry`, as `apply?`, `impossible` and `plausible`
#                do
# grind?         grind's trace mode closes a goal it cannot prove with `sorry`. `grind?` switches
#                it on, `finish?` inside `grind =>` does, and so do `+trace` and
#                `(trace := true)` behind `grind`, `lia`, `cutsat` and `grobner`. The value can
#                be written in many ways (`.true`, `!false`), so `trace :=` counts whatever
#                follows, where `trace` is a name of its own: `M.trace := by` is another name.
#                A field `trace` of a structure is reported too.
# guard_msgs     `#guard_msgs (drop error) in` takes the error of a failed proof away: the file
#                compiles without a message and the theorem rests on `sorryAx`. In any case
#                and without the underscore too, for `guardMsgsCmd` and `elabGuardMsgs`
# native         `native_decide`, `+native`, `native := true`; after a letter the lower-case
#                word is passed over, as in `alternative`
# decide-config  a `decide` with a config on its line, and `config := ⟨`: both can switch the
#                compiler on without the word `native`. The one pattern of two words: a line
#                break between them hides it.
# init           the attribute, in `@[init]`, `@[init f]` and `attribute [init] f`: it runs code
#                when the module is imported, as `initialize` does. Only as a name of its own,
#                which is how Lean reads an attribute: `Fin.init`, `init_x`, `builtin_init` and
#                `initial` are other names. A variable `init` is reported too.
# the rest       ways to declare an axiom from code, to change what is compiled, or to change
#                what the environment holds
CONSTRUCTS = (
    ("sorry", r"(?i:sorry)"),
    ("stop", "stop" + END),
    ("admit", "admit" + END),
    ("admitGoal", "admitGoal"),
    ("apply?", r"apply\?"),
    ("grind?", r"grind\?"),
    ("finish?", r"finish\?"),
    ("+trace", r"\+«?trace" + END),
    ("trace :=", r"(?<![A-Za-z0-9_.'!?])«?trace»?\s*:="),
    ("impossible", "impossible" + END),
    ("plausible", "plausible"),
    ("guard_msgs", r"(?i:guard_?msgs)"),
    ("axiom", "axiom" + END),
    ("elabAxiom", "elabAxiom"),
    ("axiomDecl", "axiomDecl"),
    ("native", r"(?i:native_?decide)|(?<![A-Za-z])native"),
    ("bv_decide", "bv_decide"),
    ("bv_check", "bv_check"),
    ("decide-config", r"decide[^\n]*config|config\s*:=\s*⟨"),
    ("implemented_by", "implemented_by"),
    ("extern", "extern" + END),
    ("unsafe", "unsafe"),
    ("opaque", "opaque"),
    ("debug", "debug"),
    ("addDecl", "addDecl"),
    ("addAndCompile", "addAndCompile"),
    ("modifyEnv", "modifyEnv"),
    ("setEnv", "setEnv"),
    ("run_cmd", "run_cmd"),
    ("run_elab", "run_elab"),
    ("run_meta", "run_meta"),
    ("#eval", "#eval"),
    ("initialize", "initialize"),
    ("init", r"(?<![A-Za-z0-9_.'!?])init(?![A-Za-z0-9_'!?])"),
)
PATTERNS = tuple((name, re.compile(pattern)) for name, pattern in CONSTRUCTS)
# Any of them. Nearly every file has none and is looked at once.
ANY = re.compile("|".join(f"(?:{pattern})" for _, pattern in CONSTRUCTS))
# What a symbolic link or a submodule under src/ is reported as.
LINK = "link"
LINK_MODES = (b"120000", b"160000")
# The lines that may stand, next to this script.
ALLOWED = Path(__file__).with_name("risky-constructs-allowed.txt")
# Files read from git in one process.
BATCH = 2000
# Most lines printed for one word in one file, and most lines offered for the list.
LISTED, OFFERED = 5, 50


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


def squeezed(line):
    """A line without the blanks at its ends, and with one blank for each run of blanks inside it."""
    return " ".join(line.split())


def scan(contents):
    """The lines of one Lean file that hold a word, as {name: [(line number, the line squeezed)]}."""
    found = {}
    text = contents.decode("utf-8", "replace")
    if not ANY.search(text):
        return found
    lines = text.split("\n")
    breaks = [at for at, char in enumerate(text) if char == "\n"]
    for name, pattern in PATTERNS:
        numbers = sorted({bisect.bisect_left(breaks, match.start()) for match in pattern.finditer(text)})
        if numbers:
            found[name] = [(number + 1, squeezed(lines[number])) for number in numbers]
    return found


def allowances(path):
    """The lines that may stand, as {(path, the line squeezed)}.

    A line of the list is `<path>: <the line as it stands in that file>`. Empty lines and lines
    that begin with `#` are passed over. Any other line is an error. No file: nothing may stand.
    """
    allowed = set()
    try:
        lines = Path(path).read_text(encoding="utf-8").split("\n")
    except FileNotFoundError:
        return allowed
    for number, line in enumerate(lines, 1):
        if not line.strip() or line.startswith("#"):
            continue
        file, _, text = line.partition(": ")
        if not (file.startswith("src/") and file.endswith(".lean") and squeezed(text)):
            raise RuntimeError(f"{path}, line {number}: expected `<a Lean file under src/>: <the line that may stand>`")
        allowed.add((file.encode("utf-8"), squeezed(text)))
    return allowed


# ---------------------------------------------------------------------------------------------
# Comparing two commits in a local repository.


def changed(repo, fork, head):
    """What `head` adds or changes under src/ relative to `fork`. Reads trees only.

    Returns the Lean files as [(path, blob at fork or None, blob at head)], and the paths that
    are a symbolic link or a submodule at `head` and were none at `fork`.
    """
    _, out = git(repo, "diff", "--raw", "--no-abbrev", "--no-renames", "--diff-filter=AMT", "-z", fork, head)
    fields = out.split(b"\0")
    files, links = [], []
    for entry, path in zip(fields[0::2], fields[1::2]):
        mode_before, mode_after, before, after, status = entry.lstrip(b":").split()
        if not path.startswith(SOURCE):
            continue
        if mode_after in LINK_MODES:
            if mode_before not in LINK_MODES:
                links.append(path)
        elif path.endswith(LEAN) and path not in EXEMPT:
            files.append((path, None if status == b"A" or mode_before in LINK_MODES else before, after))
    return sorted(files), sorted(links)


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
            if header[1] == b"blob":
                found[wanted] = out[at:at + size]
            at += size + 1
    return found


def scan_blobs(repo, files, *, fetch):
    """The lines with a word in `files`, given as [(path, blob)]: {path: what `scan` returns}. Files without any are left out."""
    found = {}
    if fetch:
        fetch_ids(repo, {blob for _, blob in files})
    for start in range(0, len(files), BATCH):
        chunk = files[start:start + BATCH]
        contents = read_blobs(repo, [blob for _, blob in chunk])
        for path, blob in chunk:
            if blob not in contents:
                raise RuntimeError(f"could not read {shown(path)}")
            words = scan(contents[blob])
            if words:
                found[path] = words
    return found


def added(repo, fork, head, *, allowed=(), fetch=False):
    """What `head` adds relative to `fork`, as [(path, name, [(line number, the line)])].

    A line with a word counts as added when the file as it was at `fork` has no line left to
    pair it with: the same line apart from blanks, holding the same word. Lines in `allowed`
    are passed over. A new link has the name LINK and no lines.
    """
    files, links = changed(repo, fork, head)
    after = scan_blobs(repo, [(path, blob) for path, _, blob in files], fetch=fetch)
    before = scan_blobs(repo, [(path, blob) for path, blob, _ in files if blob and path in after], fetch=fetch)
    findings = [(path, LINK, []) for path in links]
    for path in sorted(after):
        for name, lines in after[path].items():
            had = collections.Counter(text for _, text in before.get(path, {}).get(name, ()))
            new = []
            for number, text in lines:
                if had[text]:
                    had[text] -= 1
                elif (path, text) not in allowed:
                    new.append((number, text))
            if new:
                findings.append((path, name, new))
    return sorted(findings, key=lambda finding: finding[0])


# ---------------------------------------------------------------------------------------------
# Reporting.


def shown(text):
    """A path or a line for printing. Control characters are escaped, so that it cannot begin a new line."""
    if isinstance(text, bytes):
        text = text.decode("utf-8", "replace")
    return "".join(char if char.isprintable() else f"\\x{ord(char):02x}" for char in text)


def escaped(text, *, properties=False):
    """`text` as the message of a workflow command, or as the value of one of its properties."""
    pairs = [("%", "%25"), ("\r", "%0D"), ("\n", "%0A")] + ([(":", "%3A"), (",", "%2C")] if properties else [])
    for char, replacement in pairs:
        text = text.replace(char, replacement)
    return text


def report(findings, *, resume=None):
    """Print the findings. Returns the exit code.

    `resume` is the token that switches workflow commands back on. With it, one error annotation
    per file and word follows the listing. The listing itself is printed while commands are off,
    since file names and lines come from the pull request.
    """
    offered = []
    for path, name, lines in findings:
        if name == LINK:
            print(f"{shown(path)}: a symbolic link or a submodule")
        for number, text in lines[:LISTED]:
            print(f"{shown(path)}:{number}: {name}: {shown(text)}")
        if len(lines) > LISTED:
            print(f"{shown(path)}: {name}: and {len(lines) - LISTED} more lines")
        offered += [f"{shown(path)}: {shown(text)}" for _, text in lines]
    offered = list(dict.fromkeys(offered))
    if findings:
        print()
        print("The proof must not need these constructs (verification/NOTES.md, Static scan). The search")
        print("reads the whole text, so a word in a comment or inside a longer name is reported too.")
    if offered:
        print("To let a line stand, a maintainer adds it to scripts/risky-constructs-allowed.txt on the")
        print("default branch:")
        for line in offered[:OFFERED]:
            print(f"    {line}")
        if len(offered) > OFFERED:
            print(f"    and {len(offered) - OFFERED} more")
        print("A re-run of this job reads the list as it was. The pull request's next push or edit")
        print("starts a run that reads the new one.")
    if any(name == LINK for _, name, _ in findings):
        print("A link cannot be allowed: git has the path of its target, not the text Lean would read.")
    if not findings:
        print("No risky construct was added.")
    if resume:
        print(f"::{resume}::")
        for path, name, lines in findings:
            said = f"This pull request makes {shown(path)} a link." if name == LINK else f"This pull request adds `{name}` to {shown(path)}."
            print(f"::error file={escaped(shown(path), properties=True)},line={lines[0][0] if lines else 1}::{escaped(said)}")
    return 1 if findings else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--work", required=True, help="a git repository; created and filled when --remote is given")
    parser.add_argument("--remote", help="fetch the commits from this URL into --work, without file contents")
    parser.add_argument("--base", required=True, help="the commit the pull request is to be merged into")
    parser.add_argument("--head", required=True, help="the pull request's head commit")
    parser.add_argument("--allowed", default=ALLOWED, help="the list of lines that may stand (default: next to this script)")
    parser.add_argument("--annotate", action="store_true",
                        help="run as a workflow step: print error annotations, and keep everything else from being read as a workflow command")
    args = parser.parse_args()

    resume = None
    if args.annotate:
        # File names and lines, and what git says about them, come from the pull request. A line
        # with `::name::` or `##[name]` in it is a workflow command, so commands are switched off
        # until the annotations are printed. The token is random: the pull request cannot know it.
        resume = secrets.token_hex(16)
        print(f"::stop-commands::{resume}")
    allowed = allowances(args.allowed)
    if args.remote:
        run(["git", "init", "--quiet", args.work])
        git(args.work, "remote", "add", "origin", args.remote, ok=(0, 3))  # 3: it is there already
        # Commits and trees, without file contents. The history comes with it, so the commit
        # where the pull request branched off is worked out here.
        git(args.work, "fetch", "--quiet", "--filter=blob:none", "--no-tags", "--recurse-submodules=no",
            "origin", args.base, args.head)
    code, out = git(args.work, "merge-base", args.base, args.head, ok=(0, 1))
    if code:
        raise RuntimeError("the pull request and its base branch have no common commit")
    fork = out.decode().strip()
    print(f"branched off at {fork}, head {args.head}")
    return report(added(args.work, fork, args.head, allowed=allowed, fetch=bool(args.remote)), resume=resume)


if __name__ == "__main__":
    sys.stdout.reconfigure(line_buffering=True)  # keep stdout and git's stderr in order in the log
    try:
        sys.exit(main())
    except RuntimeError as error:
        print(f"risky-constructs: {error}", file=sys.stderr)
        sys.exit(2)  # not 1: nothing was compared
