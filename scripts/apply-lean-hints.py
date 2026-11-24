#!/usr/bin/env python3
"""Apply the edits that Lean prints with its warnings, at the places the build log names.

Some linters print the exact edit as a small diff:

    warning: src/A.lean:84:24: `if_neg` has been deprecated: Use `ite_eq_right` instead

    Hint: Replace the deprecated name:
      i̵f̵_̵n̵e̵g̵i̲t̲e̲_̲e̲q̲_̲r̲i̲g̲h̲t̲

In that line a character followed by U+0335 is to be deleted, one followed by U+0332 is to be
inserted, and any other character stays. The deprecation linter prints this when the new name
has the same type as the old one, and the `haveI` linter prints it under `Try this:`.

This script reads a log of `lake build` and makes such edits at the reported line and column,
after checking that the text to be replaced stands there. Without `--kind` it makes the two
kinds it was written for and checked on: deprecated names, and `haveI`/`letI`.

Which names it replaces. Only deprecated theorems, unless `--definitions` is given. A theorem
and its replacement of the same type are interchangeable in a proof. A definition is not: the
proof then names one constant and the statement another, and a `rw` that compiled stops
matching. Whether a name is a theorem is taken from Lean when `--kinds FILE` is given (the
output of the file that `--write-kind-check` writes, run with `lake env lean`; it
imports Mathlib only, so a name declared elsewhere comes back as missing and is left alone).
Without it the name has to read like a theorem: an underscore in its last part, as in `if_neg` and unlike
`Pi.monoidHom`. In the log this was written for, that rule called no definition a theorem and
left 42 of 758 theorems alone.

Where it edits. Only inside the proof of a `theorem` or `lemma`, unless `--everywhere` is given.
In a statement, or in the body of a definition or an instance, a file can still compile and say
something else. Those edits are left alone and counted. The test is by layout, on the text
with comments and strings blanked out: a command starts on a line that begins in the first
column with a word, `@[` or `#` (a comment may stand before it), and on any line that begins
with the keyword of a declaration, however far it is indented; its first word, after
attributes and modifiers, has to be `theorem` or `lemma`; and the proof starts after the first
`:=` outside brackets that does not belong to a `let` or `have` written before it. A `where`
ends the proof, since what follows may be definitions. Left alone are a theorem that does not
begin in the first column, and one proved by pattern matching whose first alternative reads
`| pattern =>` on one line. This fits sources laid out like this repository's. It is not a
parser: an attribute with brackets inside it, for one, hides its theorem, which is then left
alone.

What it does not trust. A message in the log can be made to look like a warning about any
file, so only regular files under `--within` (default `src`) inside `--root` are written, and
no part of their path may be a symbolic link. A warning whose text is not at its place is
skipped and counted, and the exit code is then 1: the file has changed since the log was made.
Files are written back byte for byte except for the edits.

Running it twice. An edit whose new text stands at its place counts as made already, also when
edits to its left have shifted the line, so the same log can be applied again, with the same
options or narrower ones. The price: a stale hint that happens to point at its own new text is
counted as made, not as missing. A hint that only deletes is not applied, because a second run
could not tell that it was made.

Nothing is built here. An edited file still has to be compiled; Lean's hint is a hint.

Usage: apply-lean-hints.py LOG [--root DIR] [--within DIR] [--dry-run] [--table] [--kinds FILE]
                               [--kind KIND] [--name NAME] [--definitions] [--everywhere]
       apply-lean-hints.py LOG --write-kind-check FILE
Exit code: 0; 1 when an edit did not find its text or its file was not written; 2 when an
option or an input file makes no sense.
"""
from __future__ import annotations

import argparse
import bisect
import collections
import os
from pathlib import Path
import re
import sys
import tempfile

STRUCK, UNDERLINED = "̵", "̲"
# The sign Python puts where the log was not UTF-8. It must not reach a source file.
UNREADABLE = "�"
# `warning: <file>:<line>:<column>: <text>`; the line counts from 1, the column from 0.
WARNING = re.compile(r"^warning: (?P<file>.+?\.lean):(?P<line>\d+):(?P<column>\d+): (?P<text>.*)$")
# A line of build progress or of another message ends the warning before it.
OTHER = re.compile(r"^(?:[⚠✔✖ℹ] \[\d+/\d+\]|info: |error: |warning: |Build completed|Some required)")
DEPRECATED = re.compile(r"^`(?P<name>[^`]+)` has been deprecated")
LINTER = re.compile(r"set_option (linter\.[A-Za-z0-9_.]+) false")
# The kinds applied when none is asked for.
KINDS = ("deprecated", "linter.style.haveILetI")

# Where a comment, a string or a character literal may begin.
OPENER = re.compile(r"""--|/-|"|'""")
NESTING = re.compile(r"/-|-/")
QUOTE = re.compile(r'"(?:[^"\\]|\\.)*"', re.DOTALL)
CHARACTER = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
# A command starts with a word, `@[` or `#`, on a line that begins in the first column.
COMMAND = re.compile(r"^(?:[A-Za-z_#]|@\[)")
# What may stand before the keyword of a declaration.
PREFIX = re.compile(r"^(?:@\[[^\]]*\]\s*|(?:private|protected|public|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*")
PROVES = re.compile(r"^(?:theorem|lemma)\b")
# A declaration starts a command wherever its line begins. Its keywords are no names, so a line
# of a proof cannot begin with one.
DECLARATION = re.compile(PREFIX.pattern + r"(?:theorem|lemma|def|instance|abbrev|structure|class|inductive|example|axiom|opaque)\b")
# The pieces of a statement that matter for finding its end. The first is the start of a line,
# with its `|` if it begins with one.
PIECE = re.compile(r"\n[ \t]*\|?|=>|:=|[^\W\d][\w'!?]*|[()\[\]{}⟨⟩]")
OPENING, CLOSING = "([{⟨", ")]}⟩"
# A `:=` after one of these, outside brackets, belongs to it and not to the theorem.
BINDS = ("let", "have", "haveI", "letI")

# A line of the kind check's output: the word KIND, the name, and what Lean says it is.
KIND = re.compile(r"^KIND\t(?P<name>[^\t]+)\t(?P<kind>\w+)$")
KIND_CHECK = '''import Mathlib

/-! Written by scripts/apply-lean-hints.py --write-kind-check. Run it with `lake env lean` and
give the output to `--kinds`: it says for each deprecated name of a build log what it is. -/

open Lean in
#eval show CoreM Unit from do
  let names : List String := [
  NAMES]
  let env ← getEnv
  for text in names do
    let kind := match env.find? text.toName with
      | some (.thmInfo _) => "theorem"
      | some (.defnInfo _) => "definition"
      | some (.inductInfo _) => "inductive"
      | some (.ctorInfo _) => "constructor"
      | some (.opaqueInfo _) => "opaque"
      | some (.axiomInfo _) => "axiom"
      | some (.recInfo _) => "recursor"
      | some (.quotInfo _) => "quot"
      | none => "missing"
    IO.println s!"KIND\\t{text}\\t{kind}"
'''


class Edit:
    def __init__(self, file, line, column, old, new, kind, name=None):
        self.file, self.line, self.column = os.path.normpath(file), line, column
        self.old, self.new = old, new
        self.kind = kind  # "deprecated", or the linter's option name
        self.name = name  # the deprecated name, when there is one

    def key(self):
        return (self.file, self.line, self.column, self.old, self.new)


# ---------------------------------------------------------------------------------------------
# Reading the log.


def diff(text):
    """The (old, new) pair that a line of struck and underlined characters stands for, or None."""
    old, new, at, marked = [], [], 0, False
    while at < len(text):
        char = text[at]
        mark = text[at + 1] if at + 1 < len(text) else ""
        if char in (STRUCK, UNDERLINED):
            return None  # a mark with nothing before it
        if mark == STRUCK:
            old.append(char)
            at, marked = at + 2, True
        elif mark == UNDERLINED:
            new.append(char)
            at, marked = at + 2, True
        else:
            old.append(char)
            new.append(char)
            at += 1
    old, new = "".join(old), "".join(new)
    if not marked or not old or old == new or UNREADABLE in old + new:
        return None
    return old, new


def warnings(lines):
    """The warnings of a log, as (file, line, column, text, following lines)."""
    current = None
    for raw in lines:
        # A carriage return inside a line comes from progress output; at its end, from Windows.
        for line in raw.rstrip("\r\n").split("\r"):
            start = WARNING.match(line)
            if start:
                if current:
                    yield current
                current = (start["file"], int(start["line"]), int(start["column"]), start["text"], [])
            elif OTHER.match(line):
                if current:
                    yield current
                current = None
            elif current:
                current[4].append(line)
    if current:
        yield current


def offered_lines(text, rest):
    """The lines in which a warning shows its edit: after `Try this:` or the deprecation hint, up to a blank line."""
    if "Try this:" in text:
        same_line = text.split("Try this:", 1)[1].strip()
        if same_line:
            return [same_line]
        below = rest
    else:
        header = next((at for at, line in enumerate(rest) if line.startswith("Hint: Replace the deprecated name")), None)
        if header is None:
            return []
        below = rest[header + 1:]
    shown = []
    for line in below:
        if not line.strip():
            break
        shown.append(line.strip())
    return shown


def edits(lines, skipped=None):
    """The edits a log offers. `skipped` counts the hints that look like a diff and are not used."""
    skipped = collections.Counter() if skipped is None else skipped
    for file, line, column, text, rest in warnings(lines):
        shown = offered_lines(text, rest)
        if not shown or not any(STRUCK in part or UNDERLINED in part for part in shown):
            continue
        if len(shown) > 1:
            skipped["hint has more than one line"] += 1
            continue
        pair = diff(shown[0])
        if pair is None:
            skipped["hint is no usable diff"] += 1
            continue
        if not pair[1]:
            skipped["hint only deletes"] += 1
            continue
        deprecated = DEPRECATED.match(text)
        linter = LINTER.search("\n".join(rest))
        kind = "deprecated" if deprecated else (linter.group(1) if linter else "other")
        yield Edit(file, line, column, pair[0], pair[1], kind, deprecated["name"] if deprecated else None)


# ---------------------------------------------------------------------------------------------
# Which names, and where in a file.


def is_theorem(name, kinds):
    """Whether a deprecated name is a theorem: by Lean's word in `kinds`, else by how the name reads."""
    if kinds is not None:
        return kinds.get(name) == "theorem"
    return "_" in name.rsplit(".", 1)[-1]


def read_kinds(lines):
    """What a run of the kind check says, as {name: kind}."""
    found = {}
    for line in lines:
        match = KIND.match(line.rstrip("\r\n"))
        if match:
            found[match["name"]] = match["kind"]
    return found


def kind_check(names):
    """A Lean file that prints the kind of each of `names`."""
    quoted = ",\n  ".join('"' + name.replace("\\", "\\\\").replace('"', '\\"') + '"' for name in sorted(names))
    return KIND_CHECK.replace("NAMES", quoted)


def plain(text):
    """`text` with comments, strings and character literals blanked out. Every character keeps its place."""
    out, at, end = [], 0, len(text)
    while at < end:
        opening = OPENER.search(text, at)
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
        elif not (start and (text[start - 1].isalnum() or text[start - 1] in "_'!?.")) and (literal := CHARACTER.match(text, start)):
            stop = literal.end()
        else:  # the prime of a name
            out.append(text[start])
            at = start + 1
            continue
        out.append("".join(char if char == "\n" else " " for char in text[start:stop]))
        at = stop
    return "".join(out)


def keyword(line):
    """What is left of a line without comments after indentation, attributes and modifiers."""
    line = line.lstrip()
    return line[PREFIX.match(line).end():]


def commands(bare, lines):
    """The lines (from 1) on which a command starts, and those of them that begin in the first column.

    `bare` are the `lines` without comments.
    """
    starts, flush = [], set()
    for number, (clean, line) in enumerate(zip(bare, lines), 1):
        code = clean.lstrip()
        if not code:
            continue
        if line[0] not in " \t" and COMMAND.match(code):
            starts.append(number)
            flush.add(number)
        elif DECLARATION.match(code):
            starts.append(number)
    return starts, flush


def in_proof_of_theorem(bare, starts, flush, number, column):
    """Whether a place sits in the proof of a theorem or lemma. `bare` are the lines without comments."""
    at = bisect.bisect_right(starts, number) - 1
    if at < 0:
        return False
    first = starts[at]
    # Where an indented theorem ends cannot be told by layout, so it has no proof here.
    if first not in flush or not PROVES.match(keyword(bare[first - 1])):
        return False
    before = "\n".join(bare[first - 1:number - 1] + [bare[number - 1][:column]])
    depth, waiting, proof, alternative = 0, 0, False, False
    for piece in PIECE.finditer(before):
        word = piece.group()
        if word in OPENING:
            depth += 1
        elif word in CLOSING:
            depth = max(depth - 1, 0)
        elif depth:
            continue
        elif word == "where":
            return False  # what follows may define things
        elif proof:
            continue
        elif word[0] == "\n":
            alternative = word[-1] == "|"
        elif word == "=>":
            if alternative:
                return False  # proved by pattern matching
        elif word in BINDS:
            waiting += 1
        elif word == ":=":
            if waiting:
                waiting -= 1
            else:
                proof = True
    return proof


def allowed(root, file, within):
    """Whether `file`, as a log names it, is a regular file under `root`/`within` with no symbolic link on the way."""
    relative = Path(file)
    if relative.is_absolute() or ".." in relative.parts:
        return False
    base = Path(root)
    if not relative.parts or Path(within).parts != relative.parts[:len(Path(within).parts)]:
        return False
    path = base
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            return False
    return path.is_file()


# ---------------------------------------------------------------------------------------------
# Making the edits.


def write_whole(path, text):
    """Replace the file at `path` by `text`, so that a failure leaves the old file."""
    if not os.access(path, os.W_OK):
        raise PermissionError(str(path))
    handle, fresh = tempfile.mkstemp(prefix=".apply-lean-hints.", dir=path.parent)
    try:
        with os.fdopen(handle, "w", encoding="utf-8", newline="") as stream:
            stream.write(text)
        os.chmod(fresh, os.stat(path).st_mode & 0o7777)
        os.replace(fresh, path)
    except BaseException:  # also an interrupt must not leave the temporary file in the tree
        try:
            os.unlink(fresh)
        except OSError:
            pass
        raise


def apply(root, offered, *, others=(), write=True, everywhere=False, within="src", kinds=None, definitions=False):
    """Make the edits under `root`. Returns {kind: Counter of outcomes}, the files changed, and the edits made.

    `others` are edits of the same log that are not to be made now. If one of them is in the
    text already, it has shifted its line, and that has to be known to find the rest.
    `kinds` is Lean's word on which deprecated names are theorems; without it the name decides.
    With `definitions` a deprecated name is replaced whatever it is.
    """
    outcome = collections.defaultdict(collections.Counter)
    by_file = collections.defaultdict(dict)  # {file: {key: (edit, whether it is to be made)}}
    for edit in offered:
        if edit.key() in by_file[edit.file]:
            outcome[edit.kind]["reported twice"] += 1
        elif edit.name is None or definitions or is_theorem(edit.name, kinds):
            by_file[edit.file][edit.key()] = (edit, True)
        else:
            by_file[edit.file][edit.key()] = (edit, False)
            if kinds is None:
                reason = "does not read like a theorem"
            elif edit.name not in kinds:
                reason = "not in the kinds file"
            elif kinds[edit.name] == "missing":
                reason = "not a constant the kind check found"
            else:
                reason = "not a theorem"
            outcome[edit.kind][reason] += 1
    for edit in others:
        by_file[edit.file].setdefault(edit.key(), (edit, False))
    changed, made = [], []
    for file in sorted(by_file):
        waiting = [edit for edit, wanted in by_file[file].values() if wanted]
        if not waiting:
            continue
        text = None
        if allowed(root, file, within):
            try:
                with open(Path(root) / file, encoding="utf-8", newline="") as stream:
                    text = stream.read()
            except (OSError, UnicodeDecodeError):
                pass
        if text is None:
            for edit in waiting:
                outcome[edit.kind]["file is not one to write"] += 1
            continue
        lines = text.split("\n")
        bare = [] if everywhere else plain(text).split("\n")
        starts, flush = ([], set()) if everywhere else commands(bare, lines)
        done = []
        by_line = collections.defaultdict(list)
        for pair in by_file[file].values():
            by_line[pair[0].line].append(pair)
        for number, on_line in sorted(by_line.items()):
            if not 1 <= number <= len(lines):
                for edit, wanted in on_line:
                    if wanted:
                        outcome[edit.kind]["text is not there"] += 1
                continue
            line = lines[number - 1]
            # From the left. An edit that is made already has shifted what follows it, and its
            # place is taken: nothing else may be made inside it. At one place an edit that is
            # only known goes first, so that one made in an earlier run keeps the place.
            shift, taken, pending = 0, 0, []
            for edit, wanted in sorted(on_line, key=lambda pair: (pair[0].column, -len(pair[0].old), pair[1])):
                at = edit.column + shift
                here_old = line[at:at + len(edit.old)] == edit.old
                here_new = bool(edit.new) and line[at:at + len(edit.new)] == edit.new
                if at < taken:
                    if wanted:
                        outcome[edit.kind]["overlaps another edit"] += 1
                elif here_new and (not here_old or edit.new.startswith(edit.old)):
                    if wanted:
                        outcome[edit.kind]["made already"] += 1
                    shift += len(edit.new) - len(edit.old)
                    taken = at + len(edit.new)
                elif not wanted:
                    continue
                elif not here_old:
                    outcome[edit.kind]["text is not there"] += 1
                elif not everywhere and not in_proof_of_theorem(bare, starts, flush, number, at):
                    outcome[edit.kind]["outside the proof of a theorem, left alone"] += 1
                else:
                    pending.append((at, edit))
                    taken = at + len(edit.old)
            # From the right, so that the places further left stay valid.
            for at, edit in reversed(pending):
                line = line[:at] + edit.new + line[at + len(edit.old):]
                outcome[edit.kind]["made"] += 1
                done.append(edit)
            lines[number - 1] = line
        if done and write:
            try:
                write_whole(Path(root) / file, "\n".join(lines))
            except OSError:
                for edit in done:
                    outcome[edit.kind]["made"] -= 1
                    outcome[edit.kind]["file could not be written"] += 1
                done = []
        if done:
            changed.append(file)
            made.extend(done)
    return outcome, changed, made


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("log", help="a log of `lake build`, or - for standard input")
    parser.add_argument("--root", default=".", help="the directory the paths in the log start from")
    parser.add_argument("--within", default="src", help="only files under this directory of the root are written (default: src)")
    parser.add_argument("--kind", action="append",
                        help=f"a kind of warning to apply: `deprecated`, or a linter option; may be repeated (default: {', '.join(KINDS)})")
    parser.add_argument("--name", action="append", help="of the deprecated names, only this one; may be repeated")
    parser.add_argument("--kinds", metavar="FILE", help="the output of the kind check: which deprecated names are theorems")
    parser.add_argument("--write-kind-check", metavar="FILE",
                        help="write a Lean file that prints the kind of each deprecated name in the log, and stop")
    parser.add_argument("--definitions", action="store_true",
                        help="also replace deprecated names that are not theorems; a proof can stop compiling")
    parser.add_argument("--everywhere", action="store_true",
                        help="also edit statements and the bodies of definitions and instances, where a name of the same type can change the meaning")
    parser.add_argument("--table", action="store_true", help="list every replacement that is made, with its count")
    parser.add_argument("--dry-run", action="store_true", help="change nothing, only count")
    args = parser.parse_args()

    kinds = args.kind or KINDS
    skipped = collections.Counter()
    try:
        if args.log == "-":
            sys.stdin.reconfigure(encoding="utf-8", errors="replace")
            stream = sys.stdin
        else:
            stream = open(args.log, encoding="utf-8", errors="replace")
        with stream:
            found = list(edits(stream, skipped))
    except OSError as error:
        print(f"the log cannot be read: {error}", file=sys.stderr)
        return 2
    if args.write_kind_check:
        names = {edit.name for edit in found if edit.name}
        try:
            Path(args.write_kind_check).write_text(kind_check(names), encoding="utf-8")
        except OSError as error:
            print(f"the kind check cannot be written: {error}", file=sys.stderr)
            return 2
        print(f"{len(names)} names written to {args.write_kind_check}; run it with `lake env lean` and pass the output to --kinds")
        return 0
    told = None
    if args.kinds:
        try:
            with open(args.kinds, encoding="utf-8", errors="replace") as lines:
                told = read_kinds(lines)
        except OSError as error:
            print(f"the kinds file cannot be read: {error}", file=sys.stderr)
            return 2
        if not told:
            print(f"{args.kinds} holds no line of the kind check's output", file=sys.stderr)
            return 2
    for edit in found:
        if edit.kind not in kinds:
            skipped[f"kind not asked for: {edit.kind}"] += 1
    def wanted(edit):
        return edit.kind in kinds and (edit.name is None or not args.name or edit.name in args.name)

    outcome, changed, made = apply(args.root, [edit for edit in found if wanted(edit)],
                                   others=[edit for edit in found if not wanted(edit)], write=not args.dry_run,
                                   everywhere=args.everywhere, within=args.within, kinds=told, definitions=args.definitions)

    stale = strange = unwritten = 0
    for kind in sorted(outcome):
        counts = +outcome[kind]
        stale += counts["text is not there"]
        strange += counts["file is not one to write"]
        unwritten += counts["file could not be written"]
        rest = "; ".join(f"{count} {what}" for what, count in sorted(counts.items()) if what != "made")
        print(f"{kind}: {counts['made']} edits" + (f" ({rest})" if rest else ""))
    for what, count in sorted(skipped.items()):
        print(f"not used: {count} {what}")
    if args.table:
        pairs = collections.Counter((edit.kind, edit.old, edit.new) for edit in made)
        for (kind, old, new), count in sorted(pairs.items(), key=lambda item: (-item[1], item[0])):
            print(f"{count:>7}  {old} -> {new}  [{kind}]")
    print(f"{len(changed)} files " + ("would change" if args.dry_run else "changed"))
    if stale:
        print(f"{stale} edits did not find their text: the log is not of this tree", file=sys.stderr)
    if strange:
        print(f"{strange} edits are in files that are not ones to write: check --root and --within", file=sys.stderr)
    if unwritten:
        print(f"{unwritten} edits are in files that could not be written", file=sys.stderr)
    return 1 if stale or strange or unwritten else 0


if __name__ == "__main__":
    sys.exit(main())
