#!/usr/bin/env python3
"""Check which axioms the judged theorems depend on, after a build.

`comparator.json` names the theorems and the axioms they may depend on. This script has Lean
list, for each of those theorems, every axiom its proof depends on. It ends with 1 when a
theorem does not exist, is no theorem, or depends on an axiom outside the list. A `sorry`
anywhere below a theorem shows up as the axiom `sorryAx`. It builds nothing.

It runs Lake twice:

    lake build --no-build +<solution module>
        has to end with 0: for that module and all it imports, Lake then finds the recorded
        input hashes equal to the ones of the sources in the tree.
    lake env lean <a small file>
        The file imports the solution module and prints the axioms.

Importing the solution module runs the `initialize` blocks of the tree, so the second command
runs code of the tree, and both belong where the build ran. After a pull request's build that
is the build's sandbox. `check()` therefore does not run Lake itself: it is given a function
that does, and the caller decides where and under which limits. It writes the small file to a
place the caller names, and makes the verdict from what the two commands print. Run as a
script, this uses the `lake` it finds, for a contributor's own tree.

What this is not: a second check of the proofs. In this version of Lean the axioms of a theorem
are recorded in its module's artifact when the module is built, and this script reads that
record. Code of the tree that runs during the build, or when the solution is imported, could
tamper with the record or print an answer of its own. The check finds a `sorry` or an axiom
that someone left in; it is no defence against a tree or a build cache written to deceive it:
a record that came from the cache is read as it stands. Nor does it look at what a theorem
states. Comparator and its kernels replay the proofs and compare the statements.

Exit code: 0 when every theorem depends on allowed axioms only; 1 when one does not, does not
exist or is no theorem; 2 when the check could not be made (comparator.json, the build's state,
Lean's answer).
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import secrets
import subprocess
import sys
import tempfile

# A name as Lean's `String.toName` reads it back unchanged: parts of letters, digits, `_` and `'`.
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
# The Lean file. Every line of the answer begins with a word made up for this run, so that a
# line printed by anything else is not taken for one. Axiom names are printed as the hexadecimal
# digits of their bytes: a name may hold any character, a line break among them. `Lean` is
# imported by name, because the solution need not bring it along.
CHECK = '''import SOLUTION
import Lean

def checkAxiomsHex (text : String) : String :=
  text.toUTF8.foldl (fun out byte =>
    let digits := Nat.toDigits 16 byte.toNat
    out ++ (if digits.length < 2 then "0" else "") ++ String.ofList digits) ""

open Lean in
#eval show CoreM Unit from do
  let names : List String := [NAMES]
  let env ← getEnv
  IO.println ""
  for text in names do
    let name := text.toName
    match env.find? name with
    | none => IO.println ("TOKEN\\tMISSING\\t" ++ text)
    | some info =>
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      let found := (← collectAxioms name).qsort Name.lt
      IO.println ("TOKEN\\tAXIOMS\\t" ++ text ++ "\\t" ++ kind ++ "\\t" ++ toString found.size
        ++ found.foldl (fun line a => line ++ "\\t" ++ checkAxiomsHex (toString a)) "")
  IO.println ("TOKEN\\tEND\\t" ++ toString names.length)
'''


class Unusable(ValueError):
    """The check could not be made."""


def judged(data, where="comparator.json"):
    """What the bytes of a `comparator.json` ask for: the solution module, the theorems, the allowed axioms."""
    try:
        config = json.loads(data.decode("utf-8"))
        solution, names, permitted = config["solution_module"], config["theorem_names"], config["permitted_axioms"]
    except (ValueError, KeyError, TypeError) as error:
        raise Unusable(f"{where} does not name a solution module, theorems and permitted axioms: {error}") from None
    if not (isinstance(solution, str) and isinstance(names, list) and isinstance(permitted, list) and names
            and all(isinstance(name, str) for name in [*names, *permitted])):
        raise Unusable(f"{where} does not name a solution module, theorems and permitted axioms")
    for name in [solution, *names, *permitted]:
        if not NAME.match(name):
            raise Unusable(f"{where}: `{name}` is not a name this check can pass to Lean")
    if len(set(names)) != len(names):
        raise Unusable(f"{where} names a theorem twice")
    return solution, names, permitted


def lean_source(solution, names, token):
    """The Lean file that prints the axioms of `names`. The names have passed `NAME`."""
    return (CHECK.replace("SOLUTION", solution).replace("TOKEN", token)
            .replace("NAMES", ", ".join(f'"{name}"' for name in names)))


def read(output, names, token):
    """What Lean printed: {theorem: sorted axioms, or None when it does not exist} and {theorem: kind}.

    Only lines that begin with `token` count. Raises Unusable when they are not one unbroken,
    complete answer for exactly `names`.
    """
    found, kinds, state = {}, {}, "before"
    for line in output.split("\n"):
        if not line.startswith(token + "\t"):
            if state == "answer" and line:
                raise Unusable("a line of another origin stands inside Lean's answer")
            continue
        if state == "ended":
            raise Unusable("Lean's answer goes on after its last line")
        state = "answer"
        word, *fields = line.split("\t")[1:]
        if word == "AXIOMS" and len(fields) >= 3:
            name, kind, count, coded = fields[0], fields[1], fields[2], fields[3:]
            try:
                axioms = [bytes.fromhex(item).decode("utf-8") for item in coded]
            except ValueError:
                raise Unusable(f"Lean's answer for `{name}` holds a name that cannot be read") from None
            if name in found or count != str(len(axioms)) or not all(axioms) or len(set(axioms)) != len(axioms):
                raise Unusable(f"Lean's answer for `{name}` is not usable")
            found[name], kinds[name] = sorted(axioms), kind
        elif word == "MISSING" and len(fields) == 1 and fields[0] not in found:
            found[fields[0]] = None
        elif word == "END" and len(fields) == 1 and fields[0] == str(len(names)):
            state = "ended"
        else:
            raise Unusable("a line of Lean's answer is not usable")
    if state != "ended":
        raise Unusable("Lean's answer has no last line: the run did not come to its end")
    if list(found) != list(names):
        raise Unusable("Lean did not answer for exactly the theorems that were asked for, in their order")
    return found, kinds


def problems(found, kinds, permitted):
    """One sentence for each theorem that is missing, is no theorem, or depends on an axiom outside `permitted`."""
    lines = []
    for name, axioms in found.items():
        if axioms is None:
            lines.append(f"`{name}` does not exist in the solution module")
            continue
        if kinds[name] != "theorem":
            lines.append(f"`{name}` is no theorem: Lean calls it {kinds[name]}")
        extra = [axiom for axiom in axioms if axiom not in permitted]
        if extra:
            lines.append(f"`{name}` depends on {', '.join('`' + axiom + '`' for axiom in extra)}")
    return lines


def through(command, *, cwd=None, env=None):
    """A function for `check()`: it runs `command`, a list, with the arguments it is given behind it."""
    def lake(arguments):
        try:
            done = subprocess.run([*command, *arguments], cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except OSError as error:
            raise Unusable(f"{command[0]} could not be started: {error}") from None
        return done.returncode, done.stdout.decode("utf-8", "replace")
    return lake


def check(config, lake, source, seen_as=None):
    """The axioms of the theorems that `config` names, with the verdict under `passed`.

    `config`: the bytes of a `comparator.json`. The caller chooses whose. For a pull request
        that is the base branch's: the pull request's own could permit more.
    `lake`: a function that runs Lake with the arguments it is given, a list, and returns the
        exit code and what was printed, standard error included. On one's own tree that is
        `through(["lake"], cwd=project)`. After a pull request's build it runs the build's
        sandbox command with the path of `lake` inside it and Lake's own options (`--packages`,
        `--rehash`) behind it, under the build's limits on memory and time.
    `source`: where the Lean file is written. `seen_as`: the path under which the Lean process
        finds that file, when the sandbox shows it elsewhere.

    Raises Unusable (a ValueError) when the check cannot be made.
    """
    solution, names, permitted = judged(config)
    # `+` names the module. A bare name would be taken for a library or an executable of that name first.
    code, output = lake(["build", "--no-build", "+" + solution])
    if code:
        raise Unusable(f"`lake build --no-build +{solution}` ended with {code}: the solution module is not built "
                       f"for the sources in this tree\n{output[-2000:]}")
    token = "check-axioms-" + secrets.token_hex(16)
    try:
        Path(source).write_text(lean_source(solution, names, token), encoding="utf-8")
    except OSError as error:
        raise Unusable(f"the Lean file that lists the axioms could not be written: {error}") from None
    code, output = lake(["env", "lean", str(seen_as or source)])
    if code:
        raise Unusable(f"Lean ended with {code} on the file that lists the axioms\n{output[-2000:]}")
    found, kinds = read(output, names, token)
    wrong = problems(found, kinds, permitted)
    return {"solution_module": solution, "permitted_axioms": sorted(permitted), "axioms": found, "kinds": kinds,
            "problems": wrong, "passed": not wrong}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--project", type=Path, default=Path("."),
                        help="the checkout whose build is checked, with its comparator.json (default: this directory)")
    project = parser.parse_args(argv).project.resolve()
    try:
        config = (project / "comparator.json").read_bytes()
        with tempfile.TemporaryDirectory(prefix="check-axioms-") as work:
            record = check(config, through(["lake"], cwd=project), Path(work) / "CheckAxioms.lean")
    except (Unusable, OSError) as error:
        print(f"check-axioms: {error}", file=sys.stderr)
        return 2
    for name, axioms in record["axioms"].items():
        print(f"{name}: " + ("does not exist" if axioms is None else ", ".join(axioms) if axioms else "no axioms"))
    for line in record["problems"]:
        print(f"check-axioms: {line}", file=sys.stderr)
    print(json.dumps({"axioms_checked": True, "passed": record["passed"], "theorems": len(record["axioms"])}), flush=True)
    return 0 if record["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
