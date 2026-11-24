#!/usr/bin/env python3
"""Check which axioms the judged theorems depend on, from the artifacts of a build.

`comparator.json` names the theorems and the axioms they may depend on. This script has Lean
list, for each of those theorems, every axiom its proof depends on. It ends with 1 when a
theorem does not exist, is no theorem, or depends on an axiom outside the list. A `sorry`
anywhere below a theorem shows up as the axiom `sorryAx`. It elaborates one small file that
imports the solution module. It builds nothing.

Two ways to run it:

  check-axioms.py --project DIR --build-map MAP --build-log LOG --build-receipt FILE --receipt OUT
      After scripts/run-complete-build.py. The build's receipt has to bind the checked-out
      inputs, the log and the map, by the test scripts/stage-completed-build.py applies, and
      the module traces in the build directory have to cover the map. The theorems and the
      allowed axioms are read from the commit, not from the working tree. The registered
      toolchain's `lake` and `lean` are used, in the build's trusted environment.

  check-axioms.py --project DIR --unbound [--receipt OUT]
      On any tree whose solution module is built, for a contributor's own check. It runs the
      `lake` and `lean` it finds, in the caller's environment, and its receipt says that no
      completed build stands behind it.

In both, `lake build --no-build` of the solution module runs first and has to end with 0: for
that module and all it imports, Lake then finds the recorded input hashes equal to the ones of
the sources in the tree. After a completed build the sources are hashed again for this
(`--rehash`). The artifacts themselves are not hashed against the build's map; staging does
that for the archives it publishes.

What this is not: a second check of the proofs. In this version of Lean the axioms of a theorem
are recorded in its module's artifact when the module is built, and this script reads that
record. Code of the tree that runs during the build, or when the solution is imported, could
tamper with the record or with this run. The check finds a `sorry` or an axiom that someone
left in; it is no defence against a tree written to deceive it. Nor does it look at what a
theorem states. Comparator and its kernels replay the proofs and compare the statements.

Exit code: 0 when every theorem depends on allowed axioms only; 1 when one does not, does not
exist or is no theorem; 2 when the check could not be made (inputs, build state, Lean's answer).
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
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
# The artifacts of a module that hold its declarations.
OLEANS = (".olean", ".olean.server", ".olean.private")


class Unusable(Exception):
    """The check could not be made."""


def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


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
            if (name in found or not count.isdigit() or int(count) != len(axioms) or not all(axioms)
                    or len(set(axioms)) != len(axioms)):
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


def run(command, cwd, env):
    """Run a command; its exit code and what it printed, standard error included."""
    try:
        done = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    except OSError as error:
        raise Unusable(f"{command[0]} could not be started: {error}") from None
    return done.returncode, done.stdout.decode("utf-8", "replace")


def artifacts(project, solution):
    """Checksums of the solution module's own artifacts in the build directory."""
    relative = Path(*solution.split("."))
    for other in sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean")):
        if any((other / relative.parent / (relative.name + suffix)).exists() for suffix in OLEANS):
            raise Unusable(f"a dependency's build directory holds a module `{solution}` too, and Lean would load that one: {other}")
    directory = project / ".lake/build/lib/lean" / relative.parent
    files = [directory / (relative.name + suffix) for suffix in OLEANS]
    files = [path for path in files if path.exists() or path.is_symlink()]
    if not files or files[0].name != relative.name + ".olean":
        raise Unusable(f"no artifact of `{solution}` under {directory}")
    for path in files:
        if path.is_symlink() or not path.is_file():
            raise Unusable(f"an artifact of `{solution}` is no regular file: {path}")
    return {path.name: sha256(path) for path in files}


def collect(project, lake, lean, env, solution, names):
    """Lean's answer for `names` and the artifacts it came from, after Lake has confirmed that the solution module is built."""
    # `+` names the module. A bare name would be taken for a library or an executable of that name first.
    code, output = run([*lake, "build", "--no-build", "+" + solution], project, env)
    if code:
        raise Unusable(f"`lake build --no-build +{solution}` ended with {code}: the solution module is not built "
                       f"for the sources in this tree\n{output[-2000:]}")
    before = artifacts(project, solution)
    token = "check-axioms-" + secrets.token_hex(16)
    with tempfile.TemporaryDirectory(prefix="check-axioms-") as work:
        source = Path(work) / "CheckAxioms.lean"
        source.write_text(lean_source(solution, names, token), encoding="utf-8")
        code, output = run([lake[0], "env", lean, str(source)], project, env)
    if code:
        raise Unusable(f"Lean ended with {code} on the file that lists the axioms\n{output[-2000:]}")
    found, kinds = read(output, names, token)
    if artifacts(project, solution) != before:
        raise Unusable("the solution module's artifacts changed while the check ran")
    return found, kinds, before


def repository_modules():
    """The repository's own build script and its complete-build script, as modules."""
    here = Path(__file__)
    spec = importlib.util.spec_from_file_location("completed_ci_build", here.with_name("ci-build.py"))
    ci = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ci)
    spec = importlib.util.spec_from_file_location("stock_complete_build", here.with_name("run-complete-build.py"))
    complete = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(complete)
    return ci, complete


def bound(args):
    """Check that the completed build's receipt binds this tree, as staging does.

    Returns what goes into the receipt, the bytes of the commit's `comparator.json`, the
    commands and the environment to use, and a function that makes the same check again.
    """
    ci, complete = repository_modules()
    selected = ci.settings.for_toolchain(args.release or ci.TOOLCHAIN)
    ci.TOOLCHAIN, ci.settings = selected.TOOLCHAIN, selected
    project = args.project.resolve()
    log = ci.safe_file(args.build_log.parent.resolve(), args.build_log.name)
    if not re.search(rb"Build completed successfully \([0-9]+ jobs\)\.", log.read_bytes()):
        raise Unusable("the build log does not record successful completion")
    mapping = ci.safe_file(args.build_map.parent.resolve(), args.build_map.name)
    receipt_file = ci.safe_file(args.build_receipt.parent.resolve(), args.build_receipt.name)
    receipt = json.loads(receipt_file.read_text())

    def check():
        current = complete.identity(project, selected)
        complete.validate_receipt(receipt, current, selected, log, mapping)
        # As in staging: every entry of the build's map is the input hash of a module built here.
        entries = ci.load_map(mapping)
        if not entries or {key for _, _, key in ci.module_traces(project) if key in entries} != set(entries):
            raise Unusable("the module traces in the build directory do not cover the completed build's map")
        return current

    current = check()
    env = {**ci.trusted_env(), "ELAN_TOOLCHAIN": selected.TOOLCHAIN, "LEAN_ABORT_ON_PANIC": "1"}
    toolchain = args.toolchain
    if toolchain is None:
        toolchain = Path(subprocess.check_output(["elan", "which", "lean"], env=env, text=True).strip()).parent.parent
    version = subprocess.check_output([str(toolchain / "bin/lean"), "--version"], env=env, text=True)
    if not version.startswith(f"Lean (version {selected.VERSION},") or selected.COMMIT not in version:
        raise Unusable("the check requires the exact registered stock toolchain")
    config = subprocess.check_output(["git", "-C", str(project), "cat-file", "blob",
                                      current["candidate_head"] + ":comparator.json"], env=env)
    facts = {"bound_to_completed_build": True, "candidate_head": current["candidate_head"],
             "candidate_tree": current["candidate_tree"], "toolchain": selected.TOOLCHAIN,
             "toolchain_commit": selected.COMMIT, "lean_version": version.strip(),
             "build_receipt_sha256": ci.sha256(receipt_file), "build_log_sha256": ci.sha256(log),
             "map_sha256": ci.sha256(mapping)}
    return facts, config, [str(toolchain / "bin/lake"), "--rehash"], str(toolchain / "bin/lean"), env, check


def unbound(project):
    """What can be said about a tree with no completed build behind it, and the bytes of its `comparator.json`."""
    def said(*command):
        try:
            code, output = run(list(command), project, None)
        except Unusable:
            return None
        return output.strip() if code == 0 else None

    status = said("git", "status", "--porcelain", "--", "src", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
                  "comparator.json")
    try:
        config = (project / "comparator.json").read_bytes()
    except OSError as error:
        raise Unusable(f"comparator.json cannot be read: {error}") from None
    facts = {"bound_to_completed_build": False, "candidate_head": said("git", "rev-parse", "HEAD"),
             "inputs_committed": status == "", "lean_version": said("lean", "--version")}
    return facts, config


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--project", type=Path, required=True, help="the checkout whose build is checked")
    parser.add_argument("--build-map", type=Path, help="the completed build's -o map")
    parser.add_argument("--build-log", type=Path, help="the completed build's log")
    parser.add_argument("--build-receipt", type=Path, help="the receipt scripts/run-complete-build.py wrote")
    parser.add_argument("--unbound", action="store_true",
                        help="check a tree with no completed build behind it; the receipt says so")
    parser.add_argument("--receipt", type=Path, help="where to write this check's receipt (required with a build receipt)")
    parser.add_argument("--toolchain", type=Path, help="the stock toolchain's directory (with a build receipt)")
    parser.add_argument("--release", help="the registered stock release (with a build receipt)")
    args = parser.parse_args(argv)
    build = (args.build_map, args.build_log, args.build_receipt)
    if args.unbound and (any(build) or args.toolchain or args.release):
        parser.error("--unbound stands alone: no build map, log or receipt, and no --toolchain or --release")
    if not args.unbound and not all(build):
        parser.error("give --build-map, --build-log and --build-receipt together, or --unbound alone")
    if not args.unbound and args.receipt is None:
        parser.error("with a build receipt, --receipt is required")
    if args.receipt is not None and args.receipt.exists():
        parser.error("use a fresh --receipt path, so that a stale result cannot be taken for this one")

    project = args.project.resolve()
    try:
        again = None
        if args.unbound:
            facts, config = unbound(project)
            lake, lean, env = ["lake"], "lean", None
        else:
            try:
                facts, config, lake, lean, env, again = bound(args)
            except Unusable:
                raise
            except Exception as error:  # the repository's own checks raise ValueError and CalledProcessError
                raise Unusable(f"the completed build's receipt does not stand for this tree: {error}") from None
        solution, names, permitted = judged(config)
        found, kinds, made = collect(project, lake, lean, env, solution, names)
        if again is not None:
            try:
                again()
            except Exception as error:
                raise Unusable(f"the inputs changed while the check ran: {error}") from None
        wrong = problems(found, kinds, permitted)
        value = {"schema": 1, "kind": "axioms-of-judged-theorems", **facts,
                 "comparator_sha256": hashlib.sha256(config).hexdigest(), "solution_module": solution,
                 "solution_artifacts_sha256": made, "permitted_axioms": sorted(permitted),
                 "axioms": found, "kinds": kinds, "problems": wrong, "passed": not wrong}
        if args.receipt is not None:
            args.receipt.parent.mkdir(parents=True, exist_ok=True)
            args.receipt.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    except (Unusable, OSError) as error:
        print(f"check-axioms: {error}", file=sys.stderr)
        return 2

    for name, axioms in found.items():
        print(f"{name}: " + ("does not exist" if axioms is None else ", ".join(axioms) if axioms else "no axioms"))
    for line in wrong:
        print(f"check-axioms: {line}", file=sys.stderr)
    print(json.dumps({"axioms_checked": True, "passed": not wrong, "bound_to_completed_build": facts["bound_to_completed_build"],
                      "candidate_head": facts["candidate_head"], "theorems": len(found)}), flush=True)
    return 1 if wrong else 0


if __name__ == "__main__":
    sys.exit(main())
