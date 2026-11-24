#!/usr/bin/env python3
"""The axiom check without Lean: its reading of Lean's answer, its verdict, and its runs against a stand-in for lake."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("check-axioms.py")
spec = importlib.util.spec_from_file_location("check_axioms", SCRIPT)
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)

NAMES = ["riemannHypothesis", "LFunction_eq_zero_re"]
PERMITTED = ["propext", "Quot.sound", "Classical.choice"]
T = "check-axioms-0123"


def coded(*axioms):
    """Axiom names the way the Lean file prints them."""
    return "".join("\t" + name.encode("utf-8").hex() for name in axioms)


def answer(first=("propext", "Classical.choice", "Quot.sound"), second=(), kind="theorem"):
    return ("warning: something Lean said on the way\n\n"
            f"TOKEN\tAXIOMS\triemannHypothesis\ttheorem\t{len(first)}{coded(*first)}\n"
            f"TOKEN\tAXIOMS\tLFunction_eq_zero_re\t{kind}\t{len(second)}{coded(*second)}\n"
            "TOKEN\tEND\t2\n")


GOOD = answer()
# A stand-in for lake. It notes each call and three variables of its environment, ends `build`
# with the code in the file `build-code`, and answers `env lean FILE` with the file `answer`,
# in which it puts the word made up for this run, and the code in `lean-code`.
LAKE = '''#!/bin/sh
dir="$FAKE_LAKE"
echo "$*" >> "$dir/calls"
echo "${LEAKED:-none} ${ELAN_TOOLCHAIN:-none} ${LEAN_ABORT_ON_PANIC:-none}" >> "$dir/environment"
[ "$1" = "--rehash" ] && shift
case "$1" in
  build) exit "$(cat "$dir/build-code" 2>/dev/null || echo 0)" ;;
  env) cp "$3" "$dir/asked.lean"
       token=$(grep -o 'check-axioms-[0-9a-f]*' "$3" | head -1)
       sed "s/TOKEN/$token/g" "$dir/answer"
       exit "$(cat "$dir/lean-code" 2>/dev/null || echo 0)" ;;
esac
exit 64
'''
CONFIG = json.dumps({"solution_module": "Main", "theorem_names": NAMES, "permitted_axioms": PERMITTED})


def read(text, names=NAMES):
    return check.read(text.replace("TOKEN", T), names, T)


class Reading(unittest.TestCase):
    def test_a_complete_answer_is_read_and_lines_before_and_after_it_are_passed_over(self):
        found, kinds = read(GOOD + "something printed at the end\n")
        self.assertEqual(found, {"riemannHypothesis": ["Classical.choice", "Quot.sound", "propext"], "LFunction_eq_zero_re": []})
        self.assertEqual(kinds, {"riemannHypothesis": "theorem", "LFunction_eq_zero_re": "theorem"})

    def test_a_theorem_that_does_not_exist_is_read_as_such(self):
        text = f"TOKEN\tMISSING\triemannHypothesis\nTOKEN\tAXIOMS\tLFunction_eq_zero_re\tdefinition\t1{coded('sorryAx')}\nTOKEN\tEND\t2\n"
        self.assertEqual(read(text), ({"riemannHypothesis": None, "LFunction_eq_zero_re": ["sorryAx"]},
                                      {"LFunction_eq_zero_re": "definition"}))

    def test_a_name_with_a_line_break_or_a_tab_stays_one_name(self):
        odd = "propext\n»\tx"
        found, _ = read(answer(second=("propext", odd)))
        self.assertEqual(found["LFunction_eq_zero_re"], sorted(["propext", odd]))

    def test_only_lines_with_this_runs_word_count(self):
        forged = GOOD.replace("TOKEN", "check-axioms-ffff")
        with self.assertRaises(check.Unusable):
            check.read(forged, NAMES, T)
        # A forged answer in front of the real one changes nothing.
        self.assertEqual(check.read(forged + answer(second=("sorryAx",)).replace("TOKEN", T), NAMES, T)[0]["LFunction_eq_zero_re"],
                         ["sorryAx"])

    def test_an_answer_that_is_not_complete_is_refused(self):
        second = "TOKEN\tAXIOMS\tLFunction_eq_zero_re\ttheorem\t0\n"
        cases = {"no last line": GOOD.replace("TOKEN\tEND\t2\n", ""),
                 "a last line with another count": GOOD.replace("END\t2", "END\t5"),
                 "a theorem not answered": GOOD.replace(second, ""),
                 "a theorem not asked for": GOOD.replace("TOKEN\tEND", "TOKEN\tAXIOMS\tother\ttheorem\t0\nTOKEN\tEND"),
                 "another order": second + "TOKEN\tAXIOMS\triemannHypothesis\ttheorem\t0\nTOKEN\tEND\t2\n",
                 "fewer axioms than counted": GOOD.replace("\t3" + coded("propext", "Classical.choice", "Quot.sound"), "\t3" + coded("propext")),
                 "more axioms than counted": answer(second=("sorryAx",)).replace("\t1" + coded("sorryAx"), "\t0" + coded("sorryAx")),
                 "an axiom given twice": answer(first=("propext", "propext", "Quot.sound")),
                 "an empty axiom": GOOD.replace(coded("Quot.sound"), "\t"),
                 "an axiom that is no hexadecimal text": GOOD.replace(coded("Quot.sound"), "\tQuot.sound"),
                 "an axiom that is no UTF-8": GOOD.replace(coded("Quot.sound"), "\tff"),
                 "a count that is no number": GOOD.replace(second, second.replace("\t0", "\tnone")),
                 "an answer given twice": GOOD.replace("TOKEN\tEND", "TOKEN\tAXIOMS\triemannHypothesis\ttheorem\t0\nTOKEN\tEND"),
                 "missing after an answer": GOOD.replace("TOKEN\tEND", "TOKEN\tMISSING\triemannHypothesis\nTOKEN\tEND"),
                 "lines after the last": GOOD + second,
                 "a second last line": GOOD + "TOKEN\tEND\t2\n",
                 "a line of another origin inside the answer": GOOD.replace(second, "something else\n" + second),
                 "a line with the word and no known content": GOOD.replace(second, "TOKEN\tOTHER\n" + second),
                 "nothing at all": ""}
        for name, text in cases.items():
            with self.subTest(name):
                with self.assertRaises(check.Unusable):
                    read(text)


class Verdict(unittest.TestCase):
    def test_allowed_axioms_and_no_axioms_pass(self):
        self.assertEqual(check.problems({"a": ["Classical.choice", "propext"], "b": []}, {"a": "theorem", "b": "theorem"}, PERMITTED), [])

    def test_an_axiom_outside_the_list_a_missing_theorem_and_what_is_no_theorem_are_named(self):
        found = {"a": ["Classical.choice", "sorryAx"], "b": None, "c": ["My.axiom", "propext"], "d": [], "e": ["e"]}
        kinds = {"a": "theorem", "c": "theorem", "d": "definition", "e": "axiom"}
        self.assertEqual(check.problems(found, kinds, PERMITTED),
                         ["`a` depends on `sorryAx`", "`b` does not exist in the solution module", "`c` depends on `My.axiom`",
                          "`d` is no theorem: Lean calls it definition", "`e` is no theorem: Lean calls it axiom", "`e` depends on `e`"])
        self.assertEqual(check.problems({"a": ["propext"]}, {"a": "theorem"}, []), ["`a` depends on `propext`"])


class Config(unittest.TestCase):
    def config(self, **changes):
        value = {"challenge_module": "Challenge", "solution_module": "Main", "theorem_names": NAMES, "permitted_axioms": PERMITTED}
        value.update(changes)
        return json.dumps({key: item for key, item in value.items() if item is not None}).encode()

    def test_the_solution_the_theorems_and_the_allowed_axioms_are_read(self):
        self.assertEqual(check.judged(self.config()), ("Main", NAMES, PERMITTED))
        self.assertEqual(check.judged(self.config(permitted_axioms=[]))[2], [])

    def test_a_config_that_does_not_say_all_three_is_refused(self):
        for changes in ({"theorem_names": None}, {"permitted_axioms": None}, {"solution_module": None}, {"theorem_names": []},
                        {"theorem_names": "riemannHypothesis"}, {"theorem_names": [1]}, {"permitted_axioms": "propext"},
                        {"theorem_names": ["a", "a"]}):
            with self.subTest(changes=changes):
                with self.assertRaises(check.Unusable):
                    check.judged(self.config(**changes))
        for data in (b"", b"[]", b"\xff"):
            with self.assertRaises(check.Unusable):
                check.judged(data)

    def test_a_name_that_could_leave_the_lean_string_is_refused(self):
        for name in ('a"b', "a b", "a\\b", "a\nb", "«a»", "a.", ".a", "1a", "a..b", "ä"):
            with self.subTest(name=name):
                with self.assertRaises(check.Unusable):
                    check.judged(self.config(theorem_names=[name]))
                with self.assertRaises(check.Unusable):
                    check.judged(self.config(solution_module=name))
        self.assertEqual(check.judged(self.config(theorem_names=["A.b_c'", "_x1"]))[1], ["A.b_c'", "_x1"])

    def test_the_lean_file_imports_the_solution_and_lean_and_asks_for_each_name(self):
        text = check.lean_source("Deep.Main", NAMES, T)
        self.assertTrue(text.startswith("import Deep.Main\nimport Lean\n"))
        self.assertIn('["riemannHypothesis", "LFunction_eq_zero_re"]', text)
        self.assertEqual(text.count(T), 3)
        self.assertNotIn("TOKEN", text)


class Artifacts(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name)
        self.lib = self.project / ".lake/build/lib/lean"
        (self.lib / "Deep").mkdir(parents=True)

    def test_the_declaring_artifacts_of_a_dotted_module_are_listed_and_nothing_else(self):
        for name in ("Main.olean", "Main.olean.private", "Main.olean.server", "Main.olean.hash", "Main.olean.bak", "Main.ilean", "Other.olean"):
            (self.lib / "Deep" / name).write_bytes(name.encode())
        self.assertEqual(list(check.artifacts(self.project, "Deep.Main")), ["Main.olean", "Main.olean.server", "Main.olean.private"])
        with self.assertRaises(check.Unusable):
            check.artifacts(self.project, "Deep.Absent")
        (self.lib / "Deep/Main.olean").unlink()
        with self.assertRaises(check.Unusable):
            check.artifacts(self.project, "Deep.Main")

    def test_a_linked_artifact_is_refused(self):
        (self.project / "elsewhere").write_bytes(b"x")
        (self.lib / "Main.olean").symlink_to(self.project / "elsewhere")
        with self.assertRaises(check.Unusable):
            check.artifacts(self.project, "Main")

    def test_a_module_of_the_same_name_in_a_dependency_is_refused(self):
        (self.lib / "Main.olean").write_bytes(b"x")
        self.assertEqual(list(check.artifacts(self.project, "Main")), ["Main.olean"])
        other = self.project / ".lake/packages/dep/.lake/build/lib/lean"
        other.mkdir(parents=True)
        (other / "Main.olean").write_bytes(b"planted")
        with self.assertRaises(check.Unusable):
            check.artifacts(self.project, "Main")


def make_project(root):
    """A committed project with a built solution module, a stand-in for lake on a path, and its notes."""
    project, fake, tools = root / "project", root / "fake", root / "bin"
    for path in (project / ".lake/build/lib/lean", project / "src", fake, tools):
        path.mkdir(parents=True)
    (tools / "lake").write_text(LAKE)
    (tools / "lean").write_text("#!/bin/sh\necho 'Lean (version 0.0.0, a stand-in)'\n")
    for tool in ("lake", "lean"):
        (tools / tool).chmod(0o755)
    (project / "comparator.json").write_text(CONFIG)
    (project / "lean-toolchain").write_text("leanprover/lean4:v0\n")
    (project / "src/Main.lean").write_text("-- the solution\n")
    (project / ".lake/build/lib/lean/Main.olean").write_bytes(b"olean")
    (fake / "answer").write_text(GOOD)
    git = ["git", "-C", str(project), "-c", "user.name=t", "-c", "user.email=t@example.org"]
    subprocess.run([*git, "init", "--quiet"], check=True)
    subprocess.run([*git, "add", "comparator.json", "lean-toolchain", "src"], check=True)
    subprocess.run([*git, "commit", "--quiet", "-m", "start"], check=True)
    return project, fake, tools


class Running(unittest.TestCase):
    """The script as a command on a contributor's tree, with a stand-in for lake on the path."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.project, self.fake, tools = make_project(self.root)
        self.env = {**os.environ, "PATH": f"{tools}:{os.environ['PATH']}", "FAKE_LAKE": str(self.fake)}

    def run_check(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), "--project", str(self.project), *args],
                              capture_output=True, text=True, env=self.env)

    def test_allowed_axioms_pass_and_the_receipt_says_what_was_found(self):
        receipt = self.root / "out/axioms.json"
        done = self.run_check("--unbound", "--receipt", str(receipt))
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("riemannHypothesis: Classical.choice, Quot.sound, propext", done.stdout)
        self.assertIn("LFunction_eq_zero_re: no axioms", done.stdout)
        value = json.loads(receipt.read_text())
        head = subprocess.check_output(["git", "-C", str(self.project), "rev-parse", "HEAD"], text=True).strip()
        self.assertEqual({key: value[key] for key in ("kind", "passed", "problems", "bound_to_completed_build", "candidate_head",
                                                       "inputs_committed", "solution_module", "permitted_axioms", "kinds")},
                         {"kind": "axioms-of-judged-theorems", "passed": True, "problems": [], "bound_to_completed_build": False,
                          "candidate_head": head, "inputs_committed": True, "solution_module": "Main",
                          "permitted_axioms": sorted(PERMITTED), "kinds": dict.fromkeys(NAMES, "theorem")})
        self.assertEqual(value["lean_version"], "Lean (version 0.0.0, a stand-in)")
        self.assertEqual(value["axioms"], {"riemannHypothesis": ["Classical.choice", "Quot.sound", "propext"], "LFunction_eq_zero_re": []})
        self.assertEqual(value["solution_artifacts_sha256"], {"Main.olean": check.sha256(self.project / ".lake/build/lib/lean/Main.olean")})
        self.assertEqual(value["comparator_sha256"], check.sha256(self.project / "comparator.json"))
        self.assertEqual((self.fake / "calls").read_text().split("\n")[0], "build --no-build +Main")
        self.assertIn('"riemannHypothesis", "LFunction_eq_zero_re"', (self.fake / "asked.lean").read_text())

    def test_sorry_another_axiom_a_missing_theorem_and_a_definition_fail_the_check(self):
        for text, said in ((answer(second=("My.axiom", "sorryAx")), "`LFunction_eq_zero_re` depends on `My.axiom`, `sorryAx`"),
                           (answer(kind="definition"), "`LFunction_eq_zero_re` is no theorem"),
                           (GOOD.replace("TOKEN\tAXIOMS\tLFunction_eq_zero_re\ttheorem\t0", "TOKEN\tMISSING\tLFunction_eq_zero_re"),
                            "`LFunction_eq_zero_re` does not exist")):
            with self.subTest(said=said):
                (self.fake / "answer").write_text(text)
                receipt = self.root / f"axioms-{abs(hash(said))}.json"
                done = self.run_check("--unbound", "--receipt", str(receipt))
                self.assertEqual(done.returncode, 1, done.stderr)
                self.assertIn(said, done.stderr)
                self.assertEqual(json.loads(receipt.read_text())["passed"], False)

    def test_what_cannot_be_checked_ends_with_two_and_writes_no_receipt(self):
        receipt = self.root / "axioms.json"
        for file, text, said in (("build-code", "1", "is not built"), ("lean-code", "1", "Lean ended with 1"),
                                 ("answer", GOOD.replace("TOKEN\tEND\t2\n", ""), "did not come to its end"),
                                 ("answer", GOOD.replace("TOKEN", "check-axioms-ffff"), "did not come to its end")):
            with self.subTest(file=file, said=said):
                kept = (self.fake / file).read_text() if (self.fake / file).exists() else None
                (self.fake / file).write_text(text)
                done = self.run_check("--unbound", "--receipt", str(receipt))
                self.assertEqual(done.returncode, 2)
                self.assertIn(said, done.stderr)
                self.assertFalse(receipt.exists())
                (self.fake / file).unlink() if kept is None else (self.fake / file).write_text(kept)
        (self.root / "file").write_text("in the way")
        self.assertEqual(self.run_check("--unbound", "--receipt", str(self.root / "file/axioms.json")).returncode, 2)
        (self.project / ".lake/build/lib/lean/Main.olean").unlink()
        self.assertEqual(self.run_check("--unbound").returncode, 2)

    def test_an_edited_input_is_said_in_the_receipt(self):
        for file in ("lean-toolchain", "src/Main.lean", "comparator.json"):
            with self.subTest(file=file):
                kept = (self.project / file).read_text()
                (self.project / file).write_text(kept + " ")
                receipt = self.root / f"axioms-{file.replace('/', '-')}.json"
                self.assertEqual(self.run_check("--unbound", "--receipt", str(receipt)).returncode, 0)
                self.assertEqual(json.loads(receipt.read_text())["inputs_committed"], False)
                (self.project / file).write_text(kept)

    def test_a_tree_without_git_and_without_lean_on_the_path_is_still_checked(self):
        (self.project / ".git").rename(self.root / "git-moved-away")
        tools = self.root / "only-lake"
        tools.mkdir()
        (tools / "lake").write_text(LAKE)
        (tools / "lake").chmod(0o755)
        self.env["PATH"] = f"{tools}:/usr/bin:/bin"
        receipt = self.root / "bare.json"
        done = self.run_check("--unbound", "--receipt", str(receipt))
        self.assertEqual(done.returncode, 0, done.stderr)
        value = json.loads(receipt.read_text())
        self.assertEqual((value["candidate_head"], value["inputs_committed"], value["passed"]), (None, False, True))

    def test_each_run_makes_up_its_own_word(self):
        words = []
        for _ in range(2):
            self.assertEqual(self.run_check("--unbound").returncode, 0)
            asked = (self.fake / "asked.lean").read_text()
            words.append(asked.split('IO.println ("', 1)[1].split("\\t", 1)[0])
        self.assertNotEqual(words[0], words[1])
        self.assertRegex(words[0], r"\Acheck-axioms-[0-9a-f]{32}\Z")

    def test_a_stale_receipt_is_not_written_over(self):
        stale = self.root / "stale.json"
        stale.write_text("{}")
        self.assertEqual(self.run_check("--unbound", "--receipt", str(stale)).returncode, 2)
        self.assertEqual(stale.read_text(), "{}")


class Bound(unittest.TestCase):
    """The run after a completed build, with stand-ins for the repository's own checks and toolchain."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.project, self.fake, _ = make_project(self.root)
        self.toolchain = self.root / "toolchain"
        (self.toolchain / "bin").mkdir(parents=True)
        (self.toolchain / "bin/lake").write_text(LAKE)
        (self.toolchain / "bin/lean").write_text("#!/bin/sh\necho 'Lean (version 9.9.9, commit abc123, Release)'\n")
        for tool in ("lake", "lean"):
            (self.toolchain / "bin" / tool).chmod(0o755)
        self.files = {}
        for name, text in (("map", "{}"), ("log", "Build completed successfully (7 jobs).\n"), ("receipt", "{}")):
            self.files[name] = self.root / name
            self.files[name].write_text(text)
        self.head = subprocess.check_output(["git", "-C", str(self.project), "rev-parse", "HEAD"], text=True).strip()
        self.identities, self.valid = 0, True
        self.entries, self.traces = {"aaaa": "x.ltar", "bbbb": "y.ltar"}, ["aaaa", "bbbb", "cccc"]
        for patcher in (patch.object(check, "repository_modules", side_effect=self.modules), patch("builtins.print"),
                        patch.dict(os.environ, {"LEAKED": "from-the-caller"})):
            patcher.start()
            self.addCleanup(patcher.stop)

    def modules(self):
        """Stand-ins for the repository's two scripts, fresh for each run as the real ones are."""
        selected = SimpleNamespace(TOOLCHAIN="leanprover/lean4:v9.9.9", VERSION="9.9.9", COMMIT="abc123")
        ci = SimpleNamespace(TOOLCHAIN=selected.TOOLCHAIN, settings=SimpleNamespace(for_toolchain=lambda release: selected),
                             safe_file=lambda root, name: Path(root) / name, sha256=check.sha256,
                             trusted_env=lambda: {"PATH": os.environ["PATH"], "FAKE_LAKE": str(self.fake)},
                             load_map=lambda path: self.entries,
                             module_traces=lambda project: [("M", Path("M"), key) for key in self.traces])
        return ci, SimpleNamespace(identity=self.identity, validate_receipt=self.validate)

    def identity(self, project, selected):
        self.identities += 1
        return {"candidate_head": self.head, "candidate_tree": "t" * 40}

    def validate(self, receipt, current, selected, log, mapping):
        if not self.valid or (self.valid == "once" and self.identities > 1):
            raise ValueError("completed build receipt does not bind current inputs, default scope, log and map")

    def arguments(self, *leave_out):
        self.out = self.root / f"axioms-{self.identities}-{len(leave_out)}.json"
        words = {"--project": self.project, "--build-map": self.files["map"], "--build-log": self.files["log"],
                 "--build-receipt": self.files["receipt"], "--receipt": self.out, "--toolchain": self.toolchain}
        return [str(item) for key, value in words.items() if key not in leave_out for item in (key, value)]

    def test_the_receipt_names_the_build_and_the_registered_tools_run_in_the_trusted_environment(self):
        self.assertEqual(check.main(self.arguments()), 0)
        value = json.loads(self.out.read_text())
        self.assertEqual({key: value[key] for key in ("bound_to_completed_build", "candidate_head", "candidate_tree", "toolchain",
                                                       "toolchain_commit", "lean_version", "passed")},
                         {"bound_to_completed_build": True, "candidate_head": self.head, "candidate_tree": "t" * 40,
                          "toolchain": "leanprover/lean4:v9.9.9", "toolchain_commit": "abc123",
                          "lean_version": "Lean (version 9.9.9, commit abc123, Release)", "passed": True})
        self.assertEqual((value["build_receipt_sha256"], value["build_log_sha256"], value["map_sha256"]),
                         tuple(check.sha256(self.files[name]) for name in ("receipt", "log", "map")))
        calls = (self.fake / "calls").read_text().strip().split("\n")
        self.assertEqual(calls[0], "--rehash build --no-build +Main")
        self.assertTrue(calls[1].startswith(f"env {self.toolchain}/bin/lean "))
        self.assertEqual(set((self.fake / "environment").read_text().strip().split("\n")), {"none leanprover/lean4:v9.9.9 1"})
        self.assertEqual(self.identities, 2)  # before and after the run

    def test_the_theorems_and_the_allowed_axioms_are_the_commits_not_the_working_trees(self):
        (self.fake / "answer").write_text(answer(second=("sorryAx",)))
        loose = json.loads(CONFIG)
        loose["permitted_axioms"].append("sorryAx")
        (self.project / "comparator.json").write_text(json.dumps(loose))
        self.assertEqual(check.main(self.arguments()), 1)
        value = json.loads(self.out.read_text())
        self.assertEqual((value["permitted_axioms"], value["problems"]), (sorted(PERMITTED), ["`LFunction_eq_zero_re` depends on `sorryAx`"]))
        self.assertEqual(value["comparator_sha256"], check.hashlib.sha256(CONFIG.encode()).hexdigest())

    def test_a_receipt_that_does_not_bind_the_tree_stops_the_check_before_lean_runs(self):
        self.valid = False
        self.assertEqual(check.main(self.arguments()), 2)
        self.assertFalse(self.out.exists())
        self.assertFalse((self.fake / "calls").exists())

    def test_a_build_directory_whose_traces_do_not_cover_the_map_is_refused(self):
        for entries, traces in (({"aaaa": "x.ltar", "dddd": "z.ltar"}, ["aaaa", "bbbb"]), ({}, ["aaaa"])):
            with self.subTest(entries=entries):
                self.entries, self.traces = entries, traces
                self.assertEqual(check.main(self.arguments()), 2)
                self.assertFalse(self.out.exists())
        self.assertFalse((self.fake / "calls").exists())

    def test_inputs_that_change_during_the_run_leave_no_receipt(self):
        self.valid = "once"
        self.assertEqual(check.main(self.arguments()), 2)
        self.assertFalse(self.out.exists())

    def test_a_log_without_a_completed_build_and_another_toolchain_are_refused(self):
        self.files["log"].write_text("error: build failed\n")
        self.assertEqual(check.main(self.arguments()), 2)
        self.files["log"].write_text("Build completed successfully (7 jobs).\n")
        (self.toolchain / "bin/lean").write_text("#!/bin/sh\necho 'Lean (version 1.0.0, commit fff, Release)'\n")
        self.assertEqual(check.main(self.arguments()), 2)
        self.assertFalse((self.fake / "calls").exists())

    def test_the_options_have_to_say_which_kind_of_run_it_is(self):
        # Every other check would let these runs through, so only the reading of the options stops them.
        cases = (self.arguments() + ["--unbound"], self.arguments("--build-map"), self.arguments("--build-log"),
                 self.arguments("--build-receipt"), self.arguments("--receipt"),
                 ["--project", str(self.project), "--unbound", "--toolchain", str(self.toolchain)],
                 ["--project", str(self.project), "--unbound", "--release", "x"], ["--project", str(self.project)])
        for arguments in cases:
            with self.subTest(arguments=arguments[2:]):
                with patch("sys.stderr"), self.assertRaises(SystemExit) as stopped:
                    check.main(arguments)
                self.assertEqual(stopped.exception.code, 2)
        self.assertFalse((self.fake / "calls").exists())


if __name__ == "__main__":
    unittest.main()
