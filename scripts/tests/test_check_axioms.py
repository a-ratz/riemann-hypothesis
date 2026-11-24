#!/usr/bin/env python3
"""The axiom check without Lean: its reading of Lean's answer, its verdict, and its runs against a stand-in for lake."""
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "check-axioms.py"
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
# A stand-in for lake. It notes each call, where it ran and two variables of its environment,
# passes over Lake's own options, ends `build` with the code in the file `build-code`, and
# answers `env ... FILE` with the file `answer`, in which it puts the word made up for this
# run, and the code in `lean-code`.
LAKE = '''#!/bin/sh
dir="$FAKE_LAKE"
echo "$*" >> "$dir/calls"
pwd >> "$dir/where"
echo "${LEAKED:-none} ${INSIDE:-no}" >> "$dir/environment"
while :; do case "$1" in --packages) shift 2 ;; --rehash) shift ;; *) break ;; esac; done
case "$1" in
  build) exit "$(cat "$dir/build-code" 2>/dev/null || echo 0)" ;;
  env) for file; do :; done
       cp "$file" "$dir/asked.lean"
       token=$(grep -o 'check-axioms-[0-9a-f]*' "$file" | head -1)
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
                 "a count in digits of another kind": GOOD.replace(second, second.replace("\t0", "\t٠")),
                 "a count that is a digit and no number": GOOD.replace(second, second.replace("\t0", "\t²")),
                 "a count with a sign": GOOD.replace(second, second.replace("\t0", "\t+0")),
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


def make_project(root):
    """A project with a `comparator.json`, a stand-in for lake on a path, and the stand-in's notes."""
    project, fake, tools = root / "project", root / "fake", root / "bin"
    for path in (project, fake, tools):
        path.mkdir(parents=True)
    (tools / "lake").write_text(LAKE)
    (tools / "lake").chmod(0o755)
    (project / "comparator.json").write_text(CONFIG)
    (fake / "answer").write_text(GOOD)
    return project, fake, tools


class Running(unittest.TestCase):
    """The script as a command on a contributor's tree, with a stand-in for lake on the path."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.project, self.fake, tools = make_project(self.root)
        self.env = {**os.environ, "PATH": f"{tools}:{os.environ['PATH']}", "FAKE_LAKE": str(self.fake)}

    def run_check(self, *args, cwd=None):
        args = args if cwd else ("--project", str(self.project), *args)
        return subprocess.run([sys.executable, str(SCRIPT), *args], capture_output=True, text=True, env=self.env, cwd=cwd)

    def test_allowed_axioms_pass_and_lake_is_asked_for_the_module_first(self):
        done = self.run_check()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("riemannHypothesis: Classical.choice, Quot.sound, propext", done.stdout)
        self.assertIn("LFunction_eq_zero_re: no axioms", done.stdout)
        self.assertEqual(json.loads(done.stdout.strip().split("\n")[-1]), {"axioms_checked": True, "passed": True, "theorems": 2})
        calls = (self.fake / "calls").read_text().strip().split("\n")
        self.assertEqual(calls[0], "build --no-build +Main")
        self.assertRegex(calls[1], r"\Aenv lean \S+/CheckAxioms\.lean\Z")
        self.assertEqual(set((self.fake / "where").read_text().strip().split("\n")), {str(self.project.resolve())})
        self.assertIn('"riemannHypothesis", "LFunction_eq_zero_re"', (self.fake / "asked.lean").read_text())

    def test_without_a_project_the_directory_it_runs_in_is_checked(self):
        done = self.run_check(cwd=self.project)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(set((self.fake / "where").read_text().strip().split("\n")), {str(self.project.resolve())})

    def test_sorry_another_axiom_a_missing_theorem_and_a_definition_fail_the_check(self):
        for text, said in ((answer(second=("My.axiom", "sorryAx")), "`LFunction_eq_zero_re` depends on `My.axiom`, `sorryAx`"),
                           (answer(kind="definition"), "`LFunction_eq_zero_re` is no theorem"),
                           (GOOD.replace("TOKEN\tAXIOMS\tLFunction_eq_zero_re\ttheorem\t0", "TOKEN\tMISSING\tLFunction_eq_zero_re"),
                            "`LFunction_eq_zero_re` does not exist")):
            with self.subTest(said=said):
                (self.fake / "answer").write_text(text)
                done = self.run_check()
                self.assertEqual(done.returncode, 1, done.stderr)
                self.assertIn(said, done.stderr)
                self.assertEqual(json.loads(done.stdout.strip().split("\n")[-1])["passed"], False)

    def test_what_cannot_be_checked_ends_with_two(self):
        for file, text, said in (("build-code", "1", "is not built"), ("lean-code", "1", "Lean ended with 1"),
                                 ("answer", GOOD.replace("TOKEN\tEND\t2\n", ""), "did not come to its end"),
                                 ("answer", GOOD.replace("TOKEN", "check-axioms-ffff"), "did not come to its end")):
            with self.subTest(file=file, said=said):
                kept = (self.fake / file).read_text() if (self.fake / file).exists() else None
                (self.fake / file).write_text(text)
                done = self.run_check()
                self.assertEqual(done.returncode, 2)
                self.assertIn(said, done.stderr)
                self.assertNotIn("axioms_checked", done.stdout)
                (self.fake / file).unlink() if kept is None else (self.fake / file).write_text(kept)
        self.assertEqual(self.run_check().returncode, 0)
        path, self.env["PATH"] = self.env["PATH"], "/nowhere"
        done = self.run_check()
        self.assertEqual((done.returncode, "could not be started" in done.stderr), (2, True))
        self.env["PATH"] = path
        (self.project / "comparator.json").unlink()
        calls = (self.fake / "calls").read_text()
        done = self.run_check()
        self.assertEqual((done.returncode, "comparator.json" in done.stderr, "Traceback" in done.stderr), (2, True, False))
        self.assertEqual((self.fake / "calls").read_text(), calls, "lake ran without a comparator.json")

    def test_each_run_makes_up_its_own_word(self):
        words = []
        for _ in range(2):
            self.assertEqual(self.run_check().returncode, 0)
            asked = (self.fake / "asked.lean").read_text()
            words.append(asked.split('IO.println ("', 1)[1].split("\\t", 1)[0])
        self.assertNotEqual(words[0], words[1])
        self.assertRegex(words[0], r"\Acheck-axioms-[0-9a-f]{32}\Z")


class Checking(unittest.TestCase):
    """`check()` with a function in the place of Lake."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.source = Path(directory.name) / "CheckAxioms.lean"
        self.calls, self.text, self.codes = [], GOOD, {"build": 0, "env": 0}

    def lake(self, arguments):
        self.calls.append(arguments)
        if arguments[0] == "build":
            return self.codes["build"], "what lake said"
        return self.codes["env"], self.text.replace("TOKEN", re.search("check-axioms-[0-9a-f]+", self.source.read_text()).group())

    def test_lake_is_asked_for_the_module_and_then_for_lean_on_the_file_under_the_path_given(self):
        record = check.check(CONFIG.encode(), self.lake, self.source, "/control/CheckAxioms.lean")
        self.assertEqual(record, {"solution_module": "Main", "permitted_axioms": sorted(PERMITTED),
                                  "axioms": {"riemannHypothesis": ["Classical.choice", "Quot.sound", "propext"], "LFunction_eq_zero_re": []},
                                  "kinds": dict.fromkeys(NAMES, "theorem"), "problems": [], "passed": True})
        self.assertEqual(self.calls, [["build", "--no-build", "+Main"],
                                      ["env", "lean", "/control/CheckAxioms.lean"]])
        self.assertIn('"riemannHypothesis", "LFunction_eq_zero_re"', self.source.read_text())

    def test_without_another_path_lean_is_given_the_place_the_file_was_written_to(self):
        self.assertTrue(check.check(CONFIG.encode(), self.lake, self.source)["passed"])
        self.assertEqual(self.calls[1][-1], str(self.source))

    def test_the_config_it_is_given_decides(self):
        self.text = answer(second=("sorryAx",))
        record = check.check(CONFIG.encode(), self.lake, self.source)
        self.assertEqual((record["passed"], record["problems"], record["permitted_axioms"]),
                         (False, ["`LFunction_eq_zero_re` depends on `sorryAx`"], sorted(PERMITTED)))
        loose = json.loads(CONFIG)
        loose["permitted_axioms"].append("sorryAx")
        self.assertTrue(check.check(json.dumps(loose).encode(), self.lake, self.source)["passed"])

    def test_what_cannot_be_checked_raises_a_value_error_the_build_script_catches(self):
        self.assertTrue(issubclass(check.Unusable, ValueError))
        with self.assertRaises(check.Unusable):
            check.check(b"{}", self.lake, self.source)
        self.assertEqual(self.calls, [], "lake ran for a config that names no theorems")
        with self.assertRaises(check.Unusable):
            check.check(CONFIG.encode(), self.lake, self.source.parent / "absent/CheckAxioms.lean")
        for step, calls in (("build", 1), ("env", 2)):
            with self.subTest(step):
                self.calls, self.codes = [], {"build": 0, "env": 0, step: 3}
                with self.assertRaises(check.Unusable) as stopped:
                    check.check(CONFIG.encode(), self.lake, self.source)
                self.assertIn("ended with 3", str(stopped.exception))
                self.assertEqual(len(self.calls), calls)


class ThroughACommand(unittest.TestCase):
    """`through()` as a build would use it: Lake behind another command, and the Lean file in a place that command shows elsewhere."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.project, self.fake, tools = make_project(self.root)
        (self.root / "control").mkdir()
        (self.root / "shown").symlink_to(self.root / "control")  # the sandbox's view of the same directory
        self.source, self.seen = self.root / "control/CheckAxioms.lean", str(self.root / "shown/CheckAxioms.lean")
        # `env INSIDE=yes` stands in for the sandbox's command: what runs behind it sees INSIDE.
        self.command = ["/usr/bin/env", "INSIDE=yes", str(tools / "lake"), "--packages", "/control/packages.json", "--rehash"]
        self.env = {"PATH": "/usr/bin:/bin", "FAKE_LAKE": str(self.fake)}
        patcher = patch.dict(os.environ, {"LEAKED": "from-the-caller"})
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_both_commands_run_behind_the_command_given_in_the_directory_and_the_environment_given(self):
        lake = check.through(self.command, cwd=self.project, env=self.env)
        self.assertTrue(check.check(CONFIG.encode(), lake, self.source, self.seen)["passed"])
        self.assertEqual((self.fake / "calls").read_text().strip().split("\n"),
                         ["--packages /control/packages.json --rehash build --no-build +Main",
                          f"--packages /control/packages.json --rehash env lean {self.seen}"])
        self.assertEqual((self.fake / "environment").read_text().strip().split("\n"), ["none yes", "none yes"])
        self.assertEqual(set((self.fake / "where").read_text().strip().split("\n")), {str(self.project.resolve())})

    def test_it_returns_the_exit_code_and_what_was_printed_on_both_streams(self):
        script = self.root / "both"
        script.write_text("#!/bin/sh\necho \"out $1\"\necho \"err $2\" >&2\nexit 7\n")
        script.chmod(0o755)
        self.assertEqual(check.through([str(script), "a"])(["b"]), (7, "out a\nerr b\n"))

    def test_a_command_that_cannot_be_started_is_a_refusal_of_the_check(self):
        with self.assertRaises(check.Unusable) as stopped:
            check.through([str(self.root / "absent")])(["build"])
        self.assertIn("could not be started", str(stopped.exception))


TOY = """axiom Toy.myAxiom : (1 : Nat) = 1 → True
axiom Toy.«odd name» : True

theorem Toy.clean : 1 + 1 = 2 := rfl
theorem Toy.classical (p : Prop) : p ∨ ¬p := Classical.em p
theorem Toy.withSorry : 2 + 2 = 5 := sorry
theorem Toy.withAxiom : True := Toy.myAxiom rfl
theorem Toy.withOddAxiom : True := Toy.«odd name»
theorem Toy.helper : 2 + 2 = 5 := sorry
theorem Toy.viaHelper : 2 + 2 = 5 := Toy.helper

def Toy.aDef : Nat := 1
"""
LAKEFILE = 'name = "toy"\ndefaultTargets = ["Main"]\n\n[[lean_lib]]\nname = "Main"\n\n[[lean_lib]]\nname = "Toy"\nglobs = ["Toy.+"]\n'


@unittest.skipUnless(os.environ.get("CHECK_AXIOMS_WITH_LEAN") == "1" and shutil.which("lake"),
                     "builds two small projects with the `lake` on the path; set CHECK_AXIOMS_WITH_LEAN=1 to run it")
class WithLean(unittest.TestCase):
    """The Lean file itself: a small project is built, and Lean answers for its theorems."""

    def project(self, modules):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        project = Path(directory.name)
        (project / "Toy").mkdir()
        (project / "lakefile.toml").write_text(LAKEFILE)
        toolchain = SCRIPT.parents[1] / "lean-toolchain"
        if toolchain.exists():
            shutil.copy(toolchain, project / "lean-toolchain")
        text = TOY
        if modules:  # the module form: what is judged is public, the helper with the `sorry` is not
            text = "module\n\n" + re.sub(r"^(axiom|theorem|def) (?!Toy\.helper)", r"public \1 ", TOY, flags=re.M)
        (project / "Toy/Basic.lean").write_text(text)
        (project / "Main.lean").write_text("module\n\npublic import Toy.Basic\n" if modules else "import Toy.Basic\n")
        names = ["Toy.clean", "Toy.classical", "Toy.withSorry", "Toy.withAxiom", "Toy.withOddAxiom", "Toy.viaHelper",
                 "Toy.notThere", "Toy.aDef", "Toy.myAxiom"]
        (project / "comparator.json").write_text(json.dumps({"solution_module": "Main", "theorem_names": names, "permitted_axioms": PERMITTED}))
        built = subprocess.run(["lake", "build"], cwd=project, capture_output=True, text=True)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        return project

    def test_lean_names_the_kind_and_the_axioms_of_each_theorem(self):
        for modules in (False, True):
            with self.subTest(modules=modules):
                project = self.project(modules)
                config = (project / "comparator.json").read_bytes()
                record = check.check(config, check.through(["lake"], cwd=project), project / "CheckAxioms.lean")
                self.assertEqual(record["axioms"], {
                    "Toy.clean": [], "Toy.classical": ["Classical.choice", "Quot.sound", "propext"], "Toy.withSorry": ["sorryAx"],
                    "Toy.withAxiom": ["Toy.myAxiom"], "Toy.withOddAxiom": ["Toy.«odd name»"], "Toy.viaHelper": ["sorryAx"],
                    "Toy.notThere": None, "Toy.aDef": [], "Toy.myAxiom": ["Toy.myAxiom"]})
                self.assertEqual(record["kinds"], {
                    "Toy.clean": "theorem", "Toy.classical": "theorem", "Toy.withSorry": "theorem", "Toy.withAxiom": "theorem",
                    "Toy.withOddAxiom": "theorem", "Toy.viaHelper": "theorem", "Toy.aDef": "definition", "Toy.myAxiom": "axiom"})
                self.assertEqual(record["problems"], [
                    "`Toy.withSorry` depends on `sorryAx`", "`Toy.withAxiom` depends on `Toy.myAxiom`",
                    "`Toy.withOddAxiom` depends on `Toy.«odd name»`", "`Toy.viaHelper` depends on `sorryAx`",
                    "`Toy.notThere` does not exist in the solution module", "`Toy.aDef` is no theorem: Lean calls it definition",
                    "`Toy.myAxiom` is no theorem: Lean calls it axiom", "`Toy.myAxiom` depends on `Toy.myAxiom`"])
                clean = json.dumps({"solution_module": "Main", "theorem_names": ["Toy.clean", "Toy.classical"], "permitted_axioms": PERMITTED})
                self.assertTrue(check.check(clean.encode(), check.through(["lake"], cwd=project), project / "CheckAxioms.lean")["passed"])
                # A source edited after the build: Lake no longer finds the module built for it.
                with (project / "Toy/Basic.lean").open("a") as source:
                    source.write("\ntheorem Toy.late : 4 = 4 := rfl\n")
                with self.assertRaises(check.Unusable) as stopped:
                    check.check(clean.encode(), check.through(["lake"], cwd=project), project / "CheckAxioms.lean")
                self.assertIn("is not built", str(stopped.exception))


if __name__ == "__main__":
    unittest.main()
