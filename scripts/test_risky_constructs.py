#!/usr/bin/env python3
"""Reading and comparison checks on a small local repository; no GitHub calls."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("risky-constructs.py")
spec = importlib.util.spec_from_file_location("risky_constructs", SCRIPT)
risky = importlib.util.module_from_spec(spec)
spec.loader.exec_module(risky)

IDENTITY = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
            "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
CLEAN = "theorem two : 1 + 1 = 2 := by\n  rfl\n"


class Repository:
    """A throwaway repository with one base commit and one branch per case."""

    def __init__(self, root):
        self.root = Path(root)
        self.git("init", "--quiet", "--initial-branch=main")
        self.write("src/A.lean", CLEAN)
        self.write("src/Old.lean", "theorem old : True := by\n  sorry\n")
        self.write("src/Challenge.lean", "theorem riemannHypothesis : RiemannHypothesis := by sorry\n")
        self.write("README.md", "Nothing here uses sorry.\n")
        self.base = self.commit("base")

    def git(self, *args):
        done = subprocess.run(["git", "-C", str(self.root), "-c", "commit.gpgsign=false", *args],
                              check=True, capture_output=True, env={**os.environ, **IDENTITY})
        return done.stdout.decode().strip()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def commit(self, message):
        self.git("add", "--all")
        self.git("commit", "--quiet", "--message", message)
        return self.git("rev-parse", "HEAD")

    def branch(self, name, files, *, delete=()):
        """A branch off the base commit that writes `files` and deletes `delete`. Returns its head."""
        self.git("checkout", "--quiet", "-b", name, self.base)
        for path, text in files.items():
            self.write(path, text)
        for path in delete:
            (self.root / path).unlink()
        return self.commit(name)


def names(findings):
    return [(path.decode(), name, lines) for path, name, _, lines in findings]


class Reading(unittest.TestCase):
    def found(self, text):
        return risky.scan(text.encode())

    def test_each_construct_is_found_with_its_line(self):
        cases = {
            "theorem t : False := by\n  sorry\n": {"sorry": [2]},
            "theorem t : False := sorryAx _\n": {"sorry": [1]},
            "example : False := by admit\n": {"admit": [1]},
            "\naxiom cheat : False\n": {"axiom": [2]},
            "private axiom cheat : False\n": {"axiom": [1]},
            "example : 2 + 2 = 4 := by native_decide\n": {"native_decide": [1]},
            "example : 2 + 2 = 4 := by decide +native\n": {"native_decide": [1]},
            "@[implemented_by fast] def slow := 1\n": {"implemented_by or extern": [1]},
            "@[extern \"c_fn\"] opaque fn : Nat\n": {"implemented_by or extern": [1], "opaque": [1]},
            "unsafe def cast := 1\n": {"unsafe": [1]},
            "set_option debug.skipKernelTC true in\nexample := 1\n": {"set_option debug": [1], "skipKernelTC": [1]},
            "run_cmd Lean.Elab.Command.liftCoreM (addDecl d)\n":
                {"run_cmd, run_elab, run_meta or #eval": [1], "addDecl or addAndCompile": [1]},
            "#eval 1 + 1\n": {"run_cmd, run_elab, run_meta or #eval": [1]},
            "initialize ext : Nat ← pure 1\n": {"initialize": [1]},
            "example : False := by\n  sorry; sorry\n": {"sorry": [2, 2]},
            "theorem t : 1 + 1 = 3 := by\n  stop\n  simp\n": {"stop": [2]},
            "theorem t : 1 + 1 = 3 := by stop simp\n": {"stop": [1]},
            "example : 2 + 2 = 4 := by decide (config := { native := true })\n": {"native_decide": [1]},
            "set_option\n  debug.skipKernelTC true in\nexample := 1\n": {"set_option debug": [1], "skipKernelTC": [2]},
        }
        for text, expected in cases.items():
            with self.subTest(text=text):
                self.assertEqual(self.found(text), expected)

    def test_the_stop_tactic_is_found_where_a_tactic_stands(self):
        for line in ("  case inl h => stop simp", "  | zero => stop simp", "  next => stop", "  . stop",
                     "  · stop simp", "  try stop simp", "  all_goals stop simp", "  first | stop simp | rfl",
                     "  simp <|> stop simp", "  if h : p then stop simp else rfl", "decreasing_by stop simp",
                     "  simp; stop simp", "  simp <;> stop simp", "  stop"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n"), {"stop": [2]})

    def test_a_name_called_stop_is_not_found(self):
        for line in ("  exact f (stop step : Nat)", "  exact (stop + 1)", "  exact (stop, start)", "  exact {stop}",
                     "  exact (stop.le)", "  exact { stop with x := 1 }", "  exact g (stop' : Nat)",
                     "    stop n", "  rw [hp.stop] at this", "  match x with | stop => 1", "  exact f stop",
                     "  exact bystop", "  cases h with | stop h => exact h"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n"), {})

    def test_a_comment_between_two_words_does_not_hide_a_construct(self):
        self.assertEqual(self.found("example : True := by /- c -/ stop simp\n"), {"stop": [1]})
        self.assertEqual(self.found("set_option /- c -/ debug.skipKernelTC true in\nexample := 1\n"),
                         {"set_option debug": [1], "skipKernelTC": [1]})
        self.assertEqual(self.found("example : 2 + 2 = 4 := by decide (config := { native /- c -/ := true })\n"),
                         {"native_decide": [1]})

    def test_names_that_only_contain_a_word_are_not_found(self):
        for text in ("theorem sorry_free : True := trivial\n", "def unsafeCast := 1\n",
                     "theorem axiomatic : True := trivial\n", "example := by decide +kernel\n",
                     "set_option allowUnsafeReducibility true in\nexample := 1\n",
                     "def opaqueness := 1\n", "theorem admits_basis : True := trivial\n",
                     "example := by rw [hp.stop] at this\n", "structure S where\n  stop : 1 = 1\n",
                     "initialize_simps_projections Foo\n"):
            with self.subTest(text=text):
                self.assertEqual(self.found(text), {})

    def test_comments_and_strings_are_not_read(self):
        for text in ("-- sorry, this proof is long\ntheorem t : True := trivial\n",
                     "/-- Uses no axiom beyond choice; we admit nothing. -/\ntheorem t : True := trivial\n",
                     "/- outer /- sorry -/ still a comment: axiom -/\ntheorem t : True := trivial\n",
                     "/-! # Heading\nunsafe opaque sorry\n-/\ntheorem t : True := trivial\n",
                     'def message := "sorry -- not a comment"\n',
                     'def message := "an \\" escaped quote, then sorry"\n',
                     'def message := r#"raw "sorry" text"#\n',
                     "theorem t : True := trivial -- axiom\n"):
            with self.subTest(text=text):
                self.assertEqual(self.found(text), {})

    def test_code_after_a_comment_or_string_is_read(self):
        self.assertEqual(self.found("/- note -/ theorem t : False := by sorry\n"), {"sorry": [1]})
        self.assertEqual(self.found('def a := "text"\naxiom b : False\n'), {"axiom": [2]})
        self.assertEqual(self.found('def a := "--"\naxiom b : False\n'), {"axiom": [2]})
        self.assertEqual(self.found("def a := '\"'\naxiom b : False\n"), {"axiom": [2]})
        self.assertEqual(self.found("theorem t (h' : True) : False := by sorry\n"), {"sorry": [1]})
        self.assertEqual(self.found("/-\nlong\ncomment\n-/\ntheorem t : False := by\n  sorry\n"), {"sorry": [6]})

    def test_a_doc_comment_opener_is_one_token(self):
        # Lean reads `/--/` as an open doc comment, not as an empty comment. What follows the
        # real end is code, and a quote inside the comment must not swallow it.
        self.assertEqual(self.found('/--/ " -/\naxiom hidden : False\n'), {"axiom": [2]})
        # `/-!/` cannot be read as closed either way; this one only pins the behaviour.
        self.assertEqual(self.found('/-!/ " -/\naxiom hidden : False\n'), {"axiom": [2]})
        self.assertEqual(self.found("/- a /--/ b -/\naxiom after : False\n"), {"axiom": [2]})
        self.assertEqual(self.found("/--/ sorry -/\ntheorem t : True := trivial\n"), {})

    def test_an_unterminated_comment_hides_the_rest(self):
        self.assertEqual(self.found("/- never closed\naxiom b : False\n"), {})


class Comparing(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Repository(directory.name)

    def added(self, head):
        return names(risky.added(self.repo.root, self.repo.base, head))

    def test_a_clean_change_passes(self):
        head = self.repo.branch("clean", {"src/A.lean": CLEAN + "theorem three : 1 + 2 = 3 := by\n  rfl\n"})
        self.assertEqual(self.added(head), [])

    def test_a_sorry_in_a_changed_file_is_found(self):
        head = self.repo.branch("sorry", {"src/A.lean": "theorem two : 1 + 1 = 2 := by\n  sorry\n"})
        self.assertEqual(self.added(head), [("src/A.lean", "sorry", [2])])

    def test_an_axiom_in_a_new_file_is_found(self):
        head = self.repo.branch("axiom", {"src/Deep/New.lean": "axiom cheat : False\n"})
        self.assertEqual(self.added(head), [("src/Deep/New.lean", "axiom", [1])])

    def test_a_construct_that_was_already_there_passes(self):
        head = self.repo.branch("same", {"src/Old.lean": "theorem old : True := by\n  sorry\n\ntheorem new : True := trivial\n"})
        self.assertEqual(self.added(head), [])

    def test_one_more_of_a_construct_that_was_there_is_found(self):
        head = self.repo.branch("more", {"src/Old.lean": "theorem old : True := by\n  sorry\n\ntheorem new : True := by\n  sorry\n"})
        self.assertEqual(self.added(head), [("src/Old.lean", "sorry", [2, 5])])

    def test_the_challenge_other_directories_and_deleted_files_are_not_read(self):
        head = self.repo.branch("elsewhere", {
            "src/Challenge.lean": "theorem riemannHypothesis : RiemannHypothesis := by sorry\n-- changed\n",
            "comparator/Extra.lean": "axiom elsewhere : False\n",
            "scripts/tool.py": "sorry = 1\n",
            "src/notes.txt": "sorry\n"}, delete=("src/Old.lean",))
        self.assertEqual(self.added(head), [])

    def test_a_word_in_a_comment_passes(self):
        head = self.repo.branch("comment", {"src/A.lean": "/-- We admit no axiom here, sorry. -/\n" + CLEAN})
        self.assertEqual(self.added(head), [])

    def test_a_path_that_is_not_ascii_is_read(self):
        head = self.repo.branch("odd", {"src/GaloisCohomology₂/Ω.lean": "theorem t : False := by\n  native_decide\n"})
        self.assertEqual(self.added(head), [("src/GaloisCohomology₂/Ω.lean", "native_decide", [2])])

    def test_only_what_the_pull_request_changed_counts(self):
        # main moves on after the pull request branched off; that change is not the pull request's.
        head = self.repo.branch("mine", {"src/A.lean": CLEAN + "-- mine\n"})
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/B.lean", "axiom later : False\n")
        later = self.repo.commit("later on main")
        fork = self.repo.git("merge-base", later, head)
        self.assertEqual(fork, self.repo.base)
        self.assertEqual(names(risky.added(self.repo.root, fork, head)), [])

    def test_the_whole_tree_can_be_scanned(self):
        found = names(risky.everything(self.repo.root, self.repo.base))
        self.assertEqual(found, [("src/Old.lean", "sorry", [2])])

    def test_the_report_fails_only_when_something_was_added(self):
        with contextlib.redirect_stdout(io.StringIO()) as clean:
            self.assertEqual(risky.report([], resume="token"), 0)
        self.assertEqual(clean.getvalue().splitlines(), ["No risky construct was added.", "::token::"])
        with contextlib.redirect_stdout(io.StringIO()) as failing:
            self.assertEqual(risky.report([(b"src/A.lean", "sorry", 0, [2, 9])], resume="token"), 1)
        lines = failing.getvalue().splitlines()
        self.assertEqual(lines[0], "src/A.lean: sorry: line 2, 9")
        self.assertEqual(lines[-2:], ["::token::", "::error file=src/A.lean,line=2::This pull request adds `sorry` to src/A.lean."])
        with contextlib.redirect_stdout(io.StringIO()) as plain:
            self.assertEqual(risky.report([(b"src/A.lean", "sorry", 1, [2, 9])]), 1)
        self.assertEqual(plain.getvalue().splitlines()[0], "src/A.lean: sorry: line 2, 9 (this file had 1 before)")
        self.assertNotIn("::", plain.getvalue())

    def test_a_file_name_cannot_write_a_workflow_command(self):
        name = "src/a\n::error::made up, 100%##[add-mask]x.lean".encode()
        with contextlib.redirect_stdout(io.StringIO()) as out:
            risky.report([(name, "sorry", 0, [1])], resume="token")
        lines = out.getvalue().splitlines()
        resumed = lines.index("::token::")
        # While commands are off the name may be printed, but never at the start of a line.
        self.assertEqual(lines[0], "src/a\\x0a::error::made up, 100%##[add-mask]x.lean: sorry: line 1")
        self.assertFalse(any(line.startswith(("::", "##[")) for line in lines[:resumed]))
        # After that there is exactly the annotation, with the name escaped for a property.
        self.assertEqual(lines[resumed + 1:],
                         ["::error file=src/a\\x0a%3A%3Aerror%3A%3Amade up%2C 100%25##[add-mask]x.lean,line=1::"
                          "This pull request adds `sorry` to src/a\\x0a::error::made up, 100%25##[add-mask]x.lean."])


class Fetching(unittest.TestCase):
    """The path the workflow takes: an empty directory, commits fetched without file contents."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "upstream").mkdir()
        self.repo = Repository(self.root / "upstream")
        # What GitHub allows: fetching without file contents, and fetching a commit or a file by id.
        self.repo.git("config", "uploadpack.allowFilter", "true")
        self.repo.git("config", "uploadpack.allowAnySHA1InWant", "true")

    def run_script(self, head, work):
        return subprocess.run([sys.executable, str(SCRIPT), "--annotate", "--work", str(self.root / work),
                               "--remote", self.repo.root.as_uri(), "--base", self.repo.base, "--head", head],
                              capture_output=True, text=True)

    def test_a_clean_pull_request_passes(self):
        head = self.repo.branch("clean", {"src/A.lean": CLEAN + "theorem three : 1 + 2 = 3 := by\n  rfl\n"})
        done = self.run_script(head, "clean")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("No risky construct was added.", done.stdout)

    def test_an_added_construct_fails_with_file_and_line(self):
        head = self.repo.branch("axiom", {"src/Deep/New.lean": "/-- A doc. -/\naxiom cheat : False\n",
                                          "src/Old.lean": "theorem old : True := by\n  sorry\n-- touched\n"})
        done = self.run_script(head, "axiom")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        lines = done.stdout.splitlines()
        self.assertRegex(lines[0], r"^::stop-commands::[0-9a-f]{32}$")
        token = lines[0].removeprefix("::stop-commands::")
        self.assertEqual(lines[lines.index(f"::{token}::") + 1:],
                         ["::error file=src/Deep/New.lean,line=2::This pull request adds `axiom` to src/Deep/New.lean."])
        self.assertNotIn("src/Old.lean", done.stdout)

    def test_only_the_changed_files_are_fetched(self):
        head = self.repo.branch("big", {"src/A.lean": CLEAN + "-- changed\n"})
        done = self.run_script(head, "big")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        work = self.root / "big"

        def here(path):
            blob = self.repo.git("rev-parse", f"{head}:{path}")
            found = subprocess.run(["git", "-C", str(work), "cat-file", "--batch-check"], input=blob + "\n",
                                   capture_output=True, text=True, env={**os.environ, "GIT_NO_LAZY_FETCH": "1"})
            return not found.stdout.strip().endswith("missing")

        self.assertTrue(here("src/A.lean"), "the changed file was not fetched")
        self.assertFalse(here("src/Old.lean"), "an unchanged file was fetched")
        self.assertFalse(here("README.md"), "an unchanged file was fetched")


if __name__ == "__main__":
    unittest.main()
