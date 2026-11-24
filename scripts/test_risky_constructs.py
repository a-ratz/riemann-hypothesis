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
            "example : 2 + 2 = 4 := by decide (config := { native := true })\n": {"native_decide": [1, 1]},
            "example : 2 + 2 = 4 := by decide (config := { native := Bool.true })\n": {"native_decide": [1, 1]},
            "example : 2 + 2 = 4 := by decide (config := { native := !false })\n": {"native_decide": [1, 1]},
            # No listed word, and the compiler is switched on all the same.
            "example : 2 + 2 = 4 := by decide (config := ⟨false, true, true, false⟩)\n": {"native_decide": [1]},
            "example : 2 + 2 = 4 := by\n  decide\n    (config := c)\n": {"native_decide": [2]},
            "def c : Lean.Meta.Decide.Config := { native := true }\n": {"native_decide": [1]},
            "example := Lean.reduceBool true\n": {"native_decide": [1]},
            "example : p := by bv_check \"p.lrat\"\n": {"native_decide": [1]},
            # Options and other items may stand before the config.
            "example : 2 + 2 = 4 := by decide +revert (config := ⟨false, true, true, false⟩)\n": {"native_decide": [1]},
            "example : 2 + 2 = 4 := by decide (zetaReduce := true) (config := c)\n": {"native_decide": [1]},
            "example : 2 + 2 = 4 := by decide -zetaReduce (config := c)\n": {"native_decide": [1]},
            "example := by simp (config := ⟨1⟩)\n": {"native_decide": [1]},
            "theorem e (a b c : Nat) : a * b < c := by apply?\n": {"apply?": [1]},
            "theorem e (a b c : Nat) : a * b < c := by\n  apply? using h\n": {"apply?": [2]},
            "elab \"cheat\" : tactic => do Lean.Elab.admitGoal (← Lean.Elab.Tactic.getMainGoal)\n": {"admit": [1]},
            "def s (t : Lean.Expr) := Lean.Meta.mkSorry t true\n": {"sorry": [1]},
            "theorem sorry_free : True := trivial\n": {"sorry": [1]},
            "set_option\n  debug.skipKernelTC true in\nexample := 1\n": {"set_option debug": [1], "skipKernelTC": [2]},
        }
        for text, expected in cases.items():
            with self.subTest(text=text):
                self.assertEqual(self.found(text), expected)

    def test_the_stop_tactic_is_found_wherever_tactics_follow_it(self):
        # Compiled with Lean v4.37.0-rc1, each closing its goal with `sorryAx`: `stop simp` at the
        # start of a line, in `by (...)`, in `by { ... }`, after `focus`, `classical`, `try`,
        # `all_goals`, `;`, `=>` and in `first | ... | ...`. The other lines pin the same rule.
        for line in ("  stop simp", "  exact (by (stop simp))", "  exact (by { stop simp })", "  focus stop simp",
                     "  classical stop simp", "  case inl h => stop simp", "  | zero => stop simp", "  next => stop simp",
                     "  . stop simp", "  .stop simp", "  · stop simp", "  try stop simp", "  all_goals stop simp",
                     "  first | stop simp | rfl", "  first |stop simp | rfl", "  first | stop exact fun x => x | rfl",
                     "  simp <|> stop simp", "  if h : p then stop simp else rfl", "decreasing_by stop simp",
                     "  simp; stop simp", "  simp <;> stop simp", "  skip;stop simp", "  stop (simp)", "  stop(simp)",
                     "  stop · simp", "  stop . simp", "  stop $t", "  stop _root_.foo", "  stop {simp}", "  stop ⟨x⟩",
                     "  stop [x]", "  `(tactic|stop simp)"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n"), {"stop": [2]})

    def test_the_stop_tactic_is_found_with_its_tactics_on_the_next_line(self):
        # `stop` takes the tactics that follow it, on its line or below.
        for line in ("  stop", "  · stop", "  . stop", "  simp; stop", "  next => stop", "  all_goals stop", "  try stop",
                     "  simp <;> stop", "  exact (by stop", "  focus stop", "  first | stop", "  refine ⟨by stop",
                     "  classical stop", "  repeat stop", "  exact by {stop"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n    simp\n"), {"stop": [2]})
                self.assertEqual(self.found(f"example : True := by\n{line}\n\n  simp\n"), {"stop": [2]})
        self.assertEqual(self.found("example : True := by stop\n  simp\n"), {"stop": [1]})
        self.assertEqual(self.found("stop\nsimp\n"), {"stop": [1]})
        self.assertEqual(self.found("example : True := by\r\n  stop\r\n  simp\r\n"), {"stop": [2]})
        self.assertEqual(self.found("example : True := by\r\n  simp; stop\r\n  simp\r\n"), {"stop": [2]})

    def test_a_name_called_stop_is_not_found(self):
        for line in ("  exact (stop + 1)", "  exact (stop, start)", "  exact {stop}", "  exact (stop.le)",
                     "  exact { stop with x := 1 }", "  exact g (stop' : Nat)", "  rw [hp.stop] at this",
                     "  match x with | stop => 1", "  exact f stop", "  exact bystop", "  exact (stop : Nat)",
                     "  exact h (stop := 1)", "  exact stop ≤ n", "  exact if stop then a else b", "  exact if c then stop else b",
                     "  simp [h] at stop ⊢", "  exact fun stop => stop", "  rw [h] at stop", "  simpa using stop",
                     "  exact x.stop", "  induction stop generalizing n", "  exact stop from h", "  exact le_of stop in h",
                     "  exact foo stop where", "  cases stop with", "  exact stop at h", "  exact stop using h",
                     "  cases h with | stop h => exact h"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n"), {})
        self.assertEqual(self.found("structure S where\n  stop : 1 = 1\n"), {})
        # Last on its line where a tactic may begin, but nothing below it that it could take.
        self.assertEqual(self.found("example : Nat → Nat :=\n    fun stop => stop\ntheorem t : True := trivial\n"), {})
        # At the start of a line, `| stop h => ...` is an alternative, however far `stop` stands from the bar.
        for line in ("  | stop h => exact h", "  |stop h => exact h", "  |     stop h => exact h", "  | stop h | start h => exact h"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n  cases h with\n{line}\n"), {})

    def test_a_name_called_stop_before_another_word_is_taken_for_the_tactic(self):
        # A text search cannot tell these from `stop simp`. No file of the tree has one.
        for line in ("  exact f (stop step : Nat)", "    stop n", "  exact g stop x", "  intro stop h", "  exact fun stop n => n",
                     "  exact f «stop» x"):
            with self.subTest(line=line):
                self.assertEqual(self.found(f"example : True := by\n{line}\n"), {"stop": [2]})

    def test_a_comment_between_two_words_does_not_hide_a_construct(self):
        self.assertEqual(self.found("example : True := by /- c -/ stop simp\n"), {"stop": [1]})
        self.assertEqual(self.found("set_option /- c -/ debug.skipKernelTC true in\nexample := 1\n"),
                         {"set_option debug": [1], "skipKernelTC": [1]})
        self.assertEqual(self.found("example : 2 + 2 = 4 := by decide /- c -/ (config := { native /- c -/ := true })\n"),
                         {"native_decide": [1, 1]})

    def test_names_that_only_contain_a_word_are_not_found(self):
        for text in ("def unsafeCast := 1\n", "example := by decide\n", "example := by simp (config := { decide := true })\n",
                     "theorem admitted_pair : True := trivial\n", "example := by exact? \n", "example := by apply h?\n",
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

    def test_a_name_in_guillemets_is_one_token(self):
        # Each of these compiles; read as plain text, the name would open a comment or a string.
        self.assertEqual(self.found("def «/-» : Nat := 0\naxiom cheat : False\n"), {"axiom": [2]})
        self.assertEqual(self.found("theorem «t2--» : 1 = 2 := sorry\n"), {"sorry": [1]})
        self.assertEqual(self.found('def «a"» : Nat := 1\naxiom cheat : False\ndef b := "x"\n'), {"axiom": [2]})
        # Lean reads the name on over a line break.
        self.assertEqual(self.found("def «a\n/-» : Nat := 0\naxiom cheat : False\n-- -/\n"), {"axiom": [3]})
        # A guillemet that is never closed starts no name.
        self.assertEqual(self.found("example := x « y\naxiom cheat : False\n"), {"axiom": [2]})

    def test_a_name_in_guillemets_is_the_same_name(self):
        self.assertEqual(self.found("theorem t : False := «sorryAx» _ false\n"), {"sorry": [1]})
        self.assertEqual(self.found("example := Lean.«ofReduceBool» a b c\n"), {"native_decide": [1]})
        self.assertEqual(self.found("set_option «debug».«skipKernelTC» true in\nexample := 1\n"),
                         {"set_option debug": [1], "skipKernelTC": [1]})
        self.assertEqual(self.found("example : 2 + 2 = 4 := by decide («native» := true)\n"), {"native_decide": [1]})
        self.assertEqual(self.found("example := do «modifyEnv» id\n"), {"modifyEnv or setEnv": [1]})
        # The price: a name that is spelled like a keyword counts as the keyword.
        self.assertEqual(self.found("def «sorry» : Nat := 0\n"), {"sorry": [1]})

    def test_code_inside_an_interpolated_string_is_read(self):
        self.assertEqual(self.found('theorem i : True := by\n  have _x := s!"{(sorry : Nat)}"\n  trivial\n'), {"sorry": [2]})
        self.assertEqual(self.found('def a := m!"no {x} axiom here"\n'), {})
        self.assertEqual(self.found('def a := f!"sorry {"sorry"} \\{sorry}"\n'), {})
        self.assertEqual(self.found('def a := s!"{s!"{(sorry : Nat)}"}"\naxiom b : False\n'), {"sorry": [1], "axiom": [2]})
        self.assertEqual(self.found('def a := s!"line one\n{(sorry : Nat)}"\naxiom b : False\n'), {"sorry": [2], "axiom": [3]})
        # A macro of core that takes such a string, with or without a blank before it.
        self.assertEqual(self.found('example := do throwError "{(sorry : Nat)}"\n'), {"sorry": [1]})
        self.assertEqual(self.found('example := do throwError"{(sorry : Nat)}"\n'), {"sorry": [1]})
        self.assertEqual(self.found('example := do trace[Meta.debug] "{(sorry : Nat)}"\n'), {"sorry": [1]})
        self.assertEqual(self.found('example := do println! "{(sorry : Nat)}"\n'), {"sorry": [1]})
        self.assertEqual(self.found('example := f 1s!"{(sorry : Nat)}"\n'), {"sorry": [1]})

    def test_what_stands_in_the_braces_is_lexed_like_any_code(self):
        # None of these may hide the axiom after the string.
        for inner in ("'{'", "'}'", "'\\\"'", 'r"\\" ++ ""', "«{»", '"}"', "1 /- } -/ + 2", "{ x := 1 }.x", "{{}}"):
            with self.subTest(inner=inner):
                self.assertEqual(self.found(f'def a := s!"{{{inner}}}"\naxiom cheat : False\n'), {"axiom": [2]})
        self.assertEqual(self.found("def a := s!\"{('}', (sorry : Nat)).2}\"\n"), {"sorry": [1]})
        self.assertEqual(self.found('def a := s!"{1 /- } -/ + (sorry : Nat)}"\n'), {"sorry": [1]})
        self.assertEqual(self.found('def a := s!"{1 -- }\n  + (sorry : Nat)}"\naxiom b : False\n'), {"sorry": [2], "axiom": [3]})

    def test_a_plain_string_is_not_read_and_a_brace_in_it_opens_nothing(self):
        self.assertEqual(self.found('def a := "{(sorry : Nat)}"\n'), {})
        self.assertEqual(self.found('def a := "{"\naxiom cheat : False\n'), {"axiom": [2]})
        self.assertEqual(self.found('def a := "}{"\naxiom cheat : False\ndef b := "sorry"\n'), {"axiom": [2]})
        self.assertEqual(self.found('def a := xs[i] "{"\naxiom cheat : False\n'), {"axiom": [2]})

    def test_strings_nested_too_deeply_stop_the_run(self):
        with self.assertRaises(RuntimeError):
            self.found("def a := " + 's!"{' * 40 + " sorry\n")

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

    def test_a_change_to_what_is_built_is_found(self):
        self.repo.git("checkout", "--quiet", "main")
        for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
            self.repo.write(name, "as it was\n")
        self.repo.base = self.repo.commit("with a build configuration")
        cases = {"added": ({"lakefile.lean": "import Lake\n"}, (), ["lakefile.lean"]),
                 "modified": ({"lakefile.toml": 'name = "tree"\n[[lean_lib]]\nname = "Extra"\nsrcDir = "../extra"\n',
                               "extra/Evil.lean": "axiom cheat : False\n", "docs/lakefile.toml": "elsewhere\n"}, (), ["lakefile.toml"]),
                 "deleted": ({}, ("lean-toolchain", "lake-manifest.json"), ["lake-manifest.json", "lean-toolchain"])}
        for name, (files, delete, expected) in cases.items():
            with self.subTest(name):
                head = self.repo.branch(name, files, delete=delete)
                self.assertEqual(self.added(head), [(path, risky.CONFIGURED, [1]) for path in expected])

    def test_a_link_under_src_is_found(self):
        self.repo.git("checkout", "--quiet", "-b", "link", self.repo.base)
        (self.repo.root / "src/A.lean").unlink()
        (self.repo.root / "src/A.lean").symlink_to("../extra/A.lean")   # a file that becomes a link
        (self.repo.root / "src/Dir").symlink_to("../extra")             # a new link to a directory
        self.repo.write("extra/A.lean", "axiom cheat : False\n")
        head = self.repo.commit("links")
        self.assertEqual(self.added(head), [("src/A.lean", risky.LINKED, [1]), ("src/Dir", risky.LINKED, [1])])

    def test_the_report_says_what_each_kind_of_finding_means(self):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(risky.report([(b"lakefile.toml", risky.CONFIGURED, 0, [1]), (b"src/Dir", risky.LINKED, 0, [1])],
                                          resume="token"), 1)
        text = out.getvalue()
        lines = text.splitlines()
        self.assertEqual(lines[:2], ["lakefile.toml: a change to what is built", "src/Dir: a link under src/"])
        self.assertIn("decide what is built", text)
        self.assertIn("A link under src/ can point at Lean code", text)
        self.assertNotIn("must not need these constructs", text)
        self.assertEqual(lines[-2:], ["::error file=lakefile.toml,line=1::This pull request changes lakefile.toml, which decides what is built.",
                                      "::error file=src/Dir,line=1::This pull request makes src/Dir a link."])
        with contextlib.redirect_stdout(io.StringIO()) as out:
            risky.report([(b"src/A.lean", "sorry", 0, [2])])
        self.assertIn("must not need these constructs", out.getvalue())
        self.assertNotIn("decide what is built", out.getvalue())

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
