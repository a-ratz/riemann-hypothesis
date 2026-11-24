#!/usr/bin/env python3
"""The search of the text, the list of lines that may stand, and the comparison on a small local repository; no GitHub calls."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "risky-constructs.py"
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
    """Findings as (path, word, line numbers)."""
    return [(path.decode(), name, [number for number, _ in lines]) for path, name, lines in findings]


def scan(text):
    """The words in a text, as {word: line numbers}."""
    return {name: [number for number, _ in lines] for name, lines in risky.scan(text.encode("utf-8")).items()}


class Reading(unittest.TestCase):
    def test_each_word_is_found_with_its_line(self):
        cases = {
            "sorry": "theorem t : False := by\n  sorry\n",
            "stop": "theorem t : False := by\n  stop simp\n",
            "admit": "theorem t : False := by\n  admit\n",
            "admitGoal": "elab \"cheat\" : tactic => do\n  Lean.Elab.admitGoal (← Lean.Elab.Tactic.getMainGoal)\n",
            "apply?": "theorem t : False := by\n  apply?\n",
            "plausible": "theorem t (a b : Nat) : a + b = b + a := by\n  plausible\n",
            "axiom": "\naxiom cheat : False\n",
            "elabAxiom": "elab \"cheat\" : command => do\n  Lean.Elab.Command.elabAxiom {} stx\n",
            "axiomDecl": "elab \"cheat\" : command => do\n  let d := Lean.Declaration.axiomDecl value\n",
            "native": "theorem t : 2 + 2 = 4 := by\n  native_decide\n",
            "bv_decide": "theorem t (x : BitVec 8) : x = x := by\n  bv_decide\n",
            "bv_check": "theorem t (x : BitVec 8) : x = x := by\n  bv_check \"t.lrat\"\n",
            "decide-config": "theorem t : 2 + 2 = 4 := by\n  decide (config := c)\n",
            "implemented_by": "\n@[implemented_by fast] def slow : Nat := 0\n",
            "extern": "\n@[extern \"c_fast\"] def slow : Nat := 0\n",
            "unsafe": "\nunsafe def cast : Nat := 0\n",
            "opaque": "\nopaque hidden : Nat\n",
            "debug": "\nset_option debug.skipKernelTC true\n",
            "addDecl": "run_x do\n  Lean.addDecl decl\n",
            "addAndCompile": "run_x do\n  Lean.addAndCompile decl\n",
            "modifyEnv": "run_x do\n  Lean.modifyEnv fun env => env\n",
            "setEnv": "run_x do\n  Lean.setEnv env\n",
            "run_cmd": "\nrun_cmd pure ()\n",
            "run_elab": "\nrun_elab pure ()\n",
            "run_meta": "\nrun_meta pure ()\n",
            "#eval": "\n#eval 1\n",
            "initialize": "\ninitialize pure ()\n",
        }
        self.assertEqual(list(cases), [name for name, _ in risky.CONSTRUCTS], "one case for each word of the list, in its order")
        for name, text in cases.items():
            with self.subTest(name):
                self.assertEqual(scan(text).get(name), [2])
        # A word is reported under its own name only.
        for name in ("sorry", "stop", "admit", "axiom", "elabAxiom", "axiomDecl", "plausible", "extern", "opaque", "initialize", "#eval"):
            self.assertEqual(list(scan(cases[name])), [name])

    def test_a_word_in_a_comment_or_a_string_is_found_too(self):
        text = "-- no sorry here\n/- we add no axiom\n   and never admit -/\ndef s := \"native_decide\"\n/-- A doc with #eval. -/\n"
        self.assertEqual(scan(text), {"sorry": [1], "axiom": [2], "admit": [3], "native": [4], "#eval": [5]})

    def test_nothing_that_stands_before_a_word_hides_it(self):
        after = "\naxiom cheat : False\n"
        for before in ("/- a comment that never ends", "def s := \"a string that never ends", 'Lean.logInfo "{"', "def b := !'\"'.isAlpha",
                       "def s := s!\"{\"", "«a name that never ends", "-- /-", "\"\\\""):
            with self.subTest(before=before):
                self.assertEqual(scan(before + after), {"axiom": [2]})
        for text in ("def a := x⁻¹axiom cheat : False", "#whereaxiom cheat : False", "def a := 2axiom cheat : False", "Mˣaxiom c : False",
                     "theorem t : False := by (stop simp)", "theorem t : False := by simp;admit", "theorem t : False := by ·stop simp",
                     "theorem t : False := by\n  .stop simp", "exact 0xAnative_decide", "decide +0native", "x αnative := true", "x₁native"):
            with self.subTest(text=text):
                self.assertEqual(len(scan(text)), 1)

    def test_a_word_inside_a_name_is_found(self):
        for text, name in (("Lean.mkSorry", "sorry"), ("sorryAx", "sorry"), ("«sorryAx»", "sorry"), ("set_option warn.sorry false", "sorry"),
                           ("debug.byAsSorry", "sorry"), ("have hstop := h", "stop"), ("rw [hp.stop]", "stop"), ("stop'", "stop"),
                           ("g.admit", "admit"), ("choice_axiom", "axiom"), ("evalNativeDecide", "native"),
                           ("Lean.Parser.Tactic.nativeDecide", "native"), ("decide +native", "native"),
                           ("{ c with native := true }", "native"), ("+«native»", "native"), ("incl_native", "native"),
                           ("Lean.Meta.nativeEqTrue", "native"), ("builtin_initialize", "initialize"), ("unsafeCast", "unsafe"),
                           ("unsafe_x", "unsafe"), ("opaquely", "opaque"), ("debugging", "debug"), (".axiomDecl", "axiomDecl")):
            with self.subTest(text=text):
                self.assertIn(name, scan(text))

    def test_a_longer_name_that_goes_on_after_the_word_is_another_name(self):
        text = ("stopping stops stop_at stop1 isStoppingTime\nadmits admitted admit_x AdmitsLimit\naxioms axiomatic axiomOfChoice\n"
                "external externalProduct\nhint have hint : P\nalternative Alternative coarse_degree_alternative\n"
                "config := { decide := true }\n")
        self.assertEqual(scan(text), {})

    def test_a_decide_with_a_config_and_a_config_in_angle_brackets_are_found(self):
        for text in ("decide (config := c)", "decide -zetaReduce (config := myConfig)", "decide (config := ⟨false, true, true, false⟩)",
                     "simp (config := ⟨⟩)", "omega (config :=⟨1⟩)", "first | decide (config := .mk false true true false) | rfl",
                     "decide (config := (⟨false, true, true, false⟩))"):
            with self.subTest(text=text):
                self.assertEqual(list(scan(text)), ["decide-config"])
        for text in ("decide", "simp (config := { decide := true })", "apply (config := { allowSynthFailures := true }) h", "by decide\n -- config",
                     "def c : DecideConfig := ⟨false, true, true, false⟩", "simp (config := (⟨⟩))"):
            with self.subTest(text=text):
                self.assertEqual(scan(text), {})

    def test_a_line_break_between_decide_and_its_config_hides_it(self):
        # The limit the script names: this is the one pattern of two words.
        self.assertEqual(scan("theorem t : 2 + 2 = 4 := by\n  decide\n    (config := c)\n"), {})

    def test_a_line_is_given_once_with_its_number_and_without_its_blanks(self):
        found = risky.scan("sorry sorry\n\n  Sorry\r\n\tx   sorry \t-- why".encode())
        self.assertEqual(found, {"sorry": [(1, "sorry sorry"), (3, "Sorry"), (4, "x sorry -- why")]})
        self.assertEqual(risky.scan(b"sorry"), {"sorry": [(1, "sorry")]})
        self.assertEqual(risky.scan(b""), {})
        # A config that begins on the next line belongs to the line with the word `config`.
        self.assertEqual(risky.scan("simp (config :=\n  ⟨⟩)".encode()), {"decide-config": [(1, "simp (config :=")]})

    def test_bytes_that_are_no_text_do_not_stop_the_search(self):
        self.assertEqual(scan(b"\xff\xfe\x00 \nsorry\n".decode("utf-8", "replace")), {"sorry": [2]})
        self.assertEqual([number for number, _ in risky.scan(b"\xff\xfe\x00 \nsorry\n")["sorry"]], [2])


class Allowed(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.file = Path(directory.name) / "allowed.txt"

    def read(self, text):
        self.file.write_text(text, encoding="utf-8")
        return risky.allowances(self.file)

    def test_a_line_names_a_file_and_the_line_that_may_stand_in_it(self):
        text = ("# a comment\n\nsrc/A.lean: rw [hp.stop] at this\nsrc/With space/Ω.lean:    -- keeping   the target opaque: yes  \n"
                "src/B.lean: #eval 1\n   \n")
        self.assertEqual(self.read(text), {(b"src/A.lean", "rw [hp.stop] at this"),
                                           ("src/With space/Ω.lean".encode(), "-- keeping the target opaque: yes"),
                                           (b"src/B.lean", "#eval 1")})
        self.assertEqual(self.read(""), set())

    def test_a_line_that_is_not_understood_stops_the_run(self):
        for line in ("src/A.lean", "src/A.lean:", "src/A.lean: ", "src/A.lean:    ", "src/A.lean:sorry", "A.lean: sorry",
                     "scripts/A.lean: sorry", "src/A.txt: sorry", "2 stop src/A.lean", " src/A.lean: sorry", "src/A.lean\tsorry"):
            with self.subTest(line=line):
                with self.assertRaises(RuntimeError) as stopped:
                    self.read("# fine\n" + line + "\n")
                self.assertIn("line 2", str(stopped.exception))

    def test_without_a_file_nothing_may_stand(self):
        self.assertEqual(risky.allowances(self.file), set())

    def test_the_list_in_the_repository_can_be_read(self):
        self.assertEqual(risky.ALLOWED, SCRIPT.with_name("risky-constructs-allowed.txt"))
        self.assertTrue(risky.ALLOWED.exists())
        for path, line in risky.allowances(risky.ALLOWED):
            self.assertTrue(path.startswith(b"src/") and line)


class Comparing(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.repo = Repository(directory.name)

    def added(self, head, **options):
        return names(risky.added(self.repo.root, self.repo.base, head, **options))

    def test_a_clean_change_passes(self):
        head = self.repo.branch("clean", {"src/A.lean": CLEAN + "theorem three : 1 + 2 = 3 := by\n  rfl\n"})
        self.assertEqual(self.added(head), [])

    def test_a_sorry_in_a_changed_file_is_found(self):
        head = self.repo.branch("sorry", {"src/A.lean": "theorem two : 1 + 1 = 2 := by\n  sorry\n"})
        self.assertEqual(risky.added(self.repo.root, self.repo.base, head), [(b"src/A.lean", "sorry", [(2, "sorry")])])

    def test_an_axiom_in_a_new_file_is_found(self):
        head = self.repo.branch("axiom", {"src/Deep/New.lean": "axiom cheat : False\n"})
        self.assertEqual(self.added(head), [("src/Deep/New.lean", "axiom", [1])])

    def test_a_line_that_was_already_there_passes_wherever_it_stands_now(self):
        head = self.repo.branch("same", {"src/Old.lean": "theorem new : True := trivial\n\ntheorem old : True := by\n      sorry\n"})
        self.assertEqual(self.added(head), [])

    def test_one_more_line_with_a_word_is_found_and_the_old_one_is_not_named(self):
        head = self.repo.branch("more", {"src/Old.lean": "theorem old : True := by\n  sorry\n\ntheorem new : True := by\n  sorry\n"})
        self.assertEqual(self.added(head), [("src/Old.lean", "sorry", [5])])
        other = self.repo.branch("other", {"src/Old.lean": "theorem old : True := by\n  sorry\n\ntheorem new : True := by sorry\n"})
        self.assertEqual(self.added(other), [("src/Old.lean", "sorry", [4])])

    def test_a_word_that_moves_from_a_comment_or_a_name_into_the_proof_is_found(self):
        # As many of the word before as after: a count would let these through.
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/Names.lean", "theorem t (h : P) : P := by\n  have hstop := h\n  exact hstop\n")
        self.repo.write("src/Comment.lean", "theorem t : True := by\n  -- by sorry\n  trivial\n")
        self.repo.base = self.repo.commit("with a name and a comment")
        head = self.repo.branch("swapped", {
            "src/Names.lean": "theorem t (h : P) : P := by\n  have hs := h\n  stop exact hs\n  stop simp\n",
            "src/Comment.lean": "theorem t : True := by\n  sorry\n"})
        self.assertEqual(self.added(head), [("src/Comment.lean", "sorry", [2]), ("src/Names.lean", "stop", [3, 4])])

    def test_a_line_that_stays_as_it_is_while_its_comment_is_opened_is_not_seen(self):
        # The limit the script names.
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/Block.lean", "/-\ntheorem t : False := by\n  sorry\n-/\n")
        self.repo.base = self.repo.commit("with a block comment")
        head = self.repo.branch("opened", {"src/Block.lean": "theorem t : False := by\n  sorry\n"})
        self.assertEqual(self.added(head), [])

    def test_a_word_in_a_comment_is_found(self):
        head = self.repo.branch("comment", {"src/A.lean": "/-- We admit no axiom here, sorry. -/\n" + CLEAN})
        self.assertEqual(self.added(head), [("src/A.lean", "sorry", [1]), ("src/A.lean", "admit", [1]), ("src/A.lean", "axiom", [1])])

    def test_the_challenge_other_directories_other_files_and_deleted_files_are_not_read(self):
        head = self.repo.branch("elsewhere", {
            "src/Challenge.lean": "theorem riemannHypothesis : RiemannHypothesis := by sorry\n-- sorry, changed\n",
            "comparator/Extra.lean": "axiom elsewhere : False\n",
            "scripts/tool.py": "sorry = 1\n",
            "src/notes.txt": "sorry\n",
            "srcs/B.lean": "sorry\n"}, delete=("src/Old.lean",))
        self.assertEqual(self.added(head), [])

    def test_a_renamed_file_counts_as_a_new_one(self):
        self.repo.git("checkout", "--quiet", "-b", "renamed", self.repo.base)
        self.repo.git("mv", "src/Old.lean", "src/Moved.lean")
        head = self.repo.commit("renamed")
        self.assertEqual(self.added(head), [("src/Moved.lean", "sorry", [2])])

    def test_a_link_under_src_is_found(self):
        self.repo.git("checkout", "--quiet", "-b", "link", self.repo.base)
        (self.repo.root / "src/A.lean").unlink()
        (self.repo.root / "src/A.lean").symlink_to("../extra/A.lean")   # a file that becomes a link
        (self.repo.root / "src/Dir").symlink_to("../extra")             # a new link to a directory
        (self.repo.root / "docs").mkdir()
        (self.repo.root / "docs/link.lean").symlink_to("../extra/A.lean")  # outside src/: not this check's
        self.repo.write("extra/A.lean", "axiom cheat : False\n")
        head = self.repo.commit("links")
        self.assertEqual(risky.added(self.repo.root, self.repo.base, head), [(b"src/A.lean", "link", []), (b"src/Dir", "link", [])])
        # A link that was one before is not this pull request's, and a link that becomes a file is read as a new file.
        self.repo.base = head
        (self.repo.root / "src/Dir").unlink()
        (self.repo.root / "src/Dir").symlink_to("../elsewhere")
        (self.repo.root / "src/A.lean").unlink()
        self.repo.write("src/A.lean", "theorem t : False := by\n  sorry\n")
        self.assertEqual(self.added(self.repo.commit("no longer a link")), [("src/A.lean", "sorry", [2])])

    def test_a_submodule_under_src_is_found(self):
        self.repo.git("checkout", "--quiet", "-b", "submodule", self.repo.base)
        self.repo.git("update-index", "--add", "--cacheinfo", f"160000,{self.repo.base},src/Vendored")
        self.repo.git("commit", "--quiet", "--message", "a submodule")
        head = self.repo.git("rev-parse", "HEAD")
        self.assertEqual(risky.added(self.repo.root, self.repo.base, head), [(b"src/Vendored", "link", [])])

    def test_the_path_a_link_pointed_at_is_not_the_earlier_text_of_the_file(self):
        self.repo.git("checkout", "--quiet", "main")
        (self.repo.root / "src/Was.lean").symlink_to("sorry")
        self.repo.base = self.repo.commit("with a link whose target is called sorry")
        self.repo.git("checkout", "--quiet", "-b", "file", self.repo.base)
        (self.repo.root / "src/Was.lean").unlink()
        self.repo.write("src/Was.lean", "theorem t : False := by\n  sorry\n")
        self.assertEqual(self.added(self.repo.commit("a file now")), [("src/Was.lean", "sorry", [2])])

    def test_a_line_with_two_words_pairs_off_one_line_and_not_two(self):
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/Two.lean", "theorem t : True := by\n  sorry -- admit\n")
        self.repo.base = self.repo.commit("with a line that holds two words")
        head = self.repo.branch("again", {"src/Two.lean": "theorem t : True := by\n  sorry -- admit\n\nexample : True := by\n  sorry -- admit\n"})
        self.assertEqual(self.added(head), [("src/Two.lean", "sorry", [5]), ("src/Two.lean", "admit", [5])])

    def test_a_path_that_is_not_ascii_is_read(self):
        head = self.repo.branch("odd", {"src/GaloisCohomology₂/Ω.lean": "theorem t : False := by\n  native_decide\n"})
        self.assertEqual(self.added(head), [("src/GaloisCohomology₂/Ω.lean", "native", [2])])

    def test_only_what_the_pull_request_changed_counts(self):
        # main moves on after the pull request branched off; that change is not the pull request's.
        head = self.repo.branch("mine", {"src/A.lean": CLEAN + "-- mine\n"})
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/B.lean", "axiom later : False\n")
        later = self.repo.commit("later on main")
        fork = self.repo.git("merge-base", later, head)
        self.assertEqual(fork, self.repo.base)
        self.assertEqual(names(risky.added(self.repo.root, fork, head)), [])

    def test_a_file_that_cannot_be_read_stops_the_run(self):
        for what, blob in (("no such object", b"1" * 40), ("a commit, as a submodule would give", self.repo.base.encode())):
            with self.subTest(what):
                with self.assertRaises(RuntimeError) as stopped:
                    risky.scan_blobs(self.repo.root, [(b"src/A.lean", blob)], fetch=False)
                self.assertIn("could not read src/A.lean", str(stopped.exception))

    def test_a_line_in_the_list_may_stand_and_no_other(self):
        text = "theorem old : True := by\n  sorry\n\ntheorem new : True := by\n    sorry   -- kept\n\naxiom a : True\n"
        head = self.repo.branch("two", {"src/Old.lean": text, "src/A.lean": CLEAN + "axiom a : True\n"})
        found = [("src/A.lean", "axiom", [3]), ("src/Old.lean", "sorry", [5]), ("src/Old.lean", "axiom", [7])]
        self.assertEqual(self.added(head), found)
        self.assertEqual(self.added(head, allowed={(b"src/Old.lean", "sorry -- kept")}), [found[0], found[2]])
        self.assertEqual(self.added(head, allowed={(b"src/Old.lean", "sorry -- kept"), (b"src/A.lean", "axiom a : True")}), [found[2]])
        # Another line, another file and the line that was there before allow nothing.
        self.assertEqual(self.added(head, allowed={(b"src/Old.lean", "sorry"), (b"src/B.lean", "sorry -- kept"),
                                                   (b"src/Old.lean", "sorry -- kept."), (b"src/Old.lean", "axiom b : True")}), found)

    def test_a_line_in_the_list_is_no_leave_for_the_word(self):
        # The comment may stand. The same word in the proof, in the same file, is another line.
        head = self.repo.branch("budget", {"src/A.lean": "-- no sorry here\ntheorem two : 1 + 1 = 2 := by\n  sorry\n"})
        self.assertEqual(self.added(head, allowed={(b"src/A.lean", "-- no sorry here")}), [("src/A.lean", "sorry", [3])])

    def test_the_report_fails_only_when_something_was_added(self):
        with contextlib.redirect_stdout(io.StringIO()) as clean:
            self.assertEqual(risky.report([], resume="token"), 0)
        self.assertEqual(clean.getvalue().splitlines(), ["No risky construct was added.", "::token::"])
        with contextlib.redirect_stdout(io.StringIO()) as failing:
            self.assertEqual(risky.report([(b"src/A.lean", "sorry", [(2, "sorry"), (9, "exact sorry")])], resume="token"), 1)
        lines = failing.getvalue().splitlines()
        self.assertEqual(lines[:2], ["src/A.lean:2: sorry: sorry", "src/A.lean:9: sorry: exact sorry"])
        self.assertEqual(lines[-2:], ["::token::", "::error file=src/A.lean,line=2::This pull request adds `sorry` to src/A.lean."])
        many = [(number, f"stop {number}") for number in range(1, 8)]
        with contextlib.redirect_stdout(io.StringIO()) as plain:
            self.assertEqual(risky.report([(b"src/B.lean", "stop", many)]), 1)
        lines = plain.getvalue().splitlines()
        self.assertEqual(lines[4:6], ["src/B.lean:5: stop: stop 5", "src/B.lean: stop: and 2 more lines"])
        self.assertNotIn("::", plain.getvalue())

    def test_the_report_gives_the_lines_that_would_let_what_it_found_stand(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        findings = [(b"src/A.lean", "sorry", [(2, "sorry"), (9, "exact sorry: now")]), (b"src/A.lean", "stop", [(9, "exact sorry: now")]),
                    ("src/With space/Ω.lean".encode(), "#eval", [(4, "#eval 1")])]
        with contextlib.redirect_stdout(io.StringIO()) as out:
            risky.report(findings)
        self.assertIn("scripts/risky-constructs-allowed.txt", out.getvalue())
        offered = [line[4:] for line in out.getvalue().splitlines() if line.startswith("    ")]
        self.assertEqual(offered, ["src/A.lean: sorry", "src/A.lean: exact sorry: now", "src/With space/Ω.lean: #eval 1"])
        # What the report offers is what the list understands.
        file = Path(directory.name) / "allowed.txt"
        file.write_text("\n".join(offered) + "\n", encoding="utf-8")
        self.assertEqual(risky.allowances(file), {(path, text) for path, _, lines in findings for _, text in lines})

    def test_the_report_offers_no_more_than_fifty_lines(self):
        findings = [(b"src/A.lean", "sorry", [(number, f"sorry {number}") for number in range(1, 61)])]
        with contextlib.redirect_stdout(io.StringIO()) as out:
            risky.report(findings)
        offered = [line[4:] for line in out.getvalue().splitlines() if line.startswith("    ")]
        self.assertEqual((len(offered), offered[49], offered[50]), (51, "src/A.lean: sorry 50", "and 10 more"))

    def test_a_link_is_reported_as_one_and_no_line_is_offered_for_it(self):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(risky.report([(b"src/Dir", "link", [])], resume="token"), 1)
        text = out.getvalue()
        self.assertEqual(text.splitlines()[0], "src/Dir: a symbolic link or a submodule")
        self.assertIn("A link cannot be allowed", text)
        self.assertNotIn("To let a line stand", text)
        self.assertEqual(text.splitlines()[-1], "::error file=src/Dir,line=1::This pull request makes src/Dir a link.")

    def test_a_file_name_or_a_line_cannot_write_a_workflow_command(self):
        name = "src/a\n::error::made up, 100%##[add-mask]x.lean".encode()
        with contextlib.redirect_stdout(io.StringIO()) as out:
            risky.report([(name, "sorry", [(1, "sorry\x1b[2K\r::warning::made up")])], resume="token")
        lines = out.getvalue().splitlines()
        resumed = lines.index("::token::")
        # While commands are off the name and the line may be printed, but never at the start of a line.
        self.assertEqual(lines[0], "src/a\\x0a::error::made up, 100%##[add-mask]x.lean:1: sorry: sorry\\x1b[2K\\x0d::warning::made up")
        self.assertFalse(any(line.startswith(("::", "##[")) for line in lines[:resumed]))
        # After that there is exactly the annotation, with the name escaped for a property and without the line.
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

    def run_script(self, head, work, *more, base=None):
        return subprocess.run([sys.executable, str(SCRIPT), "--annotate", "--work", str(self.root / work),
                               "--remote", self.repo.root.as_uri(), "--base", base or self.repo.base, "--head", head, *more],
                              capture_output=True, text=True)

    def test_the_pull_request_is_compared_with_the_commit_it_branched_off_from(self):
        # main drops its sorry after the pull request branched off. Against main's tip the pull
        # request would seem to add that sorry; against the commit it branched off from it adds nothing.
        head = self.repo.branch("mine", {"src/A.lean": CLEAN + "-- mine\n"})
        self.repo.git("checkout", "--quiet", "main")
        self.repo.write("src/Old.lean", "theorem old : True := trivial\n")
        later = self.repo.commit("later on main")
        done = self.run_script(head, "moved", base=later)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn(f"branched off at {self.repo.base}, head {head}", done.stdout)

    def test_a_clean_pull_request_passes(self):
        head = self.repo.branch("clean", {"src/A.lean": CLEAN + "theorem three : 1 + 2 = 3 := by\n  rfl\n"})
        done = self.run_script(head, "clean")
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn("No risky construct was added.", done.stdout)

    def test_an_added_word_fails_with_file_and_line(self):
        head = self.repo.branch("axiom", {"src/Deep/New.lean": "/-- A doc. -/\naxiom cheat : False\n",
                                          "src/Old.lean": "theorem old : True := by\n  sorry\n-- touched\n"})
        done = self.run_script(head, "axiom")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        lines = done.stdout.splitlines()
        self.assertRegex(lines[0], r"^::stop-commands::[0-9a-f]{32}$")
        self.assertIn("src/Deep/New.lean:2: axiom: axiom cheat : False", lines)
        token = lines[0].removeprefix("::stop-commands::")
        self.assertEqual(lines[lines.index(f"::{token}::") + 1:],
                         ["::error file=src/Deep/New.lean,line=2::This pull request adds `axiom` to src/Deep/New.lean."])
        self.assertNotIn("src/Old.lean", done.stdout)

    def test_a_link_fails(self):
        self.repo.git("checkout", "--quiet", "-b", "link", self.repo.base)
        (self.repo.root / "src/Linked.lean").symlink_to("../extra/A.lean")
        self.repo.write("extra/A.lean", "axiom cheat : False\n")
        done = self.run_script(self.repo.commit("a link"), "link")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("src/Linked.lean: a symbolic link or a submodule", done.stdout)

    def test_the_list_is_read_and_a_broken_one_stops_the_run(self):
        head = self.repo.branch("axiom", {"src/Deep/New.lean": "axiom chosen : True\n"})
        allowed = self.root / "allowed.txt"
        allowed.write_text("# kept on purpose\nsrc/Deep/New.lean: axiom chosen : True\n")
        done = self.run_script(head, "allowed", "--allowed", str(allowed))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual(self.run_script(head, "not-allowed").returncode, 1)
        allowed.write_text("1 axiom src/Deep/New.lean\n")
        done = self.run_script(head, "broken", "--allowed", str(allowed))
        self.assertEqual(done.returncode, 2)
        self.assertIn("line 1: expected", done.stderr)
        self.assertNotIn("No risky construct was added.", done.stdout)

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

    def test_the_file_as_it_was_is_fetched_only_where_a_word_stands_now(self):
        head = self.repo.branch("both", {"src/A.lean": CLEAN + "-- changed\n",
                                         "src/Old.lean": "theorem old : True := by\n  sorry\n\nexample : True := by sorry\n"})
        done = self.run_script(head, "both")
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("src/Old.lean:4: sorry: example : True := by sorry", done.stdout)
        self.assertNotIn("src/Old.lean:2:", done.stdout)

        def here(path):
            blob = self.repo.git("rev-parse", f"{self.repo.base}:{path}")
            found = subprocess.run(["git", "-C", str(self.root / "both"), "cat-file", "--batch-check"], input=blob + "\n",
                                   capture_output=True, text=True, env={**os.environ, "GIT_NO_LAZY_FETCH": "1"})
            return not found.stdout.strip().endswith("missing")

        self.assertTrue(here("src/Old.lean"), "the earlier text of the file with the word was not fetched")
        self.assertFalse(here("src/A.lean"), "the earlier text of a file without any word was fetched")


if __name__ == "__main__":
    unittest.main()
