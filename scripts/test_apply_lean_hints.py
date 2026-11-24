#!/usr/bin/env python3
"""Reading hints from a log and making the edits in a small directory; nothing is built."""
import collections
import importlib.util
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
import unittest.mock

SCRIPT = Path(__file__).with_name("apply-lean-hints.py")
spec = importlib.util.spec_from_file_location("apply_lean_hints", SCRIPT)
hints = importlib.util.module_from_spec(spec)
spec.loader.exec_module(hints)

S, U = hints.STRUCK, hints.UNDERLINED
HAVEILETI = "linter.style.haveILetI"


def struck(text):
    return "".join(char + S for char in text)


def underlined(text):
    return "".join(char + U for char in text)


def deprecation(file, line, column, old_name, new_name, shown):
    return [f"warning: {file}:{line}:{column}: `{old_name}` has been deprecated: Use `{new_name}` instead",
            "", "Hint: Replace the deprecated name:", f"  {shown}"]


IF_NEG = struck("if_neg") + underlined("ite_eq_right")
HAVEI = ["warning: src/A.lean:3:2: Try this: ", "  haveI" + S, "",
         "The goal is a proposition, so `have` is preferred over `haveI`.", "",
         f"Note: This linter can be disabled with `set_option {HAVEILETI} false`"]


class Reading(unittest.TestCase):
    def test_a_diff_line_gives_the_old_and_the_new_text(self):
        self.assertEqual(hints.diff(IF_NEG), ("if_neg", "ite_eq_right"))
        self.assertEqual(hints.diff("continuous_subtype" + struck("_v") + underlined("V") + "al"),
                         ("continuous_subtype_val", "continuous_subtypeVal"))
        self.assertEqual(hints.diff("haveI" + S), ("haveI", "have"))
        self.assertEqual(hints.diff("Set.mem_" + struck("setOf") + underlined("ofPred") + "_eq"),
                         ("Set.mem_setOf_eq", "Set.mem_ofPred_eq"))

    def test_a_line_without_marks_is_no_diff(self):
        self.assertIsNone(hints.diff("[apply] simp [star_neg, star_one]"))
        self.assertIsNone(hints.diff(""))

    def test_a_mark_with_nothing_before_it_is_no_diff(self):
        self.assertIsNone(hints.diff(S + "x"))
        self.assertIsNone(hints.diff("a" + S + S + "b"))

    def test_a_diff_that_only_inserts_changes_nothing_or_carries_an_unreadable_sign_is_not_used(self):
        self.assertIsNone(hints.diff(underlined("new")))
        self.assertIsNone(hints.diff("a" + S + "a" + U))
        self.assertIsNone(hints.diff("a" + S + "�" + U))

    def test_edits_are_read_with_place_kind_and_name(self):
        log = (["⚠ [7/9] Replayed A"] + deprecation("src/A.lean", 84, 24, "if_neg", "ite_eq_right", IF_NEG)
               + HAVEI + ["✔ [8/9] Built B"])
        found = list(hints.edits(log))
        self.assertEqual([(e.file, e.line, e.column, e.old, e.new, e.kind, e.name) for e in found],
                         [("src/A.lean", 84, 24, "if_neg", "ite_eq_right", "deprecated", "if_neg"),
                          ("src/A.lean", 3, 2, "haveI", "have", HAVEILETI, None)])
        self.assertEqual([e.successor for e in found], ["ite_eq_right", None])

    def test_a_root_prefix_before_the_successor_is_dropped(self):
        # Lean writes `_root_.` before a name that would be ambiguous where it is printed.
        log = ["warning: src/A.lean:9:4: `ContinuousLinearMap.add_apply` has been deprecated: Use `_root_.add_apply` instead",
               "", "Hint: Replace the deprecated name:", "  " + struck("ContinuousLinearMap.") + "add_apply"]
        self.assertEqual([(e.name, e.successor, e.old, e.new) for e in hints.edits(log)],
                         [("ContinuousLinearMap.add_apply", "add_apply", "ContinuousLinearMap.add_apply", "add_apply")])

    def test_a_deprecation_with_a_text_of_its_own_names_no_successor(self):
        self.assertIsNone(hints.DEPRECATED.match("`a` has been deprecated: see the notes")["successor"])
        self.assertIsNone(hints.DEPRECATED.match("`a` has been deprecated: Use `b` or `c` instead")["successor"])
        self.assertEqual(hints.DEPRECATED.match("`a` has been deprecated: Use `b.c'` instead")["successor"], "b.c'")

    def test_try_this_with_the_edit_on_the_same_line_is_read(self):
        log = ["warning: src/A.lean:3:2: Try this: haveI" + S, "",
               f"Note: This linter can be disabled with `set_option {HAVEILETI} false`"]
        self.assertEqual([(e.old, e.new, e.kind) for e in hints.edits(log)], [("haveI", "have", HAVEILETI)])

    def test_a_diff_without_a_linter_note_is_of_the_kind_other(self):
        log = ["warning: src/A.lean:3:2: Try this: ", "  ∀" + struck("ᵉ") + " z"]
        self.assertEqual([(e.old, e.new, e.kind) for e in hints.edits(log)], [("∀ᵉ z", "∀ z", "other")])

    def test_warnings_without_a_diff_give_no_edit(self):
        log = ["warning: src/A.lean:92:26: This simp argument is unused:", "  h", "",
               "Hint: Omit it from the simp argument list.", "  [apply] simp [star_neg, star_one]", "",
               "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`",
               "warning: src/A.lean:9:4: `Module.End.mul_apply` has been deprecated: Use `mul_apply_eq_comp` instead",
               "", "Note: The updated constant has a different type:", "  ∀ x, x = x",
               "warning: src/A.lean:5:11: Variable name `i` is not explicitly referenced.", "",
               "Hint: The binding can be removed (if unused) or named `_` (if used implicitly).", "  [apply] _i"]
        skipped = collections.Counter()
        self.assertEqual(list(hints.edits(log, skipped)), [])
        self.assertEqual(skipped, {})

    def test_a_hint_of_two_lines_or_a_broken_one_is_counted_and_not_applied(self):
        log = ["warning: src/A.lean:1:0: `a` has been deprecated: Use `b` instead", "",
               "Hint: Replace the deprecated name:", "  " + struck("a") + underlined("b"), "  " + struck("c") + underlined("d"),
               "warning: src/A.lean:2:0: `a` has been deprecated: Use `b` instead", "",
               "Hint: Replace the deprecated name:", "  " + S + "a"]
        skipped = collections.Counter()
        self.assertEqual(list(hints.edits(log, skipped)), [])
        self.assertEqual(skipped, {"hint has more than one line": 1, "hint is no usable diff": 1})

    def test_a_hint_that_only_deletes_is_counted_and_not_applied(self):
        log = ["warning: src/A.lean:3:2: Try this: ", "  " + struck("extra"), "",
               "Note: This linter can be disabled with `set_option linter.x false`"]
        skipped = collections.Counter()
        self.assertEqual(list(hints.edits(log, skipped)), [])
        self.assertEqual(skipped, {"hint only deletes": 1})

    def test_the_diff_has_to_follow_its_heading_directly(self):
        log = ["warning: src/A.lean:1:0: `a` has been deprecated: Use `b` instead", "",
               "Hint: Replace the deprecated name:", "", "Some later text " + struck("a") + underlined("b")]
        self.assertEqual(list(hints.edits(log)), [])

    def test_a_line_of_progress_ends_the_warning_before_it(self):
        log = (["warning: src/A.lean:1:0: `a` has been deprecated: Use `b` instead", "", "✔ [8/9] Built B",
                "Hint: Replace the deprecated name:", "  " + struck("a") + underlined("b")])
        self.assertEqual(list(hints.edits(log)), [])

    def test_carriage_returns_in_a_log_are_progress_or_line_ends(self):
        lines = deprecation("src/A.lean", 1, 0, "a_b", "c_d", struck("a_b") + underlined("c_d"))
        overwritten = "progress 1%\rprogress 2%\r" + "\n".join(lines)
        self.assertEqual(len(list(hints.edits(overwritten.split("\n")))), 1)
        windows = [line + "\r\n" for line in lines]
        self.assertEqual([(e.old, e.new) for e in hints.edits(windows)], [("a_b", "c_d")])


class Places(unittest.TestCase):
    """Where the proof of a theorem is."""

    def proof(self, text, marker="HERE"):
        lines = text.split("\n")
        number = next(n for n, line in enumerate(lines, 1) if marker in line)
        bare = hints.plain(text).split("\n")
        starts, flush = hints.commands(bare, lines)
        return hints.in_proof_of_theorem(bare, starts, flush, number, lines[number - 1].index(marker))

    def test_the_proof_starts_after_the_theorems_own_define_sign(self):
        self.assertTrue(self.proof("theorem t : P := by\n  exact HERE\n"))
        self.assertTrue(self.proof("theorem t : P := HERE\n"))
        self.assertTrue(self.proof("private lemma t (h : Q) :\n    P := by\n  simp [HERE]\n"))
        self.assertTrue(self.proof("@[simp] theorem t : P := HERE\n"))
        self.assertTrue(self.proof("@[simp]\nprotected theorem t : P := by\n  exact HERE\n"))
        self.assertFalse(self.proof("theorem t (h : HERE) : P := by\n  rfl\n"))
        self.assertFalse(self.proof("theorem t :\n    HERE := by\n  rfl\n"))

    def test_a_define_sign_inside_a_statement_does_not_start_the_proof(self):
        for text in ("theorem t (h : P) :\n    let x := f a\n    HERE x = 0 := by\n  rfl\n",
                     "theorem t (h : P) :\n    have x := f a\n    HERE x = 0 := by\n  rfl\n",
                     "theorem t (σ : ℝ) -- σ := Re s\n    (h : HERE σ) : P σ := by\n  rfl\n",
                     "theorem t (σ : ℝ) /- σ := Re s -/ (h : HERE σ) : P σ := by\n  rfl\n",
                     'theorem t : s = "a := b" → HERE s := by\n  rfl\n',
                     "theorem t (c : Char) (h : c = ')' ∧ HERE) : P := by\n  rfl\n",
                     "theorem t (h : bar (n := 1) = HERE) : P := by\n  rfl\n",
                     "theorem t (x : Nat := 5) (h : HERE) : P := by\n  rfl\n",
                     "theorem t (s : S) (h : s = { a := 1 }) : HERE := by\n  rfl\n",
                     "theorem t (h : P) :\n    haveI x := f a\n    HERE x = 0 := by\n  rfl\n",
                     "theorem t (h : P) :\n    letI x := f a\n    HERE x = 0 := by\n  rfl\n"):
            with self.subTest(text=text):
                self.assertFalse(self.proof(text))
        self.assertTrue(self.proof("theorem t (h : P) :\n    let x := f a\n    Q x := by\n  exact HERE\n"))
        # A name is a whole word, also when it begins with a Greek letter.
        self.assertTrue(self.proof("theorem t : αlet = βwhere := by\n  exact HERE\n"))

    def test_only_theorems_and_lemmas_have_proofs_here(self):
        for start in ("def d : T :=", "instance : Foo G :=", "abbrev a : T :=", "example : P :=", "noncomputable def d : T :=",
                      "structure S where\n  field : T :=", "variable (h : P) in\nopaque o : T :="):
            with self.subTest(start=start):
                self.assertFalse(self.proof(start + "\n  HERE\n"))

    def test_what_follows_a_where_is_left_alone(self):
        text = "theorem t : ∃ n : ℕ, n = 5 :=\n  ⟨n, FIRST⟩\nwhere\n  n : ℕ := SECOND\n  hn : THIRD n = 5 := rfl\n"
        self.assertTrue(self.proof(text, "FIRST"))
        self.assertFalse(self.proof(text, "SECOND"))
        self.assertFalse(self.proof(text, "THIRD"))
        self.assertFalse(self.proof("theorem t : P := by\n  exact foo\n  where foo : P := HERE\n"))
        self.assertFalse(self.proof("theorem t : IsFoo x where\n  field := HERE\n"))

    def test_a_theorem_proved_by_cases_is_left_alone(self):
        self.assertFalse(self.proof("theorem t : ∀ n, P n\n  | 0 => HERE\n  | n + 1 => foo\n"))
        self.assertFalse(self.proof("theorem t : ∀ n, P n\n  | 0 => by\n    have h := m n\n    exact HERE\n"))
        self.assertFalse(self.proof("theorem t : ∀ n, P n\n  | 0 => by simp\n  | n + 1 => by\n    obtain ⟨a, b⟩ := m n\n    exact HERE\n"))
        # A line of the statement that begins with an absolute value is no alternative,
        # and a `match` inside a proof is proof.
        self.assertTrue(self.proof("theorem t (x : ℝ) :\n    |x| ≤ |x| + 1 := by\n  exact HERE\n"))
        self.assertTrue(self.proof("theorem t :\n    Continuous fun x => f x := by\n  exact HERE\n"))
        self.assertTrue(self.proof("theorem t : P := by\n  match n with\n  | 0 => exact HERE\n"))
        self.assertTrue(self.proof("theorem t : P := by\n  induction n with\n  | zero => exact HERE\n"))

    def test_the_next_command_ends_the_theorem(self):
        for after in ("variable (h : HERE)", "deriving instance HERE for Bar", "#check HERE", "open Foo in\ndef d := HERE",
                      "termination_by HERE", "decreasing_by HERE", "attribute [simp] HERE", "end HERE"):
            with self.subTest(after=after):
                self.assertFalse(self.proof("theorem t : P := by\n  rfl\n" + after + "\n"))
        self.assertTrue(self.proof("theorem t : P := by\n  rfl\n\ntheorem u : P := by\n  exact HERE\n"))

    def test_a_declaration_starts_a_command_behind_a_comment_and_when_indented(self):
        for text in ("theorem t : P := by\n  rfl\n/-- Doc. -/ def d : T :=\n  HERE\n",
                     "theorem t : P := by\n  rfl\n/-- Doc. -/ theorem u (h : HERE) : Q := by\n  rfl\n",
                     "theorem t : P := by\n  rfl\n/- a note\n-/ instance : Foo := ⟨HERE⟩\n",
                     "theorem t : P := by\n  rfl\n/- a note\nthat ends here -/ def d : T := HERE\n",
                     "theorem t : P := by\n  rfl\n/- a note -/ variable (h : HERE)\n",
                     "theorem t : P := by\n  rfl\n/- a note\n-/ #check HERE\n",
                     "theorem t : P := by\n  rfl\n  def d : T :=\n    HERE\n",
                     "theorem t : P := by\n  rfl\n  @[simp] private def d : T :=\n    HERE\n",
                     "theorem t : P := by\n  rfl\n  /-- Doc. -/ instance : Foo := ⟨HERE⟩\n",
                     "namespace N\n  theorem t (h : HERE) : P := by\n    rfl\n"):
            with self.subTest(text=text):
                self.assertFalse(self.proof(text))
        self.assertTrue(self.proof("theorem t : P := by\n  rfl\n/-- Doc. -/ theorem u : Q := by\n  exact HERE\n"))
        for keyword in ("theorem", "lemma", "def", "instance", "abbrev", "structure", "class", "inductive", "example",
                        "axiom", "opaque"):
            with self.subTest(keyword=keyword):
                self.assertFalse(self.proof(f"theorem t : P := by\n  rfl\n  {keyword} d : T := HERE\n"))

    def test_an_indented_theorem_is_left_alone(self):
        # Where it ends cannot be told by layout: what follows it may be another command.
        self.assertFalse(self.proof("namespace N\n  theorem t : P := by\n    exact HERE\n"))
        for after in ("variable (h : HERE)", "alias u := HERE", 'notation "x" => HERE', "irreducible_def d : T := HERE",
                      "open X in theorem u (h : HERE) : Q := by"):
            with self.subTest(after=after):
                self.assertFalse(self.proof("namespace N\n  theorem t : P := by\n    rfl\n  " + after + "\n"))
        # Words that only begin like a keyword start nothing.
        self.assertTrue(self.proof("theorem t : P := by\n  classical\n  inferInstance\n  exact HERE\n"))

    def test_words_in_a_comment_start_no_command(self):
        text = "theorem t : P := by\n  first\n/- a note\ndef in column 0 := x\n-/\n  exact HERE\n"
        self.assertTrue(self.proof(text))
        self.assertTrue(self.proof("theorem t : P := by\n  simp\n-- def d := x\n  exact HERE\n"))

    def test_an_unmatched_bracket_does_not_hide_the_proof_for_good(self):
        self.assertTrue(self.proof("theorem t (h : P)) : Q := by\n  exact HERE\n"))


class Blanking(unittest.TestCase):
    """What `plain` takes out of a text."""

    def left(self, text):
        blanked = hints.plain(text)
        self.assertEqual(len(blanked), len(text))
        self.assertEqual([at for at, char in enumerate(blanked) if char == "\n"], [at for at, char in enumerate(text) if char == "\n"])
        return blanked.split()

    def test_comments_are_blanked_and_every_character_keeps_its_place(self):
        self.assertEqual(hints.plain("a -- b := c\nd"), "a          \nd")
        self.assertEqual(self.left("x /- a\n/- b -/ := c -/ y"), ["x", "y"])
        self.assertEqual(self.left("x /--/ := c -/ y"), ["x", "y"])
        self.assertEqual(self.left('x -- say "hi\ny := z'), ["x", "y", ":=", "z"])
        self.assertEqual(self.left("x /- open to the end := y"), ["x"])

    def test_strings_and_character_literals_are_blanked(self):
        self.assertEqual(self.left('s = "a -- b /- c \\" := d" ∧ t'), ["s", "=", "∧", "t"])
        self.assertEqual(self.left("c = ')' ∧ d = '\\'' ∧ e = '\"' ∧ f = '\\x41' ∧ g"),
                         ["c", "=", "∧", "d", "=", "∧", "e", "=", "∧", "f", "=", "∧", "g"])

    def test_the_prime_of_a_name_opens_nothing(self):
        for text in ("exact a'b' c", "h' := f'' x' -- c", "f '' s ∩ t⁻¹' u", "(g x)' y := z'"):
            with self.subTest(text=text):
                self.assertEqual(hints.plain(text).rstrip(), text.split(" --")[0])


class Applying(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name) / "root"
        (self.root / "src").mkdir(parents=True)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode("utf-8"))

    def read(self, name):
        return (self.root / name).read_bytes().decode("utf-8")

    def edit(self, line, column, old, new, kind="deprecated", file="src/A.lean", name="a_theorem"):
        """An edit; a deprecation is of a name that reads like a theorem unless `name` says otherwise."""
        if kind != "deprecated":
            return hints.Edit(file, line, column, old, new, kind)
        return hints.Edit(file, line, column, old, new, kind, name, "its.successor")

    @staticmethod
    def told(**kinds):
        """What the kind check would say: name="kind" or name="kind/arguments"; dots in names are written `__`."""
        lines = []
        for name, word in kinds.items():
            kind, _, arguments = word.partition("/")
            lines.append(f"KIND\t{name.replace('__', '.')}\t{kind}\tits.successor\t{arguments or 'same'}")
        return hints.read_kinds(lines)

    def place(self, text, old, new, occurrence=1, kind="deprecated", name="a_theorem"):
        """An edit of the `occurrence`-th `old` in `text`."""
        seen = 0
        for number, line in enumerate(text.split("\n"), 1):
            column = -1
            while True:
                column = line.find(old, column + 1)
                if column < 0:
                    break
                seen += 1
                if seen == occurrence:
                    return self.edit(number, column, old, new, kind=kind, name=name)
        raise AssertionError(f"{old!r} occurs fewer than {occurrence} times")

    def run_on(self, text, offered, **options):
        self.write("src/A.lean", text)
        outcome, changed, made = hints.apply(self.root, offered, **options)
        return {kind: dict(+counts) for kind, counts in outcome.items()}, changed, made

    def test_an_edit_is_made_where_the_log_says(self):
        text = "theorem t : x := by\n  rw [if_neg h]\n"
        outcome, changed, made = self.run_on(text, [self.place(text, "if_neg", "ite_eq_right")])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  rw [ite_eq_right h]\n")
        self.assertEqual((outcome, changed, len(made)), ({"deprecated": {"made": 1}}, ["src/A.lean"], 1))

    def test_several_edits_on_one_line_are_all_made(self):
        text = "theorem t : x := by\n  simp [if_pos h, if_neg k, if_pos l]\n"
        offered = [self.place(text, "if_pos", "ite_eq_left"), self.place(text, "if_neg", "ite_eq_right"),
                   self.place(text, "if_pos", "ite_eq_left", 2)]
        self.run_on(text, offered)
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  simp [ite_eq_left h, ite_eq_right k, ite_eq_left l]\n")

    def test_columns_count_characters_not_bytes_or_utf16_units(self):
        text = "theorem t : x := by\n  have hκ : 𝕜 ≤ β := haveI := x; if_neg h\n"
        self.assertEqual(text.split("\n")[1].index("if_neg"), 33)
        offered = [self.edit(2, 33, "if_neg", "ite_eq_right"), self.edit(2, 21, "haveI", "have", kind=HAVEILETI)]
        self.run_on(text, offered)
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  have hκ : 𝕜 ≤ β := have := x; ite_eq_right h\n")

    def test_an_edit_whose_text_is_not_there_is_skipped(self):
        text = "theorem t : x := by\n  rw [if_neg h]\n"
        outcome, changed, _ = self.run_on(text, [self.edit(2, 7, "if_neg", "ite_eq_right"), self.edit(9, 0, "if_neg", "ite_eq_right"),
                                                 self.edit(2, 12, "if_neg", "ite_eq_right")])
        self.assertEqual(self.read("src/A.lean"), text)
        self.assertEqual((outcome, changed), ({"deprecated": {"text is not there": 3}}, []))

    def test_the_same_edit_reported_twice_is_made_once(self):
        text = "theorem t : x := by\n  rw [if_neg h]\n"
        outcome, _, _ = self.run_on(text, [self.edit(2, 6, "if_neg", "ite_eq_right"),
                                           self.edit(2, 6, "if_neg", "ite_eq_right", file="./src/A.lean")])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  rw [ite_eq_right h]\n")
        self.assertEqual(outcome, {"deprecated": {"made": 1, "reported twice": 1}})

    def test_overlapping_edits_do_not_corrupt_the_line_in_any_run(self):
        cases = (("theorem t : x := by\n  aaaa\n", [(4, "aa", "a"), (3, "aa", "b")], "theorem t : x := by\n  aba\n"),
                 ("theorem t : x := by\n  exact Foo.bar h\n", [(8, "Foo.bar", "Foo.baz"), (12, "bar", "qux")],
                  "theorem t : x := by\n  exact Foo.baz h\n"),
                 ("theorem t : x := by\n  exact Foo.bar h\n", [(8, "Foo", "Goo"), (8, "Foo.bar", "Foo.baz")],
                  "theorem t : x := by\n  exact Foo.baz h\n"))
        for text, places, expected in cases:
            with self.subTest(text=text):
                offered = [self.edit(2, column, old, new) for column, old, new in places]
                outcome, _, _ = self.run_on(text, offered)
                self.assertEqual(self.read("src/A.lean"), expected)
                self.assertEqual(outcome, {"deprecated": {"made": 1, "overlaps another edit": 1}})
                for _ in range(2):
                    outcome, changed, _ = hints.apply(self.root, offered)
                    self.assertEqual(self.read("src/A.lean"), expected)
                    self.assertEqual(({k: dict(+v) for k, v in outcome.items()}, changed),
                                     ({"deprecated": {"made already": 1, "overlaps another edit": 1}}, []))

    def test_a_second_run_with_the_same_log_changes_nothing(self):
        text = "theorem t : x := by\n  haveI := foo h\n  exact foo_bar\n"
        offered = [self.place(text, "haveI", "have", kind=HAVEILETI), self.place(text, "foo", "foo_bar")]
        self.run_on(text, offered)
        once = self.read("src/A.lean")
        self.assertEqual(once, "theorem t : x := by\n  have := foo_bar h\n  exact foo_bar\n")
        outcome, changed, made = hints.apply(self.root, offered)
        self.assertEqual(self.read("src/A.lean"), once)
        self.assertEqual(({k: dict(+v) for k, v in outcome.items()}, changed, made),
                         ({"deprecated": {"made already": 1}, HAVEILETI: {"made already": 1}}, [], []))

    def test_a_run_by_kind_and_then_a_full_run_give_the_same_file(self):
        text = "theorem t : x := by\n  haveI := foo h; haveI := if_neg k\n"
        have = [self.place(text, "haveI", "have", kind=HAVEILETI), self.place(text, "haveI", "have", 2, kind=HAVEILETI)]
        names = [self.place(text, "foo", "foo_bar"), self.place(text, "if_neg", "ite_eq_right")]
        self.run_on(text, names + have)
        whole = self.read("src/A.lean")
        self.assertEqual(whole, "theorem t : x := by\n  have := foo_bar h; have := ite_eq_right k\n")
        self.run_on(text, have)
        outcome, _, _ = hints.apply(self.root, names + have)
        self.assertEqual(self.read("src/A.lean"), whole)
        self.assertEqual({k: dict(+v) for k, v in outcome.items()}, {"deprecated": {"made": 2}, HAVEILETI: {"made already": 2}})

    def test_only_the_proof_of_a_theorem_is_edited(self):
        text = ("theorem t (h : A.one f = g) :\n    A.two G := by\n  rw [A.three h]\n\n"
                "def d : A.four G :=\n  A.five\n\n"
                "theorem u : P :=\n  A.six\nwhere\n  n : ℕ := A.seven\n")
        offered = [self.place(text, f"A.{word}", "B") for word in ("one", "two", "three", "four", "five", "six", "seven")]
        outcome, _, made = self.run_on(text, offered)
        self.assertEqual(self.read("src/A.lean"), text.replace("A.three", "B").replace("A.six", "B"))
        self.assertEqual(outcome, {"deprecated": {"made": 2, "outside the proof of a theorem, left alone": 5}})
        self.assertEqual(sorted(edit.old for edit in made), ["A.six", "A.three"])
        outcome, _, _ = self.run_on(text, offered, everywhere=True)
        self.assertEqual(outcome, {"deprecated": {"made": 7}})
        self.assertNotIn("A.", self.read("src/A.lean"))

    def test_a_deprecated_definition_is_left_alone(self):
        text = "theorem t : x := by\n  rw [Pi.monoidHom, if_neg h, Measurable.enorm]\n"
        offered = [self.place(text, "Pi.monoidHom", "MonoidHom.pi", name="Pi.monoidHom"),
                   self.place(text, "if_neg", "ite_eq_right", name="if_neg"),
                   self.place(text, "Measurable.enorm", "Measurable.enorm'", name="Measurable.enorm"),
                   self.place(text, "Pi.monoidHom", "MonoidHom.pi", name="Pi.monoidHom")]
        outcome, _, _ = self.run_on(text, offered)
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  rw [Pi.monoidHom, ite_eq_right h, Measurable.enorm]\n")
        self.assertEqual(outcome, {"deprecated": {"made": 1, "does not read like a theorem": 2, "reported twice": 1}})
        # With Lean's word, the theorem without an underscore is replaced too, and nothing else.
        told = self.told(Pi__monoidHom="definition", if_neg="theorem", Measurable__enorm="theorem")
        outcome, _, _ = self.run_on(text, offered, kinds=told)
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  rw [Pi.monoidHom, ite_eq_right h, Measurable.enorm']\n")
        self.assertEqual(outcome, {"deprecated": {"made": 2, "not a theorem": 1, "reported twice": 1}})
        # A name Lean was not asked about is not replaced, and neither is one it does not know.
        outcome, _, _ = self.run_on(text, offered, kinds=self.told(if_neg="theorem"))
        self.assertEqual(outcome, {"deprecated": {"made": 1, "not in the kinds file": 2, "reported twice": 1}})
        outcome, _, _ = self.run_on(text, offered, kinds=self.told(if_neg="theorem", Pi__monoidHom="missing"))
        self.assertEqual(outcome, {"deprecated": {"made": 1, "not a constant the kind check found": 1,
                                                  "not in the kinds file": 1, "reported twice": 1}})
        # The answer belongs to the pair: for another successor of the same name it does not count.
        other = hints.read_kinds(["KIND\tif_neg\ttheorem\tsome.other.successor\tsame"])
        outcome, _, _ = self.run_on(text, offered, kinds=other)
        self.assertEqual(outcome, {"deprecated": {"not in the kinds file": 3, "reported twice": 1}})
        outcome, _, _ = self.run_on(text, offered, definitions=True)
        self.assertEqual(outcome, {"deprecated": {"made": 3, "reported twice": 1}})
        outcome, _, _ = self.run_on(text, offered, definitions=True, kinds=told)
        self.assertEqual(outcome, {"deprecated": {"made": 3, "reported twice": 1}})

    def test_a_name_whose_successor_is_said_to_take_other_arguments_is_left_alone(self):
        text = "theorem t : x := by\n  exact le_trans (Nat.add_div_le_add_div _ _ _) (foo_bar h) (if_neg k) Pi.algHom\n"
        offered = [self.place(text, "Nat.add_div_le_add_div", "Nat.div_add_div_le_add_div", name="Nat.add_div_le_add_div"),
                   self.place(text, "foo_bar", "foo_baz", name="foo_bar"), self.place(text, "if_neg", "ite_eq_right", name="if_neg"),
                   self.place(text, "Pi.algHom", "AlgHom.pi", name="Pi.algHom")]
        told = self.told(Nat__add_div_le_add_div="theorem/other", if_neg="theorem", foo_bar="theorem/unknown",
                         Pi__algHom="definition/other")
        outcome, _, _ = self.run_on(text, offered, kinds=told)
        self.assertEqual(self.read("src/A.lean"), text.replace("if_neg", "ite_eq_right"))
        self.assertEqual(outcome, {"deprecated": {"made": 1, "its successor takes its arguments differently": 1,
                                                  "its successor is not a constant the kind check found": 1, "not a theorem": 1}})
        # Asking for definitions as well does not switch this off.
        outcome, _, _ = self.run_on(text, offered, kinds=told, definitions=True)
        self.assertEqual(self.read("src/A.lean"), text.replace("if_neg", "ite_eq_right"))
        self.assertEqual(outcome, {"deprecated": {"made": 1, "its successor takes its arguments differently": 2,
                                                  "its successor is not a constant the kind check found": 1}})

    def test_lines_of_the_kind_check_are_read_in_their_present_form_only(self):
        told = hints.read_kinds(["KIND\tif_neg\ttheorem\tite_eq_right\tsame\r\n", "KIND\tPi.algHom\tdefinition\tAlgHom.pi\tother",
                                 "KIND\tif_pos\ttheorem", "KIND\tfoo\ttheorem\tbar\tperhaps", "noise"])
        self.assertEqual(told, {("if_neg", "ite_eq_right"): ("theorem", "same"), ("Pi.algHom", "AlgHom.pi"): ("definition", "other")})

    def test_line_endings_and_the_end_of_the_file_stay_byte_for_byte(self):
        text = "theorem t : x := by\r\n  rw [if_neg h]\r\n  done"
        self.run_on(text, [self.edit(2, 6, "if_neg", "ite_eq_right")])
        self.assertEqual((self.root / "src/A.lean").read_bytes(), b"theorem t : x := by\r\n  rw [ite_eq_right h]\r\n  done")

    def test_only_files_of_the_tree_are_written(self):
        proof = "theorem t : x := by\n  rw [if_neg h]\n"
        outside = self.root.parent / "outside.lean"
        outside.write_text(proof, encoding="utf-8")
        self.write(".lake/packages/dep/Dep.lean", proof)
        self.write("src/Real/B.lean", proof)
        self.write("srcx/A.lean", proof)
        (self.root / "src" / "link.lean").symlink_to(outside)
        (self.root / "src" / "dir").symlink_to(self.root.parent)
        (self.root / "src" / "Alias").symlink_to(self.root / "src" / "Real")
        (self.root / "src" / "Folder.lean").mkdir()
        files = ("../outside.lean", str(outside), "src/link.lean", "src/dir/outside.lean", "src/Alias/B.lean",
                 ".lake/packages/dep/Dep.lean", "src/Folder.lean", "src/Missing.lean", "srcx/A.lean", "src/A.lean")
        offered = [self.edit(2, 6, "if_neg", "ite_eq_right", file=file) for file in files]
        outcome, changed, _ = self.run_on(proof, offered)
        self.assertEqual(outside.read_text(encoding="utf-8"), proof)
        self.assertEqual(self.read(".lake/packages/dep/Dep.lean"), proof)
        self.assertEqual(self.read("src/Real/B.lean"), proof)
        self.assertEqual(self.read("srcx/A.lean"), proof)
        self.assertEqual((outcome, changed), ({"deprecated": {"file is not one to write": 9, "made": 1}}, ["src/A.lean"]))

    @unittest.skipIf(os.geteuid() == 0, "root can write anywhere")
    def test_a_file_that_cannot_be_written_is_counted_and_the_run_goes_on(self):
        proof = "theorem t : x := by\n  rw [if_neg h]\n"
        self.write("src/0/Locked.lean", proof)
        self.write("src/1/ReadOnly.lean", proof)
        (self.root / "src/0").chmod(0o555)  # nothing can be put beside the file
        self.addCleanup((self.root / "src/0").chmod, 0o755)
        (self.root / "src/1/ReadOnly.lean").chmod(0o444)
        offered = [self.edit(2, 6, "if_neg", "ite_eq_right", file=file)
                   for file in ("src/0/Locked.lean", "src/1/ReadOnly.lean", "src/A.lean")]
        outcome, changed, made = self.run_on(proof, offered)
        self.assertEqual((outcome, changed, len(made)),
                         ({"deprecated": {"file could not be written": 2, "made": 1}}, ["src/A.lean"], 1))
        self.assertEqual((self.read("src/0/Locked.lean"), self.read("src/1/ReadOnly.lean")), (proof, proof))
        self.assertEqual([path.name for path in (self.root / "src/1").iterdir()], ["ReadOnly.lean"])

    def test_a_failure_while_replacing_leaves_the_file_and_nothing_else(self):
        proof = "theorem t : x := by\n  rw [if_neg h]\n"
        self.write("src/A.lean", proof)
        with unittest.mock.patch.object(hints.os, "replace", side_effect=OSError("no")):
            outcome, changed, made = hints.apply(self.root, [self.edit(2, 6, "if_neg", "ite_eq_right")])
        self.assertEqual(({kind: dict(+counts) for kind, counts in outcome.items()}, changed, made),
                         ({"deprecated": {"file could not be written": 1}}, [], []))
        with unittest.mock.patch.object(hints.os, "replace", side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                hints.apply(self.root, [self.edit(2, 6, "if_neg", "ite_eq_right")])
        self.assertEqual(self.read("src/A.lean"), proof)
        self.assertEqual([path.name for path in (self.root / "src").iterdir()], ["A.lean"])

    def test_a_place_taken_by_an_edit_of_an_earlier_run_is_not_edited_again(self):
        was = "theorem t : x := by\n  exact foo h\n"
        now = "theorem t : x := by\n  exact foo_bar h\n"
        known, wanted = self.place(was, "foo", "foo_bar"), self.place(was, "foo", "qux")
        outcome, changed, _ = self.run_on(now, [wanted], others=[known])
        self.assertEqual(self.read("src/A.lean"), now)
        self.assertEqual((outcome, changed), ({"deprecated": {"overlaps another edit": 1}}, []))
        # While the known edit is not made, it stands in nobody's way and is not counted.
        outcome, _, _ = self.run_on(was, [wanted], others=[known])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  exact qux h\n")
        self.assertEqual(outcome, {"deprecated": {"made": 1}})

    def test_a_written_file_keeps_its_mode_and_no_other_file_is_left(self):
        self.write("src/A.lean", "theorem t : x := by\n  rw [if_neg h]\n")
        (self.root / "src/A.lean").chmod(0o640)
        hints.apply(self.root, [self.edit(2, 6, "if_neg", "ite_eq_right")])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  rw [ite_eq_right h]\n")
        self.assertEqual(stat.S_IMODE((self.root / "src/A.lean").stat().st_mode), 0o640)
        self.assertEqual([path.name for path in (self.root / "src").iterdir()], ["A.lean"])

    def test_the_place_is_judged_where_the_text_stands_now(self):
        # The first name is replaced already, so the second has moved left, in front of the `:=`.
        was = "theorem t : Foo.very_long_old_name a ∧ o_b c := by simp\n"
        now = "theorem t : Foo.n a ∧ o_b c := by simp\n"
        offered = [self.place(was, "Foo.very_long_old_name", "Foo.n"), self.place(was, "o_b", "p_q")]
        outcome, changed, _ = self.run_on(now, offered)
        self.assertEqual(self.read("src/A.lean"), now)
        self.assertEqual((outcome, changed),
                         ({"deprecated": {"made already": 1, "outside the proof of a theorem, left alone": 1}}, []))
        # The other way: a longer name in the statement has pushed a place of the proof to the right.
        was = "theorem t (h : if_neg a) : P := if_neg h\n"
        now = "theorem t (h : ite_eq_right a) : P := if_neg h\n"
        offered = [self.place(was, "if_neg", "ite_eq_right"), self.place(was, "if_neg", "ite_eq_right", 2)]
        outcome, _, _ = self.run_on(now, offered)
        self.assertEqual(self.read("src/A.lean"), "theorem t (h : ite_eq_right a) : P := ite_eq_right h\n")
        self.assertEqual(outcome, {"deprecated": {"made": 1, "made already": 1}})

    def test_a_narrower_second_run_still_finds_its_places(self):
        text = "theorem t : x := by\n  haveI := foo_a h; exact if_neg k\n"
        have = self.place(text, "haveI", "have", kind=HAVEILETI)
        name = self.place(text, "if_neg", "ite_eq_right")
        # An edit that is only known, not asked for, is not made.
        outcome, _, _ = self.run_on(text, [name], others=[have])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  haveI := foo_a h; exact ite_eq_right k\n")
        self.assertEqual(outcome, {"deprecated": {"made": 1}})
        # After the other kind was made, its line is shorter, and the name is found all the same.
        self.run_on(text, [have])
        outcome, _, _ = hints.apply(self.root, [name], others=[have])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  have := foo_a h; exact ite_eq_right k\n")
        self.assertEqual({kind: dict(+counts) for kind, counts in outcome.items()}, {"deprecated": {"made": 1}})
        outcome, changed, _ = hints.apply(self.root, [name], others=[have])
        self.assertEqual(({kind: dict(+counts) for kind, counts in outcome.items()}, changed), ({"deprecated": {"made already": 1}}, []))

    def test_an_edit_that_only_deletes_is_never_taken_for_made(self):
        text = "theorem t : x := by\n  exact foo extra\n"
        outcome, _, _ = self.run_on(text, [self.edit(2, 30, "extra", "", kind="linter.x")])
        self.assertEqual(outcome, {"linter.x": {"text is not there": 1}})
        outcome, _, _ = self.run_on(text, [self.place(text, " extra", "", kind="linter.x")])
        self.assertEqual(self.read("src/A.lean"), "theorem t : x := by\n  exact foo\n")
        self.assertEqual(outcome, {"linter.x": {"made": 1}})

    def test_a_dry_run_changes_nothing(self):
        text = "theorem t : x := by\n  rw [if_neg h]\n"
        outcome, changed, _ = self.run_on(text, [self.edit(2, 6, "if_neg", "ite_eq_right")], write=False)
        self.assertEqual(self.read("src/A.lean"), text)
        self.assertEqual((outcome, changed), ({"deprecated": {"made": 1}}, ["src/A.lean"]))


class Running(unittest.TestCase):
    """The script as a command: from the text of a log to the changed file."""

    SOURCE = "theorem t (h : if_neg = 1) : x := by\n  haveI := y\n  rw [if_neg h]\n  exact ∀ᵉ z\n"

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        (self.root / "src").mkdir()
        (self.root / "src/A.lean").write_text(self.SOURCE, encoding="utf-8")
        log = (["⚠ [1/2] Built A"] + deprecation("src/A.lean", 3, 6, "if_neg", "ite_eq_right", IF_NEG)
               + deprecation("src/A.lean", 1, 15, "if_neg", "ite_eq_right", IF_NEG)
               + ["warning: src/A.lean:2:2: Try this: ", "  haveI" + S, "",
                  f"Note: This linter can be disabled with `set_option {HAVEILETI} false`",
                  "warning: src/A.lean:4:8: Try this: ", "  ∀" + struck("ᵉ") + " z", "",
                  "Note: This linter can be disabled with `set_option linter.other false`"])
        self.log = "\n".join(log) + "\n"
        (self.root / "build.log").write_text(self.log, encoding="utf-8")

    def run_script(self, *args, log=None, stdin=None):
        return subprocess.run([sys.executable, str(SCRIPT), log or str(self.root / "build.log"), "--root", str(self.root), *args],
                              capture_output=True, input=stdin)

    def source(self):
        return (self.root / "src/A.lean").read_text(encoding="utf-8")

    def test_the_two_known_kinds_are_applied_in_proofs_and_the_rest_is_named(self):
        done = self.run_script("--table")
        out = done.stdout.decode()
        self.assertEqual(done.returncode, 0, out + done.stderr.decode())
        self.assertEqual(self.source(), "theorem t (h : if_neg = 1) : x := by\n  have := y\n  rw [ite_eq_right h]\n  exact ∀ᵉ z\n")
        self.assertIn("deprecated: 1 edits (1 outside the proof of a theorem, left alone)", out)
        self.assertIn(f"{HAVEILETI}: 1 edits", out)
        self.assertIn("not used: 1 kind not asked for: linter.other", out)
        self.assertIn("      1  if_neg -> ite_eq_right  [deprecated]", out)
        self.assertIn("1 files changed", out)
        again = self.run_script()
        self.assertEqual(again.returncode, 0)
        self.assertIn("deprecated: 0 edits (1 made already; 1 outside the proof of a theorem, left alone)", again.stdout.decode())
        self.assertIn("0 files changed", again.stdout.decode())

    def test_a_dry_run_only_counts(self):
        dry = self.run_script("--dry-run")
        self.assertIn("1 files would change", dry.stdout.decode())
        self.assertEqual(self.source(), self.SOURCE)

    def test_kind_selects_other_hints(self):
        self.run_script("--kind", "linter.other")
        self.assertEqual(self.source(), self.SOURCE.replace("∀ᵉ z", "∀ z"))

    def test_name_narrows_the_deprecated_names_only(self):
        self.run_script("--name", "some_other_name")
        self.assertEqual(self.source(), self.SOURCE.replace("haveI", "have"))

    def test_everywhere_also_edits_the_statement(self):
        self.run_script("--everywhere")
        self.assertEqual(self.source(), "theorem t (h : ite_eq_right = 1) : x := by\n  have := y\n  rw [ite_eq_right h]\n  exact ∀ᵉ z\n")

    def test_within_names_the_directory_that_may_be_written(self):
        done = self.run_script("--within", "other")
        self.assertEqual(done.returncode, 1)
        self.assertIn("file is not one to write", done.stdout.decode())
        self.assertIn("not ones to write", done.stderr.decode())
        self.assertEqual(self.source(), self.SOURCE)

    def test_a_log_from_standard_input_with_windows_line_ends_is_read(self):
        done = self.run_script(log="-", stdin=self.log.replace("\n", "\r\n").encode() + b"\xff\n")
        self.assertEqual(done.returncode, 0, done.stderr.decode())
        self.assertIn("rw [ite_eq_right h]", self.source())

    def test_the_kind_check_names_every_deprecated_name_and_its_output_is_read_back(self):
        check = self.root / "Kinds.lean"
        done = self.run_script("--write-kind-check", str(check))
        self.assertEqual(done.returncode, 0, done.stderr.decode())
        self.assertIn('("if_neg", "ite_eq_right")]', check.read_text(encoding="utf-8"))
        self.assertIn("import Mathlib", check.read_text(encoding="utf-8"))
        self.assertEqual(self.source(), self.SOURCE)
        (self.root / "kinds.txt").write_text("KIND\tif_neg\tdefinition\tite_eq_right\tsame\n", encoding="utf-8")
        done = self.run_script("--kinds", str(self.root / "kinds.txt"))
        self.assertIn("deprecated: 0 edits (2 not a theorem)", done.stdout.decode())
        self.assertEqual(self.source(), self.SOURCE.replace("haveI", "have"))

    def test_a_narrower_second_run_reads_the_whole_log_for_the_places(self):
        line = "  haveI := y; rw [if_neg h]"
        (self.root / "src/B.lean").write_text("theorem t : x := by\n" + line + "\n", encoding="utf-8")
        log = (deprecation("src/B.lean", 2, line.index("if_neg"), "if_neg", "ite_eq_right", IF_NEG)
               + ["warning: src/B.lean:2:2: Try this: ", "  haveI" + S, "",
                  f"Note: This linter can be disabled with `set_option {HAVEILETI} false`"])
        (self.root / "b.log").write_text("\n".join(log) + "\n", encoding="utf-8")
        self.assertEqual(self.run_script(log=str(self.root / "b.log")).returncode, 0)
        after = (self.root / "src/B.lean").read_text(encoding="utf-8")
        self.assertEqual(after, "theorem t : x := by\n  have := y; rw [ite_eq_right h]\n")
        again = self.run_script("--kind", "deprecated", log=str(self.root / "b.log"))
        self.assertEqual(again.returncode, 0, again.stderr.decode())
        self.assertIn("deprecated: 0 edits (1 made already)", again.stdout.decode())
        self.assertEqual((self.root / "src/B.lean").read_text(encoding="utf-8"), after)

    def test_names_are_written_into_the_kind_check_as_lean_strings(self):
        text = hints.kind_check({('a"b', "c\\d"), ("Foo.bar", "PAIRS"), ("no.successor", "")})
        for quoted in ('("a\\"b", "c\\\\d")', '("Foo.bar", "PAIRS")', '("no.successor", "")'):
            self.assertIn(quoted, text)
        self.assertEqual(text.count("applyLeanHintsArguments a.type == applyLeanHintsArguments b.type"), 1)

    def test_a_missing_log_or_kinds_file_is_an_error_of_the_call(self):
        self.assertEqual(self.run_script(log=str(self.root / "none.log")).returncode, 2)
        self.assertEqual(self.run_script("--write-kind-check", str(self.root / "none" / "Kinds.lean")).returncode, 2)
        self.assertEqual(self.run_script("--kinds", str(self.root / "none.txt")).returncode, 2)
        self.assertEqual(self.source(), self.SOURCE)

    def test_a_kinds_file_without_the_checks_output_is_refused(self):
        for text in ("error: unknown package 'Mathlib'\n", "KIND\tif_neg\ttheorem\n"):  # the second: an earlier form
            with self.subTest(text=text):
                (self.root / "kinds.txt").write_text(text, encoding="utf-8")
                done = self.run_script("--kinds", str(self.root / "kinds.txt"))
                self.assertEqual(done.returncode, 2)
                self.assertEqual(self.source(), self.SOURCE)

    def test_a_run_without_kinds_says_what_it_cannot_see(self):
        self.assertIn("without --kinds", self.run_script().stderr.decode())
        (self.root / "kinds.txt").write_text("KIND\tif_neg\ttheorem\tite_eq_right\tsame\n", encoding="utf-8")
        done = self.run_script("--kinds", str(self.root / "kinds.txt"))
        self.assertNotIn("without --kinds", done.stderr.decode())
        self.assertIn("rw [ite_eq_right h]", self.source())

    def test_a_log_of_another_tree_ends_with_an_error_code(self):
        (self.root / "src/A.lean").write_text("theorem t : x := by\n  rfl\n", encoding="utf-8")
        done = self.run_script()
        self.assertEqual(done.returncode, 1)
        self.assertIn("3 edits did not find their text", done.stderr.decode())
        self.assertEqual(self.source(), "theorem t : x := by\n  rfl\n")


if __name__ == "__main__":
    unittest.main()
