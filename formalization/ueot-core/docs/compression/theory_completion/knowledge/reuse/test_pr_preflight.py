#!/usr/bin/env python3
"""Adversarial Git-commit fixture tests; no network, no real UEOT source edits."""
from pathlib import Path
import tempfile
import subprocess
import unittest
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pr_preflight as pf

ROOT = "formalization/ueot-core/"
PACKAGE = ROOT + "UEOT/"


def git(repo, *args):
    return subprocess.check_output(["git", *args], cwd=repo,
                                   text=True, stderr=subprocess.STDOUT).strip()


def write(root, path, text):
    p = root / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


class DeltaChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ueot-fkrg-pr-delta-")
        self.repo = Path(self.temp.name)
        git(self.repo, "init", "-q")
        git(self.repo, "config", "user.name", "Test Researcher")
        git(self.repo, "config", "user.email", "test@example.invalid")
        write(self.repo, ROOT + "UEOT.lean", "import UEOT.Previous\n")
        write(self.repo, PACKAGE + "Previous.lean",
              "namespace UEOT.Example\n"
              "theorem reused_bound (x : Nat) : x = x := by rfl\n"
              "theorem foundational_action (x : Nat) : x = x := by rfl\n"
              "end UEOT.Example\n")
        write(self.repo, PACKAGE + "Keep.lean",
              "namespace UEOT.Kept\ntheorem source_stays : True := trivial\nend UEOT.Kept\n")
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-q", "-m", "base")
        self.base = git(self.repo, "rev-parse", "HEAD")

    def tearDown(self):
        self.temp.cleanup()

    def commit(self, reason="candidate"):
        git(self.repo, "add", ".")
        git(self.repo, "commit", "-q", "-m", reason)
        return git(self.repo, "rev-parse", "HEAD")

    def test_new_theorem_detects_prior_same_name_without_auto_block(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "theorem reused_bound (x : Nat) : x = x := by rfl\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(result["status"], "PASS_WITH_TYPED_REUSE_REVIEW_REQUIRED")
        self.assertEqual(result["new_public_source_theorem_count"], 1)
        entry = result["new_public_source_theorems"][0]
        self.assertEqual(entry["symbol"], "UEOT.New.reused_bound")
        self.assertEqual(entry["reuse_candidates"][0]["symbol"], "UEOT.Example.reused_bound")
        self.assertFalse(result["fuzzy_similarity_is_a_proof"])

    def test_changed_existing_proof_not_falsely_new(self):
        write(self.repo, PACKAGE + "Previous.lean",
              "namespace UEOT.Example\n"
              "theorem reused_bound (x : Nat) : x = x := by simp\n"
              "theorem foundational_action (x : Nat) : x = x := by rfl\n"
              "end UEOT.Example\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(result["new_public_source_theorem_count"], 0)
        self.assertIn(PACKAGE + "Previous.lean", result["changed_lean_paths"])

    def test_private_is_not_proposed_as_public_reuse(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\nprivate theorem hidden_helper : True := trivial\n"
              "lemma public_result : True := trivial\nend UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(result["new_public_source_theorem_count"], 1)
        self.assertEqual(result["new_public_source_theorems"][0]["symbol"],
                         "UEOT.New.public_result")

    def test_noncomputable_section_closure_preserves_surrounding_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.Nested\nnoncomputable section\n"
              "theorem inside_section : True := trivial\nend\n"
              "theorem after_section : True := trivial\n"
              "end UEOT.Nested\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        names = {x["symbol"] for x in result["new_public_source_theorems"]}
        self.assertEqual(names, {"UEOT.Nested.inside_section",
                                 "UEOT.Nested.after_section"})

    def test_unicode_and_attribute_declarations_are_reported(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n@[simp] theorem τ_bound : True := trivial\n"
              "lemma θεώρημα : True := trivial\nend UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"UEOT.New.τ_bound", "UEOT.New.θεώρημα"})

    def test_public_and_nonrec_declarations_not_silently_dropped(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\npublic theorem visible : True := trivial\n"
              "nonrec theorem visible_nonrec : True := trivial\n"
              "@[simp] public lemma visible_simp : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"UEOT.New.visible", "UEOT.New.visible_nonrec", "UEOT.New.visible_simp"}
        )

    def test_public_and_attribute_section_closures_preserve_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "public section\ntheorem inside_public : True := trivial\nend\n"
              "@[expose] public section\n"
              "lemma inside_expose : True := trivial\nend\n"
              "theorem after_public_sections : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"UEOT.New.inside_public", "UEOT.New.inside_expose",
             "UEOT.New.after_public_sections"}
        )

    def test_unicode_qualified_name_and_question_mark_not_truncated(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "theorem Foo.τ : True := trivial\n"
              "lemma ready? : True := trivial\n"
              "theorem safe! : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"UEOT.New.Foo.τ", "UEOT.New.ready?", "UEOT.New.safe!"})

    def test_meta_section_preserves_surrounding_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "@[expose] public meta section\n"
              "theorem inside_meta : True := trivial\nend\n"
              "theorem after_meta : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"UEOT.New.inside_meta", "UEOT.New.after_meta"})

    def test_default_repo_path_is_live_checkout(self):
        self.assertEqual(pf.REPO_DEFAULT, HERE.parents[6])
        self.assertTrue((pf.REPO_DEFAULT / ".git").exists())

    def test_open_in_theorem_wrapper_is_discovered(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "open Nat in theorem open_scoped_result : True := trivial\n"
              "open Nat in public lemma open_scoped_public : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"UEOT.New.open_scoped_result",
                          "UEOT.New.open_scoped_public"})

    def test_literal_root_component_namespace_matches_real_lean(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace A\nnamespace _root_.B\n"
              "theorem inside_B : True := trivial\n"
              "end B\nend _root_\n"
              "theorem after_root : True := trivial\nend A\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"A._root_.B.inside_B", "A.after_root"})

    def test_nested_literal_root_component_compound_end(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace A\nnamespace _root_.B\nnamespace C\n"
              "theorem inside_C : True := trivial\n"
              "end B.C\nend _root_\n"
              "theorem after_C : True := trivial\nend A\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"A._root_.B.C.inside_C", "A.after_C"})

    def test_anonymous_section_prevents_skipped_qualified_end(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nsection A\nsection\nsection B\n"
              "theorem inside_sections : True := trivial\n"
              "end A.B\ntheorem after_sections : True := trivial\nend N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_QUALIFIED_END"):
            pf.preflight(self.repo, self.base, head)

    def test_valid_anonymous_section_closes_one_by_one(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nsection A\nsection\nsection B\n"
              "theorem inside_sections : True := trivial\n"
              "end B\nend\nend A\n"
              "theorem after_sections : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.inside_sections", "N.after_sections"})

    def test_qualified_end_may_close_multiple_namespace_components(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace A.B\nnamespace C\n"
              "theorem before_end : True := trivial\n"
              "end B.C\ntheorem after_end : True := trivial\nend A\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"A.B.C.before_end", "A.after_end"})

    def test_qualified_end_partially_closes_compound_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace A.B\n"
              "theorem inside_B : True := trivial\n"
              "end B\ntheorem inside_A : True := trivial\nend A\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"A.B.inside_B", "A.inside_A"})

    def test_same_physical_line_multiple_commands_fail_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N theorem fresh : True := True.intro end N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTICOMMAND_LEAN_LINE"):
            pf.preflight(self.repo, self.base, head)

    def test_theorem_after_unparsed_variable_command_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nvariable (x : Nat) theorem fresh : True := trivial\nend N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTICOMMAND_LEAN_LINE"):
            pf.preflight(self.repo, self.base, head)

    def test_escaped_reserved_words_are_not_mistaken_for_commands(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ndef «theorem» : Nat := 0\n"
              "axiom «lemma» : Prop\ntheorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_mutual_block_does_not_pop_enclosing_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nmutual\ndef f : Nat := 0\ndef g : Nat := 0\n"
              "end\ntheorem after_mutual : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.after_mutual"})

    def test_private_section_theorems_not_listed_as_public(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nprivate section\n"
              "theorem hidden : True := trivial\nend\n"
              "theorem public_result : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.public_result"})

    def test_lemma_after_unparsed_helper_command_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ndef helper : True := trivial lemma fresh : True := trivial\nend N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTICOMMAND_LEAN_LINE"):
            pf.preflight(self.repo, self.base, head)

    def test_same_line_namespace_closing_command_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N end N\ntheorem fresh : True := trivial\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTICOMMAND_LEAN_LINE"):
            pf.preflight(self.repo, self.base, head)

    def test_escaped_namespace_name_with_spaces_not_truncated(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace «foo bar»\ntheorem result : True := trivial\n"
              "end «foo bar»\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"«foo bar».result"})

    def test_private_modifier_survives_standalone_attribute_line(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nprivate\n@[simp]\ntheorem hidden : True := trivial\n"
              "theorem visible : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.visible"})

    def test_attribute_with_escaped_closing_bracket_not_truncated(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              '@[deprecated «old]name» (since := "2026-10-10")] '
              "theorem fresh : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.fresh"}
        )

    def test_attribute_with_escaped_private_and_bracket_remains_public(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              '@[deprecated «private]token» (since := "2026-10-10")] '
              "theorem fresh : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.fresh"}
        )

    def test_standalone_attribute_with_escaped_bracket(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              '@[deprecated «old]name» (since := "2026-10-10")]\n'
              "theorem fresh : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.fresh"}
        )

    def test_deprecated_attribute_containing_escaped_private_is_public(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "@[deprecated «private» (since := \"2026-10-10\")] theorem fresh : True := trivial\n"
              "end N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.fresh"})

    def test_single_line_lean_command_quotation_is_not_a_real_theorem(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "def quoted : Lean.MacroM Lean.Syntax := " +
              chr(96) + "(command| theorem generated : True := trivial)\n"
              "theorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_character_literals_inside_quoted_syntax_do_not_change_depth(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "def quoted_open : Lean.Syntax := " + chr(96) + "(term| '(')\n"
              "def quoted_close : Lean.Syntax := " + chr(96) + "(term| ')')\n"
              "theorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_escaped_char_with_paren_does_not_terminate_syntax_quote(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "def quoted : Lean.Syntax := " + chr(96) + "(term| '\\'')\n"
              "theorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_multiline_lean_command_quotation_is_not_a_real_theorem(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "def quoted : Lean.MacroM Lean.Syntax := " + chr(96) + "(command|\n"
              " theorem generated : True := trivial\n)\n"
              "theorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_committed_lean_symlink_fails_closed(self):
        target = self.repo / PACKAGE / "Linked.lean"
        target.symlink_to("Previous.lean")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_LEAN_SOURCE_SYMLINK"):
            pf.preflight(self.repo, self.base, head)

    def test_private_before_multiline_attribute_remains_private(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nprivate\n@[simp,\n  grind]\n"
              "theorem hidden : True := trivial\n"
              "theorem visible : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.visible"})

    def test_multiline_attribute_last_line_with_theorem_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n@[simp,\n grind] theorem hidden : True := trivial\nend N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTILINE_ATTRIBUTE_TAIL"):
            pf.preflight(self.repo, self.base, head)

    def test_standalone_attribute_before_public_theorem_is_visible(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n@[simp]\ntheorem public_result : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.public_result"})

    def test_private_modifier_on_prior_line_does_not_expose_theorem(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nprivate\ntheorem hidden : True := trivial\n"
              "theorem visible : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.visible"})

    def test_private_prior_line_section_does_not_expose_members(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nprivate\nsection\n"
              "theorem inside : True := trivial\nend\n"
              "theorem public_after : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.public_after"})

    def test_escaped_name_with_lean_comment_delimiters_survives(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "theorem «fresh--result» : True := trivial\n"
              "lemma «fresh/-comment-/result» : True := trivial\n"
              "theorem «fresh" + chr(96) + "(quote)result» : True := trivial\n"
              "theorem «fresh\"quoted\"result» : True := trivial\n"
              "end N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.«fresh--result»", "N.«fresh/-comment-/result»",
             "N.«fresh" + chr(96) + "(quote)result»", 'N.«fresh"quoted"result»'}
        )

    def test_comment_and_string_guillemets_do_not_resurrect_theorems(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              '-- theorem «fake--name» : True := trivial\n'
              '/- theorem «fake/-nested-/name» : True := trivial -/\n'
              'def example : String := "«fake--in-string»"\n'
              "theorem visible : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.visible"}
        )

    def test_syntax_quote_escaped_name_is_not_source_theorem(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "def quotation : Lean.Syntax := " + chr(96) +
              "(term| «fake--theorem/-/name»)\n"
              "theorem visible : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(
            {x["symbol"] for x in result["new_public_source_theorems"]},
            {"N.visible"}
        )

    def test_unterminated_escaped_name_rejected_not_silent(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem «unterminated-- : True := trivial\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNTERMINATED_ESCAPED_IDENTIFIER"):
            pf.preflight(self.repo, self.base, head)

    def test_escaped_identifier_containing_newline_is_complete(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem «fresh\nresult» : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.«fresh\nresult»"})

    def test_multiline_escaped_namespace_identifier_preserved(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace «Scope\nName»\nlemma inside : True := trivial\n"
              "end «Scope\nName»\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"«Scope\nName».inside"})

    def test_indented_multiline_namespace_name(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace\n  Foo\ntheorem fresh : True := trivial\nend Foo\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({v["symbol"] for v in result["new_public_source_theorems"]},
                         {"Foo.fresh"})

    def test_indented_multiline_theorem_and_lemma_names(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem\n  fresh : True := trivial\n"
              "lemma\n  second : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({v["symbol"] for v in result["new_public_source_theorems"]},
                         {"N.fresh", "N.second"})

    def test_indented_multiline_section_and_end_names(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "section\n  Bar\ntheorem within : True := trivial\nend Bar\n"
              "namespace Foo\nlemma nested : True := trivial\nend\n  Foo\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({v["symbol"] for v in result["new_public_source_theorems"]},
                         {"within", "Foo.nested"})

    def test_unindented_multiline_namespace_is_not_accepted_as_root(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace\nFoo\ntheorem fresh : True := trivial\nend Foo\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_REQUIRED_MULTILINE_NAME"):
            pf.preflight(self.repo, self.base, head)

    def test_open_guillemet_inside_escaped_identifier_is_literal(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem «alpha«beta» : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({v["symbol"] for v in result["new_public_source_theorems"]},
                         {"N.«alpha«beta»"})

    def test_guillemet_character_literals_are_not_name_delimiters(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ndef openAngle : Char := '«'\n"
              "def closeAngle : Char := '»'\n"
              "theorem real_public : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({v["symbol"] for v in result["new_public_source_theorems"]},
                         {"N.real_public"})

    def test_unterminated_multiline_escaped_identifier_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem «fresh\nresult : True := trivial\nend N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNTERMINATED_ESCAPED_IDENTIFIER"):
            pf.preflight(self.repo, self.base, head)

    def test_escaped_dotted_leaf_name_is_not_split_mid_identifier(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\ntheorem «alpha.beta.gamma» : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        leaf = result["new_public_source_theorems"][0]
        self.assertEqual(leaf["symbol"], "N.«alpha.beta.gamma»")
        self.assertEqual(leaf["short_name"], "«alpha.beta.gamma»")

    def test_multiple_theorems_on_one_physical_line_fail_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\n"
              "theorem old : True := trivial theorem fresh : True := trivial\n"
              "end N\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_MULTICOMMAND_LEAN_LINE"):
            pf.preflight(self.repo, self.base, head)

    def test_qualified_end_of_two_named_sections(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace N\nsection A\nsection B\n"
              "theorem inside : True := trivial\n"
              "end A.B\n"
              "theorem after : True := trivial\nend N\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"N.inside", "N.after"})

    def test_include_and_omit_scoped_command_wrappers_are_discovered(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "variable (h : True)\n"
              "include h in theorem included : True := h\n"
              "omit h in lemma omitted : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"UEOT.New.included", "UEOT.New.omitted"})

    def test_explicit_root_qualified_theorem_does_not_prepend_namespace(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\n"
              "theorem _root_.Somewhere.τ : True := trivial\n"
              "lemma normal : True := trivial\n"
              "end UEOT.New\n")
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual({x["symbol"] for x in result["new_public_source_theorems"]},
                         {"Somewhere.τ", "UEOT.New.normal"})

    def test_unparsed_public_lemma_fails_closed(self):
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\ntheorem : True := trivial\nend UEOT.New\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "UNSUPPORTED_PUBLIC_LEAN_DECLARATION"):
            pf.preflight(self.repo, self.base, head)

    def test_duplicate_exact_fqn_is_rejected_even_across_modules(self):
        write(self.repo, PACKAGE + "Clash.lean",
              "namespace UEOT.Example\n"
              "theorem reused_bound (x : Nat) : x = x := by rfl\n"
              "end UEOT.Example\n")
        head = self.commit()
        with self.assertRaisesRegex(RuntimeError, "DUPLICATE_PUBLIC_LEXICAL_FQN_HEAD"):
            pf.preflight(self.repo, self.base, head)

    def test_removed_module_does_not_claim_new_theorem(self):
        (self.repo / PACKAGE / "Previous.lean").unlink()
        head = self.commit()
        result = pf.preflight(self.repo, self.base, head)
        self.assertEqual(result["new_public_source_theorem_count"], 0)
        self.assertEqual(result["candidate_lean_module_count"], 2)

    def test_invalid_ref_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "INVALID_REVISION"):
            pf.preflight(self.repo, self.base, "--fake")
        with self.assertRaisesRegex(RuntimeError, "GIT_COMMAND_FAILED"):
            pf.preflight(self.repo, self.base, "nonexistent-commit")

    def test_baseline_cannot_be_implicitly_mutated_by_worktree(self):
        # Editing an uncommitted candidate module must not affect Git object
        # preflight: it looks at commit trees only, not working-tree bytes.
        write(self.repo, PACKAGE + "Novel.lean",
              "namespace UEOT.New\nlemma uncommitted : True := trivial\nend UEOT.New\n")
        result = pf.preflight(self.repo, self.base, self.base)
        self.assertEqual(result["status"], "PASS_NO_NEW_PUBLIC_THEOREMS")
        self.assertEqual(result["new_public_source_theorem_count"], 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
