"""Negative checks for the release gate; these do not replace Lean's proof audit."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("check_repo", Path(__file__).parents[1] / "scripts/check_repo.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class RepositoryChecks(unittest.TestCase):
    def comparator_sources(self):
        return {
            "Challenge.lean": "module\npublic import Mathlib\nnamespace HilbertUMD.Comparison\n"
                              "theorem theorem_1_1 : True := by sorry\nend HilbertUMD.Comparison\n",
            "Solution.lean": "module\npublic import HilbertUMD\n",
            "comparator.json": json.dumps({
                "challenge_module": "Challenge", "solution_module": "Solution",
                "theorem_names": ["HilbertUMD.Comparison.theorem_1_1"],
                "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            }),
        }

    def test_fixed_paper_is_accepted(self):
        data = (Path(__file__).parents[1] / checker.PAPER_PDF).read_bytes()
        self.assertEqual(checker.paper_pdf_issues(data), [])

    def test_changed_paper_is_rejected(self):
        data = (Path(__file__).parents[1] / checker.PAPER_PDF).read_bytes()
        self.assertTrue(checker.paper_pdf_issues(data + b"modified"))

    def test_non_pdf_cannot_replace_paper(self):
        findings = checker.paper_pdf_issues(b"This is not the paper PDF.")
        self.assertTrue(any("Invalid PDF header" in finding for finding in findings))

    def test_nested_comments_and_strings_are_not_proof_holes(self):
        source = '/- sorry /- axiom -/ admit -/\ndef label := "sorry"\n-- native_decide\n'
        self.assertEqual(checker.content_issues("Test.lean", source), [])

    def test_proof_hole_after_comment_is_rejected(self):
        self.assertTrue(checker.content_issues("Test.lean", '/- explanation -/\nexample : True := sorry'))

    def test_token_is_redacted(self):
        token = "gh" + "p_" + "a" * 36
        findings = checker.content_issues("notes.txt", token)
        self.assertTrue(findings)
        self.assertNotIn(token, " ".join(findings))

    def test_links_must_be_published_and_case_correct(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertTrue(checker.link_issues(root, "README.md", "[x](../private.md)", set()))
            self.assertTrue(checker.link_issues(root, "README.md", "[x](Hidden.md)", {"hidden.md"}))
            self.assertEqual(checker.link_issues(root, "docs/a.md", "[x](../README.md)", {"README.md"}), [])

    def test_missing_and_unreachable_modules_are_rejected(self):
        sources = {"HilbertUMD.lean": "import HilbertUMD.Missing\n", "HilbertUMD/Orphan.lean": ""}
        findings = checker.module_issues(sources)
        self.assertEqual(len(findings), 2)

    def test_multiple_imports_and_cycle_terminate(self):
        sources = {"HilbertUMD.lean": "import HilbertUMD.A HilbertUMD.B\n",
                   "HilbertUMD/A.lean": "import HilbertUMD.B\n",
                   "HilbertUMD/B.lean": "import HilbertUMD.A\n"}
        self.assertEqual(checker.module_issues(sources), [])

    def test_module_system_imports_are_followed(self):
        sources = {"HilbertUMD.lean": "module\npublic import HilbertUMD.A HilbertUMD.B\n",
                   "HilbertUMD/A.lean": "module\npublic meta import HilbertUMD.B\n",
                   "HilbertUMD/B.lean": "module\n/- public import HilbertUMD.Missing -/\n"}
        self.assertEqual(checker.module_issues(sources), [])
        self.assertEqual(checker.lean_source_issues(sources), [])

    def test_cache_imports_are_targeted_and_deduplicated(self):
        sources = {"A.lean": "module\npublic import Mathlib.Tactic Mathlib.Data.Real.Basic\n",
                   "B.lean": "module\npublic meta import Mathlib.Tactic\n-- import Mathlib\n",
                   "notes.md": "import Mathlib\n"}
        self.assertEqual(checker.mathlib_cache_imports(sources), ["Mathlib.Data.Real.Basic", "Mathlib.Tactic"])
        for invalid in [{}, {"A.lean": "import Mathlib\n"}]:
            with self.assertRaises(ValueError):
                checker.mathlib_cache_imports(invalid)

    def test_module_header_and_physical_line_limit(self):
        self.assertTrue(checker.lean_source_issues({"A.lean": "import Mathlib\n"}))
        self.assertEqual(checker.lean_source_issues({"A.lean": "/- header -/\nmodule\n"}), [])
        self.assertEqual(checker.lean_source_issues({"lakefile.lean": "import Lake\n"}), [])
        self.assertEqual(checker.lean_source_issues({"A.lean": "module\n" + "\n" * 9999}), [])
        self.assertTrue(checker.lean_source_issues({"A.lean": "module\n" + "\n" * 10000}))

    def test_challenge_admission_is_narrowly_scoped(self):
        source = self.comparator_sources()["Challenge.lean"]
        self.assertEqual(checker.content_issues("Challenge.lean", source), [])
        for declaration in ["Comparison.theorem_1_1", "HilbertUMD.Comparison.theorem_1_1"]:
            self.assertEqual(checker.content_issues("Challenge.lean", source.replace("theorem theorem_1_1", f"theorem {declaration}")), [])
        self.assertTrue(checker.content_issues("Solution.lean", source))
        self.assertTrue(checker.content_issues("HilbertUMD/Challenge.lean", source))
        for modified in [source.replace("theorem_1_1", "unrelated"),
                         source.replace("by sorry", "by admit"),
                         source.replace("theorem theorem_1_1", "def theorem_1_1"),
                         source.replace("theorem theorem_1_1", "def hole : True := sorry\ntheorem theorem_1_1"),
                         source.replace("end HilbertUMD", "theorem hole : True := sorry\nend HilbertUMD")]:
            with self.subTest(source=modified):
                self.assertTrue(checker.content_issues("Challenge.lean", modified))

    def test_proof_sources_cannot_import_challenge(self):
        for name in ["Solution.lean", "HilbertUMD/A.lean", "tests/A.lean"]:
            with self.subTest(name=name):
                self.assertTrue(checker.lean_source_issues({name: "module\npublic import Challenge\n"}))
        self.assertEqual(checker.lean_source_issues({"Solution.lean": "module\n-- import Challenge\n"}), [])

    def test_comparator_contract_accepts_expected_target(self):
        self.assertEqual(checker.comparator_issues(self.comparator_sources()), [])

    def test_comparator_cannot_change_target_or_trust_boundary(self):
        replacements = {
            "challenge_module": "Solution", "solution_module": "Challenge",
            "theorem_names": [], "definition_names": ["HilbertUMD.unrelated"],
            "permitted_axioms": ["propext", "Quot.sound", "sorryAx"],
            "external_kernels": {"fake": ["true"]}, "enable_nanoda": False,
        }
        for field, value in replacements.items():
            with self.subTest(field=field):
                sources = self.comparator_sources()
                config = json.loads(sources["comparator.json"])
                config[field] = value
                sources["comparator.json"] = json.dumps(config)
                self.assertTrue(checker.comparator_issues(sources))

    def test_challenge_cannot_import_proof_or_omit_its_target(self):
        for replacement in ["HilbertUMD", "Solution", "OtherLibrary"]:
            sources = self.comparator_sources()
            sources["Challenge.lean"] = sources["Challenge.lean"].replace("Mathlib", replacement)
            self.assertTrue(checker.comparator_issues(sources))
        sources = self.comparator_sources()
        sources["Challenge.lean"] = "module\npublic import Mathlib\n"
        self.assertTrue(checker.comparator_issues(sources))

    def test_malformed_comparator_configuration_is_rejected(self):
        for invalid in ["{", "[]", "null", '{"permitted_axioms": [{}, {}, {}]}']:
            with self.subTest(invalid=invalid):
                sources = self.comparator_sources()
                sources["comparator.json"] = invalid
                self.assertTrue(checker.comparator_issues(sources))


if __name__ == "__main__":
    unittest.main()
