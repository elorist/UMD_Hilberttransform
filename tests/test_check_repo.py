"""Negative checks for the release gate; these do not replace Lean's proof audit."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("check_repo", Path(__file__).parents[1] / "scripts/check_repo.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class RepositoryChecks(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
