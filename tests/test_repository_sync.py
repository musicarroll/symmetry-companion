"""Exercise migration boundaries and the failure paths of synchronization."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_lean_coverage import manuscript_inventory, validate_inventory
from check_slide_sync import check_or_write
from repo_sync import book_root, digest
from sync_private_book import synchronize


class RepositorySyncTests(unittest.TestCase):
    def test_public_inventory_matches_ledger(self):
        inventory = {key: tuple(value) for key, value in json.loads(
            (ROOT / "lean/manuscript-inventory.json").read_text()).items()}
        entries = json.loads((ROOT / "doc/lean-coverage.json").read_text())
        self.assertGreater(validate_inventory(entries, inventory), 0)
        changed = dict(inventory)
        changed.pop(next(iter(changed)))
        with self.assertRaisesRegex(ValueError, "Inventory mismatch"):
            validate_inventory(entries, changed)

    def test_inventory_follows_inputs_and_ignores_comments(self):
        with tempfile.TemporaryDirectory() as directory:
            book = Path(directory)
            (book / "main.tex").write_text(r"\input{section}")
            (book / "section.tex").write_text(
                "% \\begin{lemma}\\label{ignored}\\end{lemma}\n"
                r"\begin{theorem}\label{kept}Body\end{theorem}")
            self.assertEqual(manuscript_inventory(book), {"kept": ("section.tex", "theorem")})
            (book / "section.tex").write_text(r"\begin{lemma}Unlabeled\end{lemma}")
            with self.assertRaisesRegex(ValueError, "Unlabeled"):
                manuscript_inventory(book)

    def test_sync_is_read_only_by_default_and_has_fixed_directions(self):
        with tempfile.TemporaryDirectory() as directory:
            public, book = Path(directory) / "public", Path(directory) / "book"
            (public / "results/figures").mkdir(parents=True)
            book.mkdir()
            (book / "references.bib").write_text("book bibliography")
            (public / "references.bib").write_text("stale bibliography")
            (public / "results/figures/test.png").write_bytes(b"figure")
            (book / "main.tex").write_text("private prose")
            with self.assertRaisesRegex(ValueError, "Artifacts differ"):
                synchronize(public, book)
            self.assertEqual((public / "references.bib").read_text(), "stale bibliography")
            self.assertFalse((book / "results").exists())
            self.assertEqual(synchronize(public, book, write=True), 2)
            self.assertEqual((public / "references.bib").read_text(), "book bibliography")
            self.assertEqual((book / "results/figures/test.png").read_bytes(), b"figure")
            self.assertFalse((public / "main.tex").exists())
            self.assertEqual((book / "main.tex").read_text(), "private prose")
            self.assertEqual(synchronize(public, book), 0)

    def test_snapshot_requires_explicit_review_after_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            snapshot = Path(directory) / "snapshot"
            with self.assertRaises(ValueError):
                check_or_write(snapshot, "first", False)
            check_or_write(snapshot, "first", True)
            with self.assertRaisesRegex(ValueError, "Sources changed"):
                check_or_write(snapshot, "second", False)
            self.assertEqual(snapshot.read_text(), "first")

    def test_digest_is_portable_and_content_sensitive(self):
        with tempfile.TemporaryDirectory() as directory:
            roots = [Path(directory) / name for name in ("first", "second")]
            for root in roots:
                root.mkdir()
                (root / "file").write_text("same")
            self.assertEqual(*(digest(root, [root / "file"]) for root in roots))
            (roots[1] / "file").write_text("changed")
            self.assertNotEqual(*(digest(root, [root / "file"]) for root in roots))

    def test_private_source_is_not_in_public_tree(self):
        for name in ("main.tex", "main.pdf", "macros.tex", "chapters", "SESSION_NOTES.md"):
            self.assertFalse((ROOT / name).exists(), name)
        with self.assertRaises(ValueError):
            book_root(ROOT)


if __name__ == "__main__":
    unittest.main()
