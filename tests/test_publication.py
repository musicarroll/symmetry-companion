"""Check publication transformations, version pairing, and cover geometry."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
import zipfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_versions import check_versions
from publication_cover import cover_geometry
from publication_figures import split_panels
from publication_epub import normalize_epub, NS
from lxml import etree


class PublicationTests(unittest.TestCase):
    def test_cover_uses_even_interior_count_and_exact_paper_factor(self):
        cover = cover_geometry(236, "0.1.0")
        self.assertAlmostEqual(cover["spine_width_inches"], .531472)
        self.assertAlmostEqual(cover["full_cover_width_inches"], 14.781472)
        self.assertEqual(cover["full_cover_pixels_at_300_dpi"], [4435, 3075])
        with self.assertRaises(ValueError):
            cover_geometry(235, "0.1.0")

    def test_version_pair_rejects_stale_companion(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            public, book = root / "public", root / "book"
            public.mkdir(); book.mkdir()
            (public / "VERSION").write_text("0.1.0\n")
            (public / "lakefile.toml").write_text('version = "0.1.0"\n')
            (book / "VERSION").write_text("0.2.0\n")
            (book / "COMPANION_VERSION").write_text("0.1.0\n")
            self.assertEqual(len(check_versions(public, book)), 2)
            (book / "COMPANION_VERSION").write_text("0.0.9\n")
            with self.assertRaisesRegex(ValueError, "does not match"):
                check_versions(public, book)
            (public / "lakefile.toml").write_text('version = "9.0.0"\n')
            with self.assertRaisesRegex(ValueError, "disagree"):
                check_versions(public)

    def test_split_panels_preserve_caption_math_and_single_label(self):
        source = r'''\begin{figure}[ht]
\includegraphics[width=0.32\textwidth]{one.png}
\includegraphics[width=0.32\textwidth]{two.png}
\caption{Compare $x=\frac{a}{b}$ and $y$.}\label{fig:original}
\end{figure}'''
        result = split_panels(source)
        self.assertEqual(result.count(r"\begin{figure}"), 2)
        self.assertEqual(result.count(r"\ContinuedFloat"), 1)
        self.assertEqual(result.count(r"\label{fig:original}"), 1)
        self.assertIn(r"$x=\frac{a}{b}$", result)
        self.assertIn(r"Figure~\ref{fig:original}", result)
        self.assertIn("one.png", result)
        self.assertIn("two.png", result)

    def test_epub_navigation_metadata_assets_and_math_are_preserved(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "results/figures").mkdir(parents=True)
            (root / "results/figures/plot.png").write_bytes(b"fixture-image")
            container = '<container xmlns="urn:oasis:names:tc:opendocument:xmlns:container"><rootfiles><rootfile full-path="OEBPS/content.opf"/></rootfiles></container>'
            opf = '''<package xmlns="http://www.idpf.org/2007/opf" version="3.0" unique-identifier="id">
<metadata xmlns:dc="http://purl.org/dc/elements/1.1/"><dc:title>Old</dc:title><dc:identifier id="id">old</dc:identifier><dc:creator>Anonymous</dc:creator><dc:language>en</dc:language></metadata>
<manifest><item id="toc" href="toc.xhtml" media-type="application/xhtml+xml" properties="nav mathml"/><item id="chapter" href="chapter.xhtml" media-type="application/xhtml+xml"/></manifest>
<spine><itemref idref="toc"/><itemref idref="chapter"/></spine></package>'''
            toc = '<html xmlns="http://www.w3.org/1999/xhtml"><head><title>Contents</title></head><body><ol><span>Broken</span></ol></body></html>'
            chapter = '''<html xmlns="http://www.w3.org/1999/xhtml"><head><title>Chapter 1</title></head><body>
<h2>Finite Relational Structures and Symmetry</h2><h3>Relations</h3>
<p>Keep this argument.</p><math xmlns="http://www.w3.org/1998/Math/MathML"><mi>x</mi></math>
<img src="results/figures/plot.png" alt="PIC"/></body></html>'''
            source, target = root / "source.epub", root / "final.epub"
            with zipfile.ZipFile(source, "w") as archive:
                for name, content in {"mimetype": "application/epub+zip", "META-INF/container.xml": container,
                                      "OEBPS/content.opf": opf, "OEBPS/toc.xhtml": toc,
                                      "OEBPS/chapter.xhtml": chapter}.items():
                    archive.writestr(name, content)
            report = normalize_epub(source, target, {"title": "Book", "subtitle": "Subtitle",
                "author": "Author", "language": "en-US", "edition": "First edition", "status": "proof"}, "0.1.0", root)
            self.assertEqual(report["native_mathml_expressions"], 1)
            with zipfile.ZipFile(target) as archive:
                self.assertEqual(archive.infolist()[0].filename, "mimetype")
                self.assertEqual(archive.infolist()[0].compress_type, zipfile.ZIP_STORED)
                package = etree.fromstring(archive.read("OEBPS/content.opf"))
                self.assertEqual(package.find("opf:metadata/dc:creator", NS).text, "Author")
                nav = etree.fromstring(archive.read("OEBPS/toc.xhtml"))
                self.assertEqual(nav.xpath("count(//h:ol/h:span)", namespaces=NS), 0)
                self.assertIn("Keep this argument.", archive.read("OEBPS/chapter.xhtml").decode())
                self.assertEqual(archive.read("OEBPS/results/figures/plot.png"), b"fixture-image")
                item = package.xpath("//opf:item[@id='chapter']", namespaces=NS)[0]
                self.assertIn("mathml", item.get("properties"))


if __name__ == "__main__":
    unittest.main()
