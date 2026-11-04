# Optional publication build tools

The actual manuscript and publication artifacts remain in a separate private
checkout. These tools accept its path explicitly and never put its chapters or
PDF/EPUB outputs in the public companion tree. Public Lean and slide builds do
not require any manuscript access.

Install the numerical and publication Python dependencies:

```bash
python3 -m pip install -r requirements.txt -r requirements-publication.txt
```

The host also needs PDFLaTeX, BibTeX, MakeIndex, Ghostscript, Poppler, MuPDF,
TeX4ebook, and EPUBCheck. A system TeX4ebook is preferred. On Ubuntu, it is part
of `texlive-extra-utils`; the build also recognizes a workspace-local extracted
package under `.tools/publishing/extracted/` and EPUBCheck under
`.tools/publishing/epubcheck-*/`. These downloaded tools and caches are ignored
by Git. The first proof used TeX Live 2023's TeX4ht/TeX4ebook and EPUBCheck 5.4.0.

```bash
python3 scripts/check_versions.py --book ../symmetry-monograph
python3 scripts/build_publication.py --book ../symmetry-monograph
```

Use `--format paperback` or `--format epub` to build one format. Both compile
the staged `main.tex` and the same modular mathematical source files.

The paperback build checks page dimensions, font embedding, and grayscale,
flattened raster images. It regenerates publication figures from recorded data
with a minimum target label size, and uses continued panels for small grouped
plots. Numerical data and ordinary public figures are unchanged. It computes
cover dimensions from the final even page count and creates a layout guide.

The EPUB retains native MathML. Its postprocessor normalizes the ordered
chapter/section navigation, bibliography metadata, image packaging, and linked
indexes. Chapter and appendix labels include explicit text spacing so navigation
labels survive readers that omit line breaks. An optional `cover_image` relative
path in the private `publishing/metadata.json` embeds the original PNG/JPEG as
the OPF `cover-image`, with compatibility cover metadata. No extra HTML cover
page is inserted, following KDP guidance against duplicate covers. The same
image is exported as `kindle-cover.png` (or `.jpg`) for the separate marketing
cover upload. Artwork stays in the private checkout. EPUBCheck must pass without errors or warnings. Reports, cover
parameters, and artifact hashes accompany the outputs in the private checkout.

These automated checks do not emulate Amazon's converter or physical printer.
Inspect the EPUB in Kindle Previewer and the paperback through KDP's previewer
and a physical proof before publishing.

## Versioning

`VERSION` and the Lake package version agree. Tags use `vMAJOR.MINOR.PATCH`.
The book's `COMPANION_VERSION` identifies its chosen companion release; versions
can advance independently. A tagged book links to tagged companion files so
later development on `main` does not change the references for that edition.

```bash
python3 scripts/check_versions.py
python3 scripts/check_versions.py --book ../symmetry-monograph --require-tag
```

The tag check requires each selected version tag to identify the current commit.
It is intended for release preparation rather than ordinary development on
commits after a release. Do not rewrite a published tag; bump the version.
