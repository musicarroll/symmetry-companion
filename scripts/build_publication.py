#!/usr/bin/env python3
"""Build private book publication artifacts from an explicit checkout path.

No manuscript source or output is written into the public companion repository.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(command, cwd, log, env=None):
    with open(log, "a") as output:
        output.write("\nCOMMAND: " + " ".join(map(str, command)) + "\n")
        output.flush()
        result = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}); inspect {log}")


def version(path):
    value = path.read_text().strip()
    if not re.fullmatch(r"\d+\.\d+\.\d+", value):
        raise ValueError(f"Expected MAJOR.MINOR.PATCH in {path}")
    return value


def stage(book, mode):
    work = book / "build/publication" / mode
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    for name in ("main.tex", "macros.tex", "references.bib", "VERSION", "COMPANION_VERSION"):
        shutil.copy2(book / name, work / name)
    for name in ("chapters", "results/figures", "publishing"):
        shutil.copytree(book / name, work / name)
    metadata = json.loads((book / "publishing/metadata.json").read_text())
    if metadata.get("cover_image"):
        cover = Path(metadata["cover_image"])
        if cover.is_absolute() or ".." in cover.parts:
            raise ValueError("Cover image must be a relative path in the private book checkout")
        (work / cover).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(book / cover, work / cover)
    (work / "publishing/build-mode.tex").write_text(
        "\\def\\" + ("PaperbackEdition" if mode == "paperback" else "KindleEdition") + "{1}\n")
    if mode == "epub":
        # EPUB cannot embed PDF graphics. Render the two vector plot assets
        # before TeX4ht reads them; the source manuscript remains unchanged.
        replacements = {}
        for pdf in (work / "results/figures").glob("*.pdf"):
            target = pdf.with_name(pdf.stem + "-epub")
            subprocess.run(["pdftoppm", "-r", "300", "-singlefile", "-png",
                            str(pdf), str(target)], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            replacements[str(pdf.relative_to(work))] = str(target.relative_to(work)) + ".png"
        for path in (work / "chapters").rglob("*.tex"):
            text = path.read_text()
            for old, new in replacements.items():
                text = text.replace("{" + old + "}", "{" + new + "}")
            path.write_text(text)
    else:
        from publication_figures import prepare_figures
        prepare_figures(ROOT, work)
        from PIL import Image
        # Flatten each figure on white before laying out the page. This keeps
        # text outside the figure vector-based when the final PDF is flattened.
        for image in (work / "results/figures").glob("*.png"):
            with Image.open(image) as opened:
                rgba = opened.convert("RGBA")
                background = Image.new("RGBA", rgba.size, "white")
                background.alpha_composite(rgba)
                background.convert("L").save(image)
        for pdf in (work / "results/figures").glob("*.pdf"):
            temporary = pdf.with_suffix(".flattened.pdf")
            run(["gs", "-sDEVICE=pdfwrite", "-dCompatibilityLevel=1.3", "-dBATCH", "-dNOPAUSE",
                 "-sColorConversionStrategy=Gray", "-dProcessColorModel=/DeviceGray", "-r600",
                 "-sOutputFile=" + str(temporary), pdf], work, work / "build.log")
            temporary.replace(pdf)
    return work


def pages(pdf):
    info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
    return int(re.search(r"^Pages:\s+(\d+)", info, re.M)[1])


def paperback(book, output):
    work = stage(book, "paperback")
    log = work / "build.log"
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]
    run(command, work, log)
    run(["bibtex", "main"], work, log)
    run(command, work, log)
    run(command, work, log)
    final_log = (work / "main.log").read_text(errors="replace")
    problems = re.findall(r"Overfull[^\n]*|LaTeX Warning:[^\n]*|pdfTeX warning[^\n]*", final_log)
    if problems:
        raise RuntimeError("Paperback layout requires review:\n" + "\n".join(problems))
    pdf = output / "symmetry-paperback-interior.pdf"
    run(["gs", "-sDEVICE=pdfwrite", "-dCompatibilityLevel=1.3", "-dNOPAUSE", "-dBATCH",
         "-sColorConversionStrategy=Gray", "-dProcessColorModel=/DeviceGray",
         "-dEmbedAllFonts=true", "-dSubsetFonts=true", "-dDownsampleColorImages=false",
         "-dDownsampleGrayImages=false", "-dDownsampleMonoImages=false", "-r600",
         "-sOutputFile=" + str(pdf), "main.pdf"], work, log)
    count = pages(pdf)
    if count % 2:
        blank = work / "blank.pdf"
        run(["gs", "-sDEVICE=pdfwrite", "-dBATCH", "-dNOPAUSE",
             "-sOutputFile=" + str(blank), "-c",
             "<</PageSize [504 720]>> setpagedevice showpage"], work, log)
        merged = work / "even-interior.pdf"
        run(["mutool", "merge", "-o", merged, pdf, blank], work, log)
        shutil.copy2(merged, pdf)
        count = pages(pdf)
    report = {"pages": count, "trim_inches": [7, 10], "interior_bleed": False,
              "ink": "black and white", "paper": "white", "body_font_points": 11,
              "inside_margin_inches": .85, "outside_margin_inches": .65}
    info = subprocess.check_output(["pdfinfo", "-f", "1", "-l", str(count), "-box", str(pdf)], text=True)
    sizes = re.findall(r"Page\s+\d+ size:\s+([\d.]+) x ([\d.]+)", info)
    if len(sizes) != count or any(abs(float(w)-504)>.02 or abs(float(h)-720)>.02 for w,h in sizes):
        raise ValueError("Paperback pages do not all have 7 x 10 inch trim")
    fonts = subprocess.check_output(["pdffonts", str(pdf)], text=True)
    font_rows = re.findall(r"\s+(yes|no)\s+(yes|no)\s+(yes|no)\s+\d+\s+\d+$", fonts, re.M)
    if not font_rows or any(embedded != "yes" for embedded, _, _ in font_rows) or "Type 3" in fonts:
        raise ValueError("Paperback has an unembedded or bitmap font")
    images = subprocess.check_output(["pdfimages", "-list", str(pdf)], text=True)
    if "smask" in images or re.search(r"\s(?:rgb|cmyk)\s", images):
        raise ValueError("Paperback contains an unflattened or color raster image")
    report.update({"all_pages_same_size": True, "embedded_fonts": len(font_rows),
                   "grayscale_raster_images": True, "transparency_flattened": True})
    (output / "paperback-report.json").write_text(json.dumps(report, indent=2) + "\n")
    from publication_cover import write_cover_guide
    write_cover_guide(output, work, count, version(book / "VERSION"))
    return report


def ebook_command():
    found = shutil.which("tex4ebook")
    env = os.environ.copy()
    if found:
        return [found], env
    tree = ROOT / ".tools/publishing/extracted/usr/share/texlive/texmf-dist"
    program = tree / "scripts/tex4ebook/tex4ebook"
    if not program.exists():
        raise ValueError("Install tex4ebook (TeX Live extra utilities), or provision .tools/publishing.")
    env["TEXMFHOME"] = str(tree)
    return ["texlua", str(program)], env


def epub(book, output):
    from publication_epub import normalize_epub
    work = stage(book, "epub")
    command, env = ebook_command()
    run(command + ["-a", "info", "-f", "epub3", "-e", "publishing/epub.mk4", "-c", "publishing/epub.cfg",
                   "main.tex", "mathml"], work, work / "build.log", env)
    candidates = list(work.rglob("*.epub"))
    if not candidates:
        raise RuntimeError(f"No EPUB generated; inspect {work / 'build.log'}")
    target = output / "symmetry-kindle-mathml.epub"
    metadata = json.loads((book / "publishing/metadata.json").read_text())
    report = normalize_epub(candidates[0], target, metadata, version(book / "VERSION"), work)
    if metadata.get("cover_image"):
        cover = work / metadata["cover_image"]
        marketing_cover = output / ("kindle-cover" + cover.suffix.lower())
        shutil.copy2(cover, marketing_cover)
        report["marketing_cover"] = marketing_cover.name
    report["file"] = target.name
    checker = shutil.which("epubcheck")
    if checker:
        check_command = [checker]
    else:
        jars = sorted((ROOT / ".tools/publishing").glob("epubcheck-*/epubcheck.jar"))
        if not jars:
            raise ValueError("EPUBCheck is required to validate the publication EPUB")
        check_command = ["java", "-jar", str(jars[-1])]
    validation_log = output / "epubcheck.txt"
    validation_log.write_text("")
    run(check_command + [str(target)], work, validation_log)
    if "No errors or warnings detected" not in validation_log.read_text():
        raise ValueError("EPUBCheck did not report a clean publication EPUB")
    report["epubcheck"] = "0 errors, 0 warnings"
    (output / "epub-report.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book", required=True, type=Path)
    parser.add_argument("--format", choices=("all", "paperback", "epub"), default="all")
    args = parser.parse_args()
    book = args.book.resolve()
    if book == ROOT or not (book / "main.tex").is_file():
        raise ValueError("Supply a separate private manuscript checkout containing main.tex")
    book_version = version(book / "VERSION")
    companion_version = version(ROOT / "VERSION")
    if version(book / "COMPANION_VERSION") != companion_version:
        raise ValueError("COMPANION_VERSION does not match the companion checkout")
    output = book / "dist" / book_version
    output.mkdir(parents=True, exist_ok=True)
    from repo_sync import book_digest, public_digest
    book_inputs = book_digest(book)
    companion_inputs = public_digest()
    results = {"book_version": book_version, "companion_version": companion_version}
    if args.format in ("all", "paperback"):
        results["paperback"] = paperback(book, output)
    if args.format in ("all", "epub"):
        results["epub"] = epub(book, output)
    if book_inputs != book_digest(book) or companion_inputs != public_digest():
        raise ValueError("Publication inputs changed during the build; rerun from a stable source tree")
    for kind in ("paperback", "epub"):
        if kind in results:
            results[kind]["book_source_sha256"] = book_inputs
            results[kind]["companion_source_sha256"] = companion_inputs
            (output / (kind + "-report.json")).write_text(json.dumps(results[kind], indent=2) + "\n")
        elif (output / (kind + "-report.json")).exists():
            old = json.loads((output / (kind + "-report.json")).read_text())
            if old.get("book_source_sha256") != book_inputs or old.get("companion_source_sha256") != companion_inputs:
                raise ValueError(f"Existing {kind} output uses older inputs; rebuild with --format all")
    (output / "README.md").write_text(f"""# Publication proof {book_version}

Companion release: v{companion_version}.

- `symmetry-paperback-interior.pdf`: 7 × 10-inch, 11-point, black-and-white
  interior on white paper, no bleed. See `paperback-report.json` for the final
  even page count and automated PDF checks.
- `symmetry-kindle-mathml.epub`: reflowable EPUB with native MathML, chapter and
  section navigation, bibliography, linked indexes, and the supplied cover.
  `kindle-cover.png` is the separate cover image for the KDP listing.
  See `epub-report.json`
  and `epubcheck.txt` for validation results.
- `cover-layout-guide.pdf`, `cover-parameters.md`, `cover-parameters.json`:
  dimensioned back–spine–front guide and geometry for this exact interior.
- `release-manifest.json`: input fingerprints and artifact SHA-256 hashes.

The cover guide is not upload artwork. Use a separately prepared full cover
matched to this interior; see the private publishing/cover/README.md.
Kindle Previewer and a KDP physical proof remain the device and manufacturing
checks before publication. No Amazon account upload has been performed.
""")
    artifacts = {}
    for path in sorted(output.iterdir()):
        if path.is_file() and path.name != "release-manifest.json":
            artifacts[path.name] = {"bytes": path.stat().st_size,
                                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    manifest = {"book_version": book_version, "companion_version": companion_version,
                "book_tag": "v" + book_version, "companion_tag": "v" + companion_version,
                "book_source_sha256": book_inputs, "companion_source_sha256": companion_inputs,
                "artifacts": artifacts}
    (output / "release-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, RuntimeError, OSError) as error:
        sys.exit(str(error))
