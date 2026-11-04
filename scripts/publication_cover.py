"""Compute KDP white-paper cover geometry from the actual interior page count."""
from decimal import Decimal
import json
from pathlib import Path
import shutil
import subprocess


def cover_geometry(pages, version):
    if pages < 24 or pages % 2:
        raise ValueError("Cover geometry requires an even paperback page count of at least 24")
    spine = Decimal(pages) * Decimal("0.002252")
    width = Decimal("14.25") + spine
    return {"book_version": version, "pages": pages, "trim_width_inches": 7,
            "trim_height_inches": 10, "ink": "black and white", "paper": "white",
            "spine_factor_inches_per_page": "0.002252", "spine_width_inches": float(spine),
            "bleed_inches": .125, "full_cover_width_inches": float(width),
            "full_cover_height_inches": 10.25,
            "full_cover_width_mm": float(width * Decimal("25.4")),
            "full_cover_height_mm": 260.35,
            "full_cover_pixels_at_300_dpi": [int((width * 300).to_integral_value(rounding="ROUND_CEILING")), 3075],
            "source": "https://kdp.amazon.com/en_US/help/topic/G201953020"}


def write_cover_guide(output, work, pages, version):
    spec = cover_geometry(pages, version)
    (output / "cover-parameters.json").write_text(json.dumps(spec, indent=2) + "\n")
    spine = spec["spine_width_inches"]
    width = spec["full_cover_width_inches"]
    front = 7.125 + spine
    guide = work / "cover-guide"
    guide.mkdir(exist_ok=True)
    source = r"""\documentclass[tikz,border=0pt]{standalone}
\usepackage{tikz}
\begin{document}
\begin{tikzpicture}[x=1in,y=1in,font=\sffamily]
\path[use as bounding box] (0,0) rectangle (WIDTH,10.25);
\clip (0,0) rectangle (WIDTH,10.25);
\fill[gray!12] (0,0) rectangle (WIDTH,10.25);
\fill[white] (.125,.125) rectangle (RIGHT,10.125);
\draw[red,dashed] (.125,.125) rectangle (RIGHT,10.125);
\draw[blue] (7.125,.125)--(7.125,10.125);
\draw[blue] (FRONT,.125)--(FRONT,10.125);
\draw[gray,dotted] (.375,.375) rectangle (6.875,9.875);
\draw[gray,dotted] (FRONTSAFE,.375) rectangle (FRONTRIGHT,9.875);
\draw[gray,dotted] (SPINESAFE,.125)--(SPINESAFE,10.125);
\draw[gray,dotted] (SPINESAFERIGHT,.125)--(SPINESAFERIGHT,10.125);
\node[align=center,text width=5.8in] at (3.625,7.0) {
  \Large BACK COVER\\[1em]\normalsize 7\,in $\times$ 10\,in trim\\
  Layout guide for book version VERSION\\[1em]
  Back-cover description and author information go here.\\
  Remove all guide lines and labels from the final cover.};
\node[align=center,text width=5.8in] at (FRONTCENTER,7.0) {
  \Large Front cover\\[1em]\normalsize 7\,in $\times$ 10\,in trim\\
  Replace with the final high-resolution artwork and typography.\\[1em]
  This guide is not a cover file to upload to KDP.};
\node[rotate=90,align=center,font=\sffamily\small] at (SPINECENTER,5.125)
  {Spine: SPINE\,in --- PAGES pages, black ink / white paper};
\draw (4.625,.375) rectangle (6.625,1.575);
\node[align=center,font=\sffamily\small] at (5.625,.975)
  {Barcode reserve\\verify final KDP template};
\node[align=center] at (3.625,3.5) {Full spread including bleed:\\
  WIDTH\,in $\times$ 10.25\,in\\0.125\,in outer bleed};
\end{tikzpicture}
\end{document}
"""
    replacements = {"WIDTH": f"{width:.6f}", "RIGHT": f"{width-.125:.6f}",
                    "FRONT": f"{front:.6f}", "FRONTSAFE": f"{front+.25:.6f}",
                    "FRONTRIGHT": f"{width-.375:.6f}", "FRONTCENTER": f"{front+3.5:.6f}",
                    "SPINECENTER": f"{7.125+spine/2:.6f}", "SPINESAFE": "7.1875",
                    "SPINESAFERIGHT": f"{front-.0625:.6f}", "SPINE": f"{spine:.6f}",
                    "PAGES": str(pages), "VERSION": version}
    for key in sorted(replacements, key=len, reverse=True):
        source = source.replace(key, replacements[key])
    (guide / "main.tex").write_text(source)
    with (guide / "build.log").open("w") as log:
        subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                       cwd=guide, stdout=log, stderr=subprocess.STDOUT, check=True)
    shutil.copy2(guide / "main.pdf", output / "cover-layout-guide.pdf")
    note = f"""# Cover parameters — book {version}

These dimensions apply to `symmetry-paperback-interior.pdf` in this release.

| Parameter | Value |
|---|---:|
| Interior page count, including final blank page | {pages} |
| Trim size | 7 × 10 inches |
| Ink / paper | Black and white / white |
| Spine | {spine:.6f} inches |
| Full back–spine–front spread, including bleed | {width:.6f} × 10.25 inches |
| Full spread at 300 DPI, rounded up | {spec['full_cover_pixels_at_300_dpi'][0]} × 3075 pixels |
| Outer bleed | 0.125 inch |

The front panel alone is 2100 × 3000 pixels at 300 DPI, before bleed allowance.
Obtain a higher-resolution source with additional background around the edges;
3000 × 4500 pixels or larger is a useful art source. Editable title and author
lettering will give more control than lettering baked into the image.

`cover-layout-guide.pdf` is a dimensioned guide, not final cover artwork. Use the
KDP cover calculator with this page count, trim, ink, and paper selection when
constructing the final spread. A changed interior page count changes the spine.

Formula: spine = pages × 0.002252 inches; spread width = 14.25 + spine inches.
Source: https://kdp.amazon.com/en_US/help/topic/G201953020
"""
    (output / "cover-parameters.md").write_text(note)
    return spec
