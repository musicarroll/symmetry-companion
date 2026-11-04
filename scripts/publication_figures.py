"""Prepare readable paperback panels from unchanged recorded experiment data."""
from pathlib import Path
import re
import runpy
import shutil
import sys


def braced(text, start):
    depth = 0
    for position in range(start, len(text)):
        if text[position] == "{" and (position == 0 or text[position - 1] != "\\"):
            depth += 1
        elif text[position] == "}" and (position == 0 or text[position - 1] != "\\"):
            depth -= 1
            if depth == 0:
                return text[start + 1:position], position + 1
    raise ValueError("Unclosed caption argument")


def split_panels(text):
    def replace(match):
        figure = match[0]
        images = re.findall(r"\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}", figure)
        if len(images) < 2:
            return figure
        cap = re.search(r"\\caption\s*\{", figure)
        label = re.search(r"\\label\{([^}]+)\}", figure)
        if not cap or not label:
            raise ValueError("A split figure requires an explicit caption and label")
        caption, _ = braced(figure, cap.end() - 1)
        output = []
        for number, image in enumerate(images, 1):
            continued = "\\ContinuedFloat\n" if number > 1 else ""
            if number == 1:
                description = "\\caption{" + caption + f" (Panel {number} of {len(images)}.)" + "}\n\\label{" + label[1] + "}"
            else:
                description = ("\\caption[]{Continued: panel " + str(number) + " of " + str(len(images)) +
                               "; see the caption for Figure~\\ref{" + label[1] + "}.}")
            output.append("\\begin{figure}[p]\n" + continued + "\\centering\n" +
                          "\\includegraphics[width=0.95\\textwidth,height=0.70\\textheight,keepaspectratio]{" + image + "}\n" +
                          description + "\n\\end{figure}\n")
        return "\n".join(output)
    return re.sub(r"\\begin\{figure\}(?:\[[^]]*\])?.*?\\end\{figure\}", replace, text, flags=re.S)


def prepare_figures(public, work):
    widths = {}
    for path in (work / "chapters").rglob("*.tex"):
        source = split_panels(path.read_text())
        path.write_text(source)
        for options, filename in re.findall(r"\\includegraphics\[([^]]+)\]\{([^}]+\.png)\}", source):
            width = re.search(r"width=([0-9.]+)\\textwidth", options)
            if width:
                printed = float(width[1]) * 5.5
                key = Path(filename).name
                widths[key] = min(widths.get(key, printed), printed)
    shutil.copytree(public / "src", work / "src", ignore=shutil.ignore_patterns("__pycache__"))
    shutil.copytree(public / "results/data", work / "results/data")
    (work / "scripts").mkdir()
    for name in ("plot_two_block_results.py", "plot_large_scale_phase_results.py", "plot_reference_group_phase_results.py"):
        shutil.copy2(public / "scripts" / name, work / "scripts" / name)
    import matplotlib
    matplotlib.use("Agg")
    from matplotlib.figure import Figure
    from matplotlib.text import Text
    original = Figure.savefig
    def save(self, filename, *args, **kwargs):
        printed = widths.get(Path(filename).name, 5.225)
        minimum = 7.6 * self.get_figwidth() / printed
        for obj in self.findobj(match=Text):
            if obj.get_text().strip():
                obj.set_fontsize(max(obj.get_fontsize(), minimum))
        self.tight_layout()
        kwargs["dpi"] = max(400, kwargs.get("dpi", 400))
        kwargs["facecolor"] = "white"
        return original(self, filename, *args, **kwargs)
    Figure.savefig = save
    try:
        for script in sorted((work / "scripts").glob("plot_*.py")):
            runpy.run_path(str(script), run_name="__main__")
    finally:
        Figure.savefig = original
    return widths
