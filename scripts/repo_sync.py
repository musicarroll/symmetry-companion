"""Shared paths and content digests for the public/private review workflow."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def digest(root, paths):
    """Hash relative names and contents, independent of checkout location."""
    result = hashlib.sha256()
    for path in sorted(set(paths)):
        result.update(path.relative_to(root).as_posix().encode() + b"\0")
        result.update(hashlib.sha256(path.read_bytes()).digest())
    return result.hexdigest()


def public_digest(root=ROOT):
    paths = [root / name for name in (
        "AGENTS.md", "README.md", "README_computational.md", "SYNC.md",
        "GITHUB_SETUP.md", "references.bib", "requirements.txt", "requirements-publication.txt",
        "VERSION", "CHANGELOG.md", "lakefile.toml",
        "lake-manifest.json", "lean-toolchain", "SymmetryMonograph.lean")]
    suffixes = {".lean", ".py", ".md", ".tex", ".csv", ".json", ".txt",
                ".png", ".pdf", ".dot", ".svg", ".jpg", ".jpeg", ".webp"}
    for directory in ("SymmetryMonograph", "lean", "doc", "src", "scripts", "results", "tests"):
        paths.extend(path for path in (root / directory).rglob("*")
                     if path.is_file() and path.suffix in suffixes)
    paths.extend(path for path in (root / "slides").rglob("*")
                 if path.is_file() and path.suffix in {".tex", ".md", ".sh"})
    paths.append(root / "slides/Makefile")
    paths.extend((root / ".github/workflows").glob("*.yml"))
    return digest(root, paths)


def book_root(path):
    book = Path(path).resolve()
    if book == ROOT or not (book / "main.tex").is_file():
        raise ValueError(f"Expected a separate private manuscript checkout: {book}")
    return book


def book_digest(book):
    paths = [book / name for name in ("main.tex", "macros.tex", "references.bib", "requirements.md",
                                     "VERSION", "COMPANION_VERSION")]
    paths.extend((book / "chapters").rglob("*.tex"))
    paths.extend((book / "doc").glob("*.md"))
    paths.extend(path for path in (book / "publishing").rglob("*")
                 if path.is_file() and path.suffix in {".tex", ".cfg", ".mk4", ".css", ".json"})
    metadata_path = book / "publishing/metadata.json"
    if metadata_path.exists():
        cover = json.loads(metadata_path.read_text()).get("cover_image")
        if cover:
            cover_path = Path(cover)
            if cover_path.is_absolute() or ".." in cover_path.parts:
                raise ValueError("Cover image must be relative to the private book checkout")
            paths.append(book / cover_path)
    return digest(book, paths)
