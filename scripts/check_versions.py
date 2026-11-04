#!/usr/bin/env python3
"""Check companion version metadata and an optional paired private book."""
import argparse
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def read_version(path):
    value = path.read_text().strip()
    if not re.fullmatch(r"\d+\.\d+\.\d+", value):
        raise ValueError(f"Invalid MAJOR.MINOR.PATCH version: {path}")
    return value


def check_versions(public, book=None, require_tag=False):
    companion = read_version(public / "VERSION")
    lake = re.search(r'^version\s*=\s*"([^"]+)"', (public / "lakefile.toml").read_text(), re.M)
    if not lake or lake[1] != companion:
        raise ValueError("VERSION and lakefile.toml version disagree")
    versions = {public: companion}
    if book is not None:
        if read_version(book / "COMPANION_VERSION") != companion:
            raise ValueError("Book COMPANION_VERSION does not match the companion checkout")
        versions[book] = read_version(book / "VERSION")
    if require_tag:
        for root, number in versions.items():
            tag = subprocess.check_output(["git", "rev-parse", f"v{number}^{{commit}}"], cwd=root, text=True).strip()
            head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            if tag != head:
                raise ValueError(f"v{number} does not identify the current commit in {root}")
    return {str(root): value for root, value in versions.items()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book", type=Path)
    parser.add_argument("--require-tag", action="store_true")
    args = parser.parse_args()
    try:
        result = check_versions(ROOT, args.book.resolve() if args.book else None, args.require_tag)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, str(error) + "\n")
    print("Versions consistent: " + ", ".join(f"{Path(k).name} {v}" for k, v in result.items()))
