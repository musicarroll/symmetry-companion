#!/usr/bin/env python3
"""Check or copy bibliography (book -> public) and figures (public -> book)."""
import argparse
import shutil
import sys

from repo_sync import ROOT, book_root


def artifact_pairs(public, book):
    yield book / "references.bib", public / "references.bib"
    figures = public / "results/figures"
    for source in sorted(figures.rglob("*")):
        if source.is_file():
            yield source, book / "results/figures" / source.relative_to(figures)


def synchronize(public, book, write=False):
    stale = []
    copied = 0
    for source, target in artifact_pairs(public, book):
        if not source.is_file():
            raise ValueError(f"Missing authoritative artifact: {source}")
        if target.is_file() and target.read_bytes() == source.read_bytes():
            continue
        if write:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            copied += 1
        else:
            stale.append(str(target))
    if stale:
        raise ValueError("Artifacts differ; inspect and run with --write:\n" + "\n".join(stale))
    return copied


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book", required=True, help="private manuscript checkout")
    parser.add_argument("--write", action="store_true", help="copy changed artifacts in the documented directions")
    args = parser.parse_args()
    count = synchronize(ROOT, book_root(args.book), args.write)
    print(f"Synchronized {count} changed artifacts." if args.write else "Bibliography and book figure copies are synchronized.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        sys.exit(str(error))
