#!/usr/bin/env python3
"""Check reviewed public sources, optionally including the private manuscript."""
import argparse
import json
import sys

from repo_sync import ROOT, book_digest, book_root, public_digest


def check_or_write(path, content, write):
    if write:
        path.write_text(content)
    elif not path.is_file() or path.read_text() != content:
        raise ValueError(f"Sources changed since slide review: {path.name}. "
                         "Review affected slides and SOURCE_MAP.md, then refresh-snapshot.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book", help="also check a private manuscript checkout")
    parser.add_argument("--write", action="store_true", help="record an already completed editorial review")
    args = parser.parse_args()
    book = book_root(args.book) if args.book else None
    current = public_digest() + "\n"
    reviewed = (json.dumps({"schema": 1, "manuscript_sha256": book_digest(book)},
                           indent=2) + "\n") if book else None
    check_or_write(ROOT / "slides/source.sha256", current, args.write)
    if book:
        check_or_write(book / "companion-review.json", reviewed, args.write)
    print("Slide sources reviewed and recorded." if args.write else "Public slide sources match the review snapshot.")
    if book:
        print("Private manuscript review recorded." if args.write else "Private manuscript matches the review snapshot.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        sys.exit(str(error))
