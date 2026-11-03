#!/bin/sh
set -eu
slide_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$slide_dir/../scripts/check_slide_sync.py" "$@"
