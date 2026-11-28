#!/usr/bin/env bash

set -euo pipefail

ROOT="$(pwd)"
DRY_RUN=0
QUIET=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --root)
      if [[ $# -lt 2 ]]; then
        echo "Missing value for --root" >&2
        exit 1
      fi
      ROOT="$2"
      shift 2
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    --quiet)
      QUIET=1
      shift
      ;;
    -h|--help)
      cat <<'EOF'
Usage:
  bash scripts/update_java_header_versions.sh
  bash scripts/update_java_header_versions.sh --root jacop-core
  bash scripts/update_java_header_versions.sh --dry-run
  bash scripts/update_java_header_versions.sh --dry-run --quiet

Updates text in each *.java file:
  "Copyright (C) 2000-2008" -> "Copyright (C) 2000-2026"
  "@version 4.9" -> "@version 4.10"
  "@version 4.10" -> "@version 5.0"
EOF
      exit 0
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 1
      ;;
  esac
done

if ! command -v perl >/dev/null 2>&1; then
  echo "This script requires perl, but it was not found in PATH." >&2
  exit 1
fi

if [[ ! -d "$ROOT" ]]; then
  echo "Root directory does not exist: $ROOT" >&2
  exit 1
fi

changed=0

while IFS= read -r -d '' file; do
  if perl -0777 -e '
      my $f = shift;
      open my $fh, q{<}, $f or exit 2;
      local $/;
      my $text = <$fh>;
      close $fh;
      my $updated = $text;
      $updated =~ s/Copyright \(C\) 2000-2008/Copyright (C) 2000-2026/g;
      $updated =~ s/\@version 4\.9/\@version 4.10/g;
      $updated =~ s/\@version 4\.10/\@version 5.0/g;
      exit($updated ne $text ? 0 : 1);
    ' "$file"; then
    changed=$((changed + 1))
    if [[ "$QUIET" -eq 0 ]]; then
      printf '%s\n' "$file"
    fi

    if [[ "$DRY_RUN" -eq 0 ]]; then
      perl -0777 -i -pe '
        s/Copyright \(C\) 2000-2008/Copyright (C) 2000-2026/g;
        s/\@version 4\.9/\@version 4.10/g;
        s/\@version 4\.10/\@version 5.0/g;
      ' "$file"
    fi
  fi
done < <(find "$ROOT" -type f -name '*.java' -print0)

if [[ "$DRY_RUN" -eq 1 ]]; then
  printf '%s file(s) would be updated.\n' "$changed"
else
  printf '%s file(s) updated.\n' "$changed"
fi
