#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# check-lean-proofs.sh — a proof gate that can actually fail.
#
# Replaces the previous gate:
#
#     ! grep -r "sorry\|admit" src/
#
# which was substring-based and therefore wrong in both directions. It fired on
# every one of these *legitimate* uses already in this repo:
#
#   src/GqlDt/TypeInference.lean:162   | admit : ProofStrategy   <- constructor DECLARATION
#   src/GqlDt/TypeInference.lean:171   | _ => .admit             <- constructor USE
#   src/GqlDt/TypeInference.lean:179   | .admit => "sorry"       <- string literal
#   src/GqlDt/TypeSafeQueries.lean:90  --   ... := by sorry      <- commented out
#   src/GqlDt/Lexer.lean:230           ("sorry", .kwSorry)       <- lexer keyword table
#
# ...while a genuine `theorem foo : P := by sorry` is what we actually care about.
#
# Two modes, because only one of them is authoritative:
#
#   --build-log FILE   AUTHORITATIVE. Lean itself emits "declaration uses 'sorry'"
#                      for any declaration whose proof is incomplete, including
#                      ones no regex could find (e.g. sorry reached through a
#                      tactic block or an unfolded definition).
#
#   (default)          FAST PRE-CHECK. Comment- and string-aware textual scan.
#                      Catches the common case without needing a full build, but
#                      it is a heuristic — never treat a green pre-check as proof.
#
# Exit 0 = clean, 1 = incomplete proofs found.

set -euo pipefail

SRC_DIR="${SRC_DIR:-src}"
MODE="textual"
BUILD_LOG=""

while [ $# -gt 0 ]; do
  case "$1" in
    --build-log) MODE="build-log"; BUILD_LOG="${2:-}"; shift 2 ;;
    --src)       SRC_DIR="${2:-src}"; shift 2 ;;
    -h|--help)   sed -n '3,40p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

# ---------------------------------------------------------------- build-log mode
if [ "$MODE" = "build-log" ]; then
  if [ ! -f "$BUILD_LOG" ]; then
    echo "❌ build log not found: $BUILD_LOG" >&2
    echo "   Refusing to report success from a log that does not exist." >&2
    exit 1
  fi
  # Lean's own wording; match loosely so a phrasing change surfaces as a hit
  # rather than a silent pass.
  if grep -nE "uses '?sorry'?|sorryAx|declaration uses" "$BUILD_LOG"; then
    echo "❌ Lean reported incomplete proofs (see matches above)."
    exit 1
  fi
  echo "✅ Lean reported no incomplete proofs in $BUILD_LOG"
  exit 0
fi

# ----------------------------------------------------------------- textual mode
if [ ! -d "$SRC_DIR" ]; then
  echo "❌ source directory not found: $SRC_DIR" >&2
  exit 1
fi

found=0

# Strip, in order: /- block comments -/, "string literals", -- line comments.
# Then a bare `sorry`/`admit` token is a proof-position use, EXCEPT when it is
#   .admit          — constructor/field access
#   | admit : T     — constructor declaration in an inductive
strip_and_scan() {
  local file="$1"
  awk -v FNAME="$file" '
    BEGIN { inblock = 0 }
    {
      line = $0

      # /- ... -/ block comments, including nested-on-one-line cases
      while (inblock) {
        p = index(line, "-/")
        if (p == 0) { line = ""; break }
        line = substr(line, p + 2); inblock = 0
      }
      while ((s = index(line, "/-")) > 0) {
        rest = substr(line, s + 2)
        e = index(rest, "-/")
        if (e == 0) { line = substr(line, 1, s - 1); inblock = 1; break }
        line = substr(line, 1, s - 1) " " substr(rest, e + 2)
      }

      gsub(/"[^"]*"/, "\"\"", line)   # string literals
      sub(/--.*$/, "", line)          # line comments

      if (line ~ /(^|[^A-Za-z0-9_.])(sorry|admit)([^A-Za-z0-9_]|$)/) {
        if (line ~ /^[[:space:]]*\|[[:space:]]*(sorry|admit)[[:space:]]*:/) next  # ctor decl
        printf "%s:%d: %s\n", FNAME, FNR, $0
      }
    }
  ' "$file"
}

while IFS= read -r f; do
  out="$(strip_and_scan "$f")"
  if [ -n "$out" ]; then
    printf '%s\n' "$out"
    found=1
  fi
done < <(find "$SRC_DIR" -name '*.lean' -type f | sort)

if [ "$found" -ne 0 ]; then
  echo
  echo "❌ Proof-position 'sorry'/'admit' found (see above)."
  echo "   Invariant (0-AI-MANIFEST.a2ml): \"No sorry in Lean 4 proofs — hard invariant\"."
  exit 1
fi

echo "✅ No proof-position sorry/admit in $SRC_DIR/"
echo "   NOTE: heuristic pre-check only. The authoritative gate is"
echo "         $0 --build-log <lake-build-output>"
exit 0
