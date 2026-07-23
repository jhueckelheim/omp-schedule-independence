#!/bin/sh
# Build the schedule-independence proof development.
#
# These proofs are stated against the ClightOMP formal semantics of C-with-OpenMP
# (https://github.com/dkxb/ClightOMP), and use its logical path
#   VST.concurrency.openmp_sem.sched_indep
# so they must be compiled inside a built ClightOMP checkout.
#
# Usage:
#   ./build.sh /path/to/ClightOMP
#
# where /path/to/ClightOMP is a ClightOMP checkout that has already been built
# (see README.md; in particular concurrency/openmp_sem/HybridMachine.vo must
# exist). This script copies src/*.v into <ClightOMP>/sched_indep/ and compiles
# them in dependency order. It does not modify any upstream ClightOMP file.
set -e

CLIGHTOMP="$1"
if [ -z "$CLIGHTOMP" ]; then
  echo "usage: ./build.sh /path/to/ClightOMP" >&2
  exit 2
fi
if [ ! -f "$CLIGHTOMP/_CoqProject" ]; then
  echo "error: $CLIGHTOMP/_CoqProject not found; is this a built ClightOMP checkout?" >&2
  exit 2
fi

HERE="$(cd "$(dirname "$0")" && pwd)"
DEST="$CLIGHTOMP/sched_indep"
mkdir -p "$DEST"
cp "$HERE"/src/*.v "$DEST"/

# Prefer an opam switch named ClightOMP if present; otherwise use coqc on PATH.
COQC="coqc"
if command -v opam >/dev/null 2>&1 && opam switch list 2>/dev/null | grep -q ClightOMP; then
  COQC="opam exec --switch=ClightOMP -- coqc"
fi

cd "$CLIGHTOMP"
FLAGS="$(cat _CoqProject) -Q sched_indep VST.concurrency.openmp_sem.sched_indep"

for f in ObsEquiv ClassPredicates ChunkIndep Reduction StepFraming \
         DryStepFraming OstepFraming OstepRun SetN EvElimFrame \
         HardenedConfluence SourceToTrace DRF DRFExtended PrivateOracle; do
  echo "COQC sched_indep/$f.v"
  $COQC $FLAGS "sched_indep/$f.v"
done

echo "OK: schedule-independence development built."
