#!/bin/sh
# Rebuild the reduced package from a clean checkout.
#   scripts/build.sh native   build Poly/ML and HOL4 from vendor/ into _build/, then the package (Linux or WSL)
#   scripts/build.sh docker   build the docker image from vendor/, then the package inside it
# The package is built with CAKEMLDIR=<repo>/package and HOLDIR=<built vendor HOL>, by
# running $HOLDIR/bin/Holmake holSoundnessTheory in package/candle/standard/semantics.
# The HOL4 build also builds the HOL example directories that package/holproject.toml
# lists (HOL_EXAMPLES below).
# Timings are written to logs/build-*.log.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
MODE=${1:-native}
mkdir -p "$ROOT/logs"
stamp() { date -u +%Y-%m-%dT%H:%M:%SZ; }
HOL_EXAMPLES="examples/pl-semantics/lprefix_lub examples/machine-code/hoare-triple examples/formal-languages/context-free examples/algorithms"
SEM=candle/standard/semantics

case "$MODE" in
native)
  B="$ROOT/_build"; mkdir -p "$B"
  if [ ! -x "$B/polyml/bin/poly" ]; then
    echo "polyml start $(stamp)" >> "$ROOT/logs/build-native.log"
    rm -rf "$B/polyml-src"; cp -R "$ROOT/vendor/polyml" "$B/polyml-src"
    (cd "$B/polyml-src" && ./configure --prefix="$B/polyml" --enable-intinf-as-int \
       && make -j"$(nproc)" && make compiler && make install)
    echo "polyml end $(stamp)" >> "$ROOT/logs/build-native.log"
  fi
  export PATH="$B/polyml/bin:$PATH" LD_LIBRARY_PATH="$B/polyml/lib:${LD_LIBRARY_PATH:-}"
  if [ ! -x "$B/HOL/bin/Holmake" ]; then
    echo "hol start $(stamp)" >> "$ROOT/logs/build-native.log"
    rm -rf "$B/HOL"; cp -R "$ROOT/vendor/HOL" "$B/HOL"
    (cd "$B/HOL" && poly --script tools/smart-configure.sml && bin/build)
    echo "hol end $(stamp)" >> "$ROOT/logs/build-native.log"
  fi
  if [ ! -f "$B/HOL/.examples-built" ]; then
    echo "hol-examples start $(stamp)" >> "$ROOT/logs/build-native.log"
    for d in $HOL_EXAMPLES; do (cd "$B/HOL/$d" && "$B/HOL/bin/Holmake"); done
    touch "$B/HOL/.examples-built"
    echo "hol-examples end $(stamp)" >> "$ROOT/logs/build-native.log"
  fi
  echo "package start $(stamp)" >> "$ROOT/logs/build-native.log"
  (cd "$ROOT/package/$SEM" && HOLDIR="$B/HOL" CAKEMLDIR="$ROOT/package" \
     "$B/HOL/bin/Holmake" holSoundnessTheory)
  echo "package end $(stamp)" >> "$ROOT/logs/build-native.log"
  ;;
docker)
  echo "image start $(stamp)" >> "$ROOT/logs/build-docker.log"
  docker build -f "$ROOT/docker/Dockerfile" -t candle-hol4:pinned "$ROOT"
  echo "image end $(stamp)" >> "$ROOT/logs/build-docker.log"
  echo "package start $(stamp)" >> "$ROOT/logs/build-docker.log"
  # The image sets HOLDIR=/opt/HOL and CAKEMLDIR=/work and has the examples built.
  docker run --rm -v "$ROOT/package:/work" -w "/work/$SEM" candle-hol4:pinned \
    Holmake holSoundnessTheory
  echo "package end $(stamp)" >> "$ROOT/logs/build-docker.log"
  ;;
*) echo "usage: $0 [native|docker]" >&2; exit 2 ;;
esac
