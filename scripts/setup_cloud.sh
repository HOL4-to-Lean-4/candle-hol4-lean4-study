#!/bin/sh
# Set up a Linux cloud session (Ubuntu 24.04, 4 cores) for the study and the CakeML migration.
#   sh scripts/setup_cloud.sh [hol] [lean]     (no argument: both)
# hol:  builds Poly/ML, HOL4 9783a499 and the Candle package from vendor/ into _build/
#       (scripts/build.sh native). About 20 min (27 Nov 2026). Then tools/hol4_query/hol4q.py works.
# lean: installs elan and Lean 4.28.0. If the network allows releases.lean-lang.org or GitHub
#       release downloads, elan fetches it in about a minute. Otherwise Lean is built from the
#       v4.28.0 source tag (git clone works) and linked as the elan toolchain; that takes about
#       45 min on 4 cores.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WHAT=${*:-hol lean}
SUDO=""; [ "$(id -u)" = 0 ] || SUDO=sudo
$SUDO apt-get install -y libgmp-dev libuv1-dev pkg-config cmake clang >/dev/null 2>&1 || {
  $SUDO apt-get update -qq && $SUDO apt-get install -y libgmp-dev libuv1-dev pkg-config cmake clang; }

for w in $WHAT; do case "$w" in
hol)
  sh "$ROOT/scripts/build.sh" native
  ;;
lean)
  if [ ! -x "$HOME/.elan/bin/elan" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
    sh /tmp/elan-init.sh -y --default-toolchain none
  fi
  export PATH="$HOME/.elan/bin:$PATH"
  if elan toolchain install leanprover/lean4:v4.28.0 2>/dev/null; then
    echo "Lean 4.28.0 installed by elan"
  else
    S="$HOME/lean4-src"
    [ -d "$S" ] || git clone -q --depth 1 --branch v4.28.0 https://github.com/leanprover/lean4.git "$S"
    mkdir -p "$S/build/release"
    (cd "$S/build/release" && CC=clang CXX=clang++ cmake ../.. -DCMAKE_BUILD_TYPE=Release \
       && CC=clang CXX=clang++ make -j"$(nproc)")
    elan toolchain link leanprover/lean4:v4.28.0 "$S/build/release/stage1"
    echo "Lean 4.28.0 built from source and linked"
  fi
  ;;
*) echo "usage: $0 [hol] [lean]" >&2; exit 2 ;;
esac; done
