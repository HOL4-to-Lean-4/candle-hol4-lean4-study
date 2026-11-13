# Pinned HOL4 build environment for the Candle study.
# Build context: the repository root (see scripts/build.sh / build.ps1).
# Poly/ML and HOL4 are built from vendor/ with no network clone.
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential libgmp-dev python3 time \
    && rm -rf /var/lib/apt/lists/*

# Poly/ML v5.9.2 (commit 4557554077078decce4ce5f90da00a713cfc32e4)
COPY vendor/polyml /opt/polyml-src
RUN cd /opt/polyml-src \
    && ./configure --prefix=/usr --enable-intinf-as-int \
    && make -j"$(nproc)" && make compiler && make install \
    && cd / && rm -rf /opt/polyml-src

# HOL4 master at commit 9783a49979c94c401ff8c0e51b2eefae7ea95ae3
COPY vendor/HOL /opt/HOL
RUN cd /opt/HOL \
    && poly --script tools/smart-configure.sml \
    && bin/build

# HOL example directories the package uses (package/holproject.toml, external_includes).
RUN for d in examples/pl-semantics/lprefix_lub examples/machine-code/hoare-triple \
             examples/formal-languages/context-free examples/algorithms; do \
      (cd /opt/HOL/$d && /opt/HOL/bin/Holmake) || exit 1; \
    done

# The package is mounted at /work; build it with
#   docker run --rm -v <repo>/package:/work -w /work/candle/standard/semantics
#     candle-hol4:pinned Holmake holSoundnessTheory
ENV HOLDIR=/opt/HOL
ENV CAKEMLDIR=/work
ENV PATH=/opt/HOL/bin:$PATH
WORKDIR /work
