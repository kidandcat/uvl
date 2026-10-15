# Linux environment for uvl_bundle.py on hosts without GNU ld (macOS).
# Build it once from the repository root:
#
#   docker build -t uvl-bundler baremetal/tools
#
# The Lean toolchain must match lean-toolchain.
FROM ubuntu:24.04
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      gcc libc6-dev binutils python3 curl ca-certificates git zstd && \
    rm -rf /var/lib/apt/lists/*
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
    sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0
ENV PATH=/root/.elan/bin:$PATH
# elan installs toolchains lazily; fetch it into the image.
RUN lean --version
