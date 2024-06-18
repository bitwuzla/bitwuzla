FROM registry.gitlab.com/sosy-lab/benchmarking/competition-scripts/user:latest AS base

RUN apt-get update && apt-get install -y \
  autoconf \
  build-essential \
#  meson \
#  ninja-build \
  python3

RUN pip3 install meson ninja

WORKDIR /src

# Compile binary
FROM base as binary-builder
COPY bitwuzla-src.tar.xz .
RUN tar --strip-components=1 -xf bitwuzla-src.tar.xz
RUN meson setup build --buildtype release --force-fallback-for=cadical,gmp,symfpu
RUN cd build && ninja

# Copy bitwuzla binary
FROM scratch as bitwuzla_binary
COPY --from=binary-builder /src/build/src/main/bitwuzla /bin/
ENTRYPOINT [ "/bin/bitwuzla" ]
