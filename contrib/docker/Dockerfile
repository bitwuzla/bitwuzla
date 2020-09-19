##############################################################################
#                                                                            #
# *Notice*                                                                   #
#                                                                            #
# This Docker image is based on Alpine Linux, which is a `musl` libc-based   #
# distribution, and not `glibc`-based (e.g., like Ubuntu or Debian).         #
#                                                                            #
# To make Boolector work under `musl`, Boolector is "patched" using the      #
# Windows patch-sets. These patch-sets (predominantly) are used to restrict  #
# Boolector to the minimum amount of libc that is exposed via MinGW.         #
#                                                                            #
# For our purposes, restricting Boolector to the MinGW runtime also means    #
# that Boolector builds and runs under `musl`.                               #
#                                                                            #
# Any references to patching "for Windows" should be read as "patching for   #
# a minimal libc".                                                           #
#                                                                            #
##############################################################################

FROM alpine:3.9

MAINTAINER Andrew V. Jones "andrew.jones@vector.com"

ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8

#
# Deps needed only for build
#
ENV BUILD_DEPS \
    alpine-sdk \
    cmake \
    cython \
    cython-dev \
    g++ \
    gcc \
    git \
    make \
    python-dev \
    python3 \
    sed \
    wget

#
# Deps needed for running afterwards
#
ENV PERSISTENT_DEPS \
    bash \
    libgcc \
    libstdc++ \
    python

#
# Which repo to build from?
#
ARG UPSTREAM=https://github.com/Boolector/boolector/archive

#
# Which Boolector branch to build?
#
ARG BRANCH=master

#
# Steps to build-up our image
#
RUN apk upgrade --update && \
    apk add --no-cache --virtual .build-deps $BUILD_DEPS && \
    apk add --no-cache --virtual .persistent-deps $PERSISTENT_DEPS && \
    # \
    # Musl does not provide /usr/include/sys/unistd.h, which Lingeling needs \
    # \
    echo "#include <unistd.h>" > /usr/include/sys/unistd.h && \
    #
    # Grab our Boolector tar (output is going to be "boolector-${BRANCH}".tar.gz)
    #
    wget "${UPSTREAM}/${BRANCH}.tar.gz" -O "boolector-${BRANCH}.tar.gz" && \
    tar -xzvf "boolector-${BRANCH}.tar.gz" && \
    #
    # Move to sanitized location
    #
    mv "boolector-${BRANCH}" boolector && \
    #
    # Enter source tree
    #
    cd boolector && \
    # \
    # Musl does not provide quite enough of glibc, so we pretend we're Windows \
    # \
    sed -i "s#MINGW32#Linux#g" ./contrib/setup-utils.sh && \
    # \
    # Force -fPIC for CaDiCaL
    # \
    sed -i "s#export CXXFLAGS=\"\"#export CXXFLAGS=\"-fPIC\"#g" ./contrib/setup-cadical.sh && \
    ./contrib/setup-btor2tools.sh && \
    ./contrib/setup-picosat.sh && \
    ./contrib/setup-cadical.sh && \
    ./contrib/setup-lingeling.sh && \
    ./configure.sh --python --shared && \
    cd build && \
    make -j$(nproc) && \
    # \
    # Validate our build of Boolector
    # \
    ctest -j$(nproc) --output-on-failure \
    apk del .build-deps

#
# When we're in the container, we want to have PYTHONPATH to include pyboolector
#
ENV PYTHONPATH "${PYTHONPATH}:/boolector/build/lib"

#
# Entry point to allow us to run .smt2 files "from the outside"
#
ENTRYPOINT ["/boolector/build/bin/boolector"]

# EOF
