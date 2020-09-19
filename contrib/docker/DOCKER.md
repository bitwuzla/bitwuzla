# Using Boolector with Docker

Boolector has support for executing Boolector "input files" (e.g., `.smt2`)
files via the use of a Docker container. The base container used is Alpine
Linux.

This guide assumes that the reader is familiar with both Docker and Boolector,
and are able to install the necessary prerequisites to run Docker.


## Building the Docker image

To build the Docker image locally, you can perform the following:

```
git clone https://github.com/Boolector/boolector.git
cd boolector
docker build -t bzla/bzla -f contrib/docker/Dockerfile .
```

This will then build you a fresh Docker image, with Boolector's current master
branch built inside.

If you wish to build a version of Boolector using a different repository or a
different branch, you can specify this as part of Docker's build arguments:

```
# default arguments
UPSTREAM=https://github.com/Boolector/boolector/archive
BRANCH=master
docker build 	-t bzla/bzla \
		-f contrib/docker/Dockerfile \
		--build-arg UPSTREAM=${UPSTREAM} \
		--build-arg BRANCH=${BRANCH} .
```

## Using Docker to run `.smt2` files

As Boolector is able to read SMT-LIB v2 files via `stdin`, this means that it
is extremely easy to run Boolector against a `.smt2` file. For example:

```
# Assuming you're at the root of a Boolector clone
cat src/tests/log/modelgensmt227.smt2 | docker run -i --rm bzla/bzla -m
```

Alternatively, to see Boolector's help:

```
docker run -i --rm bzla/bzla --help
```

*Note*: the `ENTRYPOINT` specified in the Boolector `Dockerfile` tells it to run
`boolector` without any arguments. You can specify additional arguments to
Boolector via your Docker `run` command.

### Sharing files to the container

The Boolector Docker image (by default) does not have access to your "host"
file-system, which is why `cat` was necessary to pipe in the contents of your
`.smt2` file into the image.

If you wish to allow the containerised version of Boolector to able to read
files from the host file-system, you can use Docker's `-v` flag to mount a
shared volume:

```
# Assuming you're at the root of a Boolector clone
docker run --rm -i -v $(pwd):/tmp bzla/bzla -m /tmp/test/log/modelgensmt227.smt2
```

*Note*: the current working directory (`pwd`) has been mapped to `/tmp` within
the container -- hence why the file-path to the SMT2LIB file you wish to run
starts with `/tmp`.


## Using Docker to work with Boolector's Python API

The Boolector Docker image has been built with support for Boolector's Python
API, however as the entry-point for the image is to run `boolector` (the
application), then slightly more work is required to work with Python inside of
the container:

```
# Assuming you're at the root of a Boolector clone
docker run -it -v $(pwd):/tmp --entrypoint=/bin/bash bzla/bzla -i

# Note: you are now inside of the container and not the host!

# Run a Python script using pyboolector
python /tmp/examples/api/python/api_usage_examples.py

# Leave the container!
exit
```

*Note*: if you wish to use the containerised Python directly with files on your
host file-system, you can customise the `ENTRYPOINT` specified in Boolector's
`Dockerfile` (i.e., rather than running `boolector`, you can run `python`).

