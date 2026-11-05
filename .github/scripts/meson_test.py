#!/usr/bin/env python3
# Runs 'meson test' with the given arguments.
#
# Meson starts each test with a preexec_fn that calls setsid(), which makes
# Python fork the whole meson process instead of using vfork. This takes a
# large part of the test step, since meson starts the tests one at a time.
# start_new_session also calls setsid() and allows vfork. Not for --gdb and
# --interactive, which need the preexec_fn of meson.

import asyncio
import os
import shutil
import sys

args = ['test'] + sys.argv[1:]
try:
    from mesonbuild import mesonmain
except ImportError:
    os.execvp('meson', ['meson'] + args)

create_subprocess_exec = asyncio.create_subprocess_exec


async def create_subprocess_exec_vfork(*cmd, preexec_fn=None, **kwargs):
    if preexec_fn is not None:
        kwargs['start_new_session'] = True
    return await create_subprocess_exec(*cmd, **kwargs)


asyncio.create_subprocess_exec = create_subprocess_exec_vfork
sys.exit(mesonmain.run(args, shutil.which('meson') or sys.argv[0]))
