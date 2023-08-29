###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https:#github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https:#github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import pytest

from bitwuzla import *

if __name__ == '__main__':

    # First, create a Bitwuzla options instance.
    options = Options()

    # We will parse example file `smt2/quickstart.smt2`.
    # Create parser instance.
    parser = Parser(options, "../smt2/quickstart.smt2")

    # Now parse the input file.
    err_msg = parser.parse()
    # We expect no error to occur.
    assert not err_msg

    # Now we retrieve the set of asserted formulas and print them.
    assertions = parser.bitwuzla().get_assertions()
    print('Assertions:')
    print('{')
    for a in assertions:
        print(f' {a}')
    print('}')
