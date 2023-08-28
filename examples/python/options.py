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

    # Enable model generation, which expects a boolean configuration value.
    options.set(Option.PRODUCE_MODELS, True)

    # Increase the verbosity level, which expects an integer value.
    print(f'Previous verbosity level: {options.get(Option.VERBOSITY)}')
    options.set(Option.VERBOSITY, 2)
    print(f'Current verbosity level: {options.get(Option.VERBOSITY)}')

    # Now configure an option that has modes (a choice of configuration values).
    # First, query which bit-vector solver engine is set.
    print(f'Default bv solver: {options.get(Option.BV_SOLVER)}')
    # Then, select the propagation-based local search engine as solver engine.
    options.set(Option.BV_SOLVER, 'prop')
    print(f'Current engine: {options.get(Option.BV_SOLVER)}')

    # Now, create a Bitwuzla instance.
    bitwuzla = Bitwuzla(options)
    # Check sat (nothing to solve, input formula is empty).
    result = bitwuzla.check_sat()
    print('Expect: sat')
    print(f'Bitwuzla: {result}')
