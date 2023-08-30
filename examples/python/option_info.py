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

    # Set some options to illustrate current vs default value.
    options.set(Option.PRODUCE_MODELS, True)
    options.set(Option.VERBOSITY, 2)
    options.set(Option.BV_SOLVER, 'prop')

    # Then iterate over all available configuration options and extract info.
    for opt in Option:
        info = OptionInfo(options, opt)
        print(f'  long name:   {info.lng()}')
        print(f'  short name:  {info.shrt() if info.shrt() else "-"}')
        print('  kind:        ', end = '')
        if info.kind() == OptionInfoKind.BOOL:
            print('bool')
            print('  values:')
            print(f'  + current:   {info.cur()}')
            print(f'  + default:   {info.dflt()}')
        elif info.kind() == OptionInfoKind.NUMERIC:
            print('numeric')
            print('  values:')
            print(f'  + current:   {info.cur()}')
            print(f'  + default:   {info.dflt()}')
            print(f'  + min:       {info.min()}')
            print(f'  + max:       {info.max()}')
        else:
            print('modes')
            print('  values:')
            print(f'  + current:   {info.cur()}')
            print(f'  + default:   {info.dflt()}')
            print(f'  + modes:     {info.modes()}')
        print(f'  description: {info.description()}\n')
