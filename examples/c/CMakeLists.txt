###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

set (BZLA_EXAMPLES_API
  checksatassuming
  options
  pushpop
  quickstart
  unsatassumptions
  unsatcore
  )

foreach(example ${BZLA_EXAMPLES_API})
  bzla_add_example(${example} "" "c" "c")
endforeach()
