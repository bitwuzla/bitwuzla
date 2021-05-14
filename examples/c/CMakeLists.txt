###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

set (BZLA_EXAMPLES_API
  quickstart
  )

foreach(example ${BZLA_EXAMPLES_API})
  bzla_add_example(${example} "" "c" "c")
endforeach()
