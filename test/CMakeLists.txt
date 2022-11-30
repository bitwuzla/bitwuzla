###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

#add_subdirectory(unit)
add_subdirectory(regress)

if(PYTHON)
  add_subdirectory(python)
endif()
