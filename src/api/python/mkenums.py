###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2020 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

#
# Generate enums.pxd and option.pxd includes from enums.h and option.h.
#
# Usage: mkenums.py path/to/header.h path/to/outputfile
#

import argparse
import sys
import re
from collections import OrderedDict


class BitwuzlaEnumParseError(Exception):
    def __init__(self, bzla_enum):
        self.message = "Failed to parse bitwuzla.h when handling enum '{:s}'".format(
            bzla_enum
        )
        super(Exception, self).__init__(self.message)


def extract_enums(header):
    """
    Given the file "enums.h", constructs a dictionary representing the set
    of all Bitwuzla enums and corresponding values
    """

    # We want to get only non-empty, stripped lines from our input file
    lines = [
        line
        for line in [line.strip() for line in open(header, "r").readlines()]
        if line
    ]

    # Manually create an iterator as we want to be able to move this forwards ourselves
    line_iter = iter(lines)

    # Dictionary of all our enums and their values
    bzla_enums = OrderedDict()

    # For each line ...
    value_prefix = None
    for line in line_iter:

#        prefix = re.match(r'#define EVALUE\(name\) (\w+)_##name', line)
#        if prefix:
#            assert value_prefix is None
#            value_prefix = prefix.group(1)
#
        # Do we see the _start_ of an enum?
        # Find start of enum defined as `ENUM(<enum_name>)`
        enum = re.match(r'enum ENUM\((\w+)\)', line)
        if enum:
            enum_name = enum.group(1)

            # Get the next line
            line = next(line_iter)

            # We expect this to be an opening curly, given Bitwuzla's style
            if line != "{":
                raise BitwuzlaEnumParseError(enum_name)

            # List to collect up all of the enum values for this enum
            enum_vals = []

            # Keep iterating until our line starts with the closing curly
            while not line.startswith("};"):

                # Find enum value in line defined as `EVALUE(<value>)`.
                evalue = re.match(r'EVALUE\((\w+)\)', line)
                if evalue:
                    enum_vals.append(f'{evalue.group(1)}')

                # Consume the next line
                line = next(line_iter)

            # Store this enum with its associated set of values
            bzla_enums[enum_name] = enum_vals

    # Return our dictionary of enums
    return bzla_enums


# Template for one enum
CPP_ENUM_TEMPLATE = """
    cdef enum class Cpp{bzla_enum:s} "bitwuzla::{bzla_enum:s}":
        {values:s}
"""

PY_ENUM_TEMPLATE = """
class {bzla_enum:s}(Enum):
    \"\"\"{docstring:s}
    \"\"\"
    {values:s}
"""

PY_ENUM_TEMPLATE_STR = """
class {bzla_enum:s}(Enum):
    \"\"\"{docstring:s}
    \"\"\"
    {values:s}

    def __str__(self):
        cdef stringstream c_ss
        c_ss << <Cpp{bzla_enum}> self.value
        return c_ss.to_string().decode()
"""

# Template for the whole file
FILE_TEMPLATE = """from enum import Enum

cdef extern from "<iostream>" namespace "std":
    cdef cppclass ostream:
        pass

cdef extern from "<sstream>" namespace "std":
    cdef cppclass stringstream(ostream):
        string to_string "str" () const
        stringstream &operator << (CppKind)
        stringstream &operator << (CppResult)
        stringstream &operator << (CppRoundingMode)

cdef extern from \"bitwuzla/cpp/bitwuzla.h\" namespace \"bitwuzla\":
{cenums:s}

{pyenums:s}"""

ENUM_DOCSTRINGS = {
    "Option":
"""Configuration options supported by Bitwuzla. For more information on
   options see :ref:`cpp_options`.
""",

    "Kind":
"""BitwuzlaTerm kinds. For more information on term kinds see :ref:`cpp_kinds`.
""",

    "Result":
"""Satisfiability result.
""",

    "RoundingMode":
"""Floating-point rounding mode.
"""
}


def generate_output(bzla_enums, output_file):
    """
    Given a dictionary of enums, formats each enum into `CPP_ENUM_TEMPLATE` and
    then all the enums into `FILE_TEMPLATE` and writes into "output_file"
    """

    # List of strings for all our enums
    all_c_enums = []
    all_py_enums = []

    # Iterate on each enum and its associated values
    for bzla_enum, values in bzla_enums.items():

        # Construct the formatted list of all values
        formatted_c_values = ",\n        ".join(values)

        # Construct the C enum string
        s = CPP_ENUM_TEMPLATE.format(
            bzla_enum=bzla_enum, values=formatted_c_values
        )
        all_c_enums.append(s)


        #  Construct the Python enum string
        py_enum_name = bzla_enum.replace('Bitwuzla', '')
        py_values = []
        for e in values:
            py_e = e
            if e not in ('MAX', 'NUM_KINDS',
                         'NUM_OPTS'):
                py_values.append('{} = Cpp{}.{}'.format(py_e, py_enum_name, e))

        formatted_py_values = "\n    ".join(py_values)
        if py_enum_name not in ENUM_DOCSTRINGS:
            raise BitwuzlaEnumParseError(
                    f'Missing docstring for enum {py_enum_name}')
        docstring = ENUM_DOCSTRINGS[py_enum_name]
        tpl = PY_ENUM_TEMPLATE if py_enum_name == 'Option' else PY_ENUM_TEMPLATE_STR
        s = tpl.format(
            bzla_enum=py_enum_name,
            docstring=docstring,
            values=formatted_py_values
        )
        all_py_enums.append(s)

    # Open-up our output file
    with open(output_file, "w") as output_fd:

        # Write the whole template
        output_fd.write(FILE_TEMPLATE.format(
            cenums="\n".join(all_c_enums),
            pyenums="\n".join(all_py_enums)
            ))


def main():
    """
    Entry point
    """

    ap = argparse.ArgumentParser()
    ap.add_argument('input_file')
    ap.add_argument('output_file')
    args = ap.parse_args()

    if not args.input_file.endswith('enums.h') and not args.input_file.endswith('option.h'):
        raise ValueError("Expected enums.h or option.h as input file")

    # Extract all of our enums
    bzla_enums = extract_enums(args.input_file)

    # Generate our output file
    generate_output(bzla_enums, args.output_file)

    return 0


if __name__ == "__main__":
    sys.exit(main())

# EOF
