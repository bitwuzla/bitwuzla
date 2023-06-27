###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2021 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import os

from docutils import nodes
from docutils.parsers.rst import Directive
from docutils.statemachine import StringList

class TabbedExamples(Directive):
    """Add directive `tabbed-examples` to be used as follows:

        .. tabbed-examples::
            file1
            file2

        The arguments should be relative paths to source files.
        This directive detects the language from the file extension and
        supports the extensions specified in self.exts.
    """

    # Set tab title and language for syntax highlighting
    exts = {
        '.c': {'title': 'C', 'lang': 'c'},
        '.cpp': {'title': 'C++', 'lang': 'c++'},
        '.py': {'title': 'Python', 'lang': 'python'},
        '.smt2': {'title': 'SMT-LIBv2', 'lang': 'smtlib'},
    }

    # The "arguments" are actually the content of the directive
    has_content = True

    def run(self):
        # collect everything in a list of strings
        content = ['.. tabs::', '']

        for file in self.content:
            # detect file extension
            _, ext = os.path.splitext(file)
            if ext in self.exts:
                title = self.exts[ext]['title']
                lang = self.exts[ext]['lang']
            else:
                title = ext
                lang = ext

            # generate tabs
            content.append(f'    .. tab:: {title}')
            content.append(f'')
            content.append(f'        .. literalinclude:: {file}')
            content.append(f'            :language: {lang}')
            content.append(f'            :linenos:')

        # parse the string list
        node = nodes.Element()
        self.state.nested_parse(StringList(content), 0, node)
        return node.children


def setup(app):
    app.setup_extension('sphinx_tabs.tabs')
    app.add_directive("tabbed-examples", TabbedExamples)
    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
