import sys, re

macros = dict()
typedefs = dict()
functions = dict()
typedefs = dict()
deprecated = dict()
docstrings = dict()

class DocString:

    def __init__(self, string):
        self.docstring = string

    def to_rst(self):
        s = self.docstring

        # reference macros
        for m in macros:
            s = s.replace(m, ":c:macro:`{}`".format(m))

        # reference functions
        for f in functions:
            # exactly match function name (no substrings in other names)
            s = re.sub(r'{}((?![a-z0-9_]))'.format(f),
                       r':c:func:`{}`\1'.format(f), s)
            # all functions with _noref will not be referenced
            s = s.replace("{}_noref".format(f), f)

        return s

    def __str__(self):
        return self.docstring

    def __repr__(self):
        return self.__str__()

class Macro:

    def __init__(self, definition):
        l = definition.split()
        self.name = l[1].strip()
        assert("BOOLECTOR_" in self.name)

    def to_rst(self):
        return ".. c:macro:: {}".format(self.name)

class TypeDef:

    def __init__(self, definition):
        l = definition.replace(';', '').split()
        assert(len(l) == 4)
        self.name = l[-1]

    def to_rst(self):
        return ".. c:type:: {}".format(self.name)


class FunDef:

    def __init__(self, signature):
        p_name = re.compile(r'boolector_([a-z0-9_]+)') 
        m = p_name.search(signature)
        assert(m is not None)
        assert(m.group(0))
        self.name = m.group(0)
        self.signature = signature

        p_params = re.compile(r'\((.*)\)')
        m = p_params.search(signature)
        params = m.group(1).split(',')

        self.params = dict()

        # extract param with type
        if len(params) > 0 and params[0] != "void":
            for param in params:
                p = param.split()
                name = p[-1]
                type = " ".join(p[:-1])
                assert(name not in self.params)
                self.params[name] = type 

    def to_rst(self):
        return ".. c:function:: {}".format(self.signature.replace(';', ''))

    def __str__(self):
        return self.signature

    def __repr__(self):
        return self.__str__()

if __name__ == "__main__":

    if len(sys.argv) != 2:
        raise Exception("Invalid number of arguments")

    with open(sys.argv[1], "r") as file:
        fun_open = False
        doc_open = False
        fun = []
        doc = []
        linenum = 0
        for line in file:
            linenum += 1

            assert(not fun_open or not doc_open)
            assert(not doc_open or not fun_open)

            if line.strip().startswith("/*!"):  # start doc string
                if line.strip() != "/*!":
                    raise Exception(
                        "Invalid start of docstring at line {}. Docstring "\
                        "must start with '/*!' only".format(linenum))
                doc = []
                doc_open = True
            elif doc_open and line.strip().startswith("*/"):  # end doc string
                if line.strip() != "*/":
                    raise Exception(
                        "Invalid end of docstring at line {}. Docstring "\
                        "must end with '*/' only".format(linenum))
                doc_open = False
            elif doc_open: # contents doc string
                doc.append(line)
            elif not doc_open and "boolector_" in line:  # open function
                fun = []
                fun_open = True

            # collect function signature
            if fun_open:
                fun.append(line.strip())

            if fun_open and ");" in line:  # end function
                fun_open = False
                fd = FunDef(" ".join(fun))
                if len(doc) == 0:
                    raise Exception(
                        "No docstring found for function '{}'".format(fd.name))
                ds = DocString("".join(doc))
                if ".. deprecated::" in ds.docstring:
                    deprecated[fd.name] = fd
                else:
                    functions[fd.name] = fd
                docstrings[fd.name] = ds
                fun = []
                doc = []
            elif line.startswith("#define") and "BOOLECTOR_" in line and \
                 len(line.split()) > 2:
                m = Macro(line)
                ds = DocString("".join(doc))
                macros[m.name] = m 
                docstrings[m.name] = ds
                doc = []
            elif "typedef" in line and ("BoolectorNode" in line or \
                                        "BoolectorSort" in line or \
                                        "Bzla " in line):
                td = TypeDef(line)
                ds = DocString("".join(doc))
                typedefs[td.name] = td
                docstrings[td.name] = ds
                doc = []

    with open('cboolector_index.rst', 'w') as file:
        file.write("C Interface\n")
        file.write("===========\n\n")

        file.write(".. _macros:\n\n")
        file.write("Macros\n")
        file.write("^^^^^^\n\n")
        for m in sorted(macros.keys()):
            file.write("{}\n\n".format(macros[m].to_rst()))
            for line in docstrings[m].to_rst().split('\n'):
                file.write("{}\n".format(line))
            file.write("\n")

        file.write("Typedefs\n")
        file.write("^^^^^^^^\n\n")
        for td in sorted(typedefs.keys()):
            file.write("{}\n\n".format(typedefs[td].to_rst()))
            for line in docstrings[td].to_rst().split('\n'):
                file.write("{}\n".format(line))
            file.write("\n")

        file.write("Functions\n")
        file.write("^^^^^^^^^\n\n")
        for f in sorted(functions.keys()):
            file.write("{}\n\n".format(functions[f].to_rst()))
            for line in docstrings[f].to_rst().split('\n'):
                file.write("{}\n".format(line))
            file.write("\n")

        file.write("Deprecated\n")
        file.write("^^^^^^^^^^\n\n")
        for f in sorted(deprecated.keys()):
            file.write("{}\n\n".format(deprecated[f].to_rst()))
            for line in docstrings[f].to_rst().split('\n'):
                file.write("{}\n".format(line))
            file.write("\n")
    print("generated cboolector_index.rst")

    sys.exit(0)
