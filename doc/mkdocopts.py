import sys, re

if __name__ == "__main__":

    if len(sys.argv) != 2:
        raise Exception("Invalid number of arguments")

    lpad = 0
    opts = []
    with open(sys.argv[1], "r") as file:
        desc_open = False
        desc = []
        linenum = 0
        for line in file:
            linenum += 1
            if not desc_open \
               and line.strip().startswith("/*!"):  # start doc string
                   if line.strip() != "/*!":
                       raise Exception(
                               "Invalid start of docstring at line {}. "\
                               "Docstring must start with "\
                               "'/*!' only".format(linenum))
                   desc_open = True
            elif desc_open \
                 and line.strip().startswith("*/"):  # end doc string
                     if line.strip() != "*/":
                         raise Exception(
                                 "Invalid end of docstring at line {}. "\
                                 "Docstring must end with "\
                                 "'*/' only".format(linenum))
                     opts.append(desc)
                     desc = []
                     desc_open = False
            elif desc_open:  # collect opt desc
                if line[0] == ' ':
                    pad = len(line) - len(line.lstrip(' '))
                    if pad <= 3:
                        print(
                            "Wrong indent for '{}'. Expected at least 4".format(
                                line.rstrip()))
                    if lpad == 0 or pad < lpad:
                        lpad = pad
                desc.append(line.rstrip())

    opts_str = []
    for o in opts:
        for line in o:
            assert(line[:lpad].lstrip(' ') == '')
            opts_str.append('{}\n'.format(line[lpad:]))
        opts_str.append('\n')

    with open('cboolector_options.rst', 'w') as file:
        file.write('Boolector Options\n')
        file.write('-----------------\n')
        file.write(''.join(opts_str))

    with open('pyboolector_options.rst', 'w') as file:
        file.write('Boolector Options\n')
        file.write('-----------------\n')
        file.write(''.join(opts_str))
