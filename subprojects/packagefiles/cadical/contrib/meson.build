sources = [
  'craigtracer.cpp',
]

dependencies = [cadical_dep]
cadicraig_lib = library('cadicraig', sources: sources, dependencies: dependencies)
cadicraig_dep = declare_dependency(
                  include_directories: include_directories('.'),
                  link_with: cadicraig_lib,
                  dependencies: dependencies)
