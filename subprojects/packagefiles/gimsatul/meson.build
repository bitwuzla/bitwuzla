project('gimsatul',
  'c',
  version: '1.1.3',
  license: 'mit',
  default_options: [
    'c_std=c11',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=if-release',
    'warning_level=0',
    'optimization=3',
  ]
)

compiler = meson.get_compiler('c')
conf_data = configuration_data()
conf_data.set('version', '1.1.3')
conf_data.set('gitid', '44ae6e9e265c4e16850e0fdb8fdaed8c9b8c5a85')
conf_data.set('compiler', compiler.version())
configure_file(input: 'config.h.in',
               output: 'config.h',
               configuration: conf_data)


sources = [
  'allocate.c',
  'analyze.c',
  'assign.c',
  'average.c',
  'backtrack.c',
  'barrier.c',
  'build.c',
  'bump.c',
  'catch.c',
  'clause.c',
  'clone.c',
  'compact.c',
  'decide.c',
  'deduplicate.c',
  'definition.c',
  'detach.c',
  'eliminate.c',
  'export.c',
  'fail.c',
  'file.c',
  'gimsatul.c',
  'heap.c',
  'import.c',
  'logging.c',
  'message.c',
  'minimize.c',
  'mode.c',
  'options.c',
  'parse.c',
  'probe.c',
  'profile.c',
  'promote.c',
  'propagate.c',
  'queue.c',
  'reduce.c',
  'rephase.c',
  'report.c',
  'restart.c',
  'ring.c',
  'ruler.c',
  'scale.c',
  'search.c',
  'set.c',
  'simplify.c',
  'solve.c',
  'statistics.c',
  'substitute.c',
  'subsume.c',
  'system.c',
  'tiers.c',
  'trace.c',
  'types.c',
  'unclone.c',
  'utilities.c',
  'vivify.c',
  'walk.c',
  'warm.c',
  'watches.c',
  'witness.c'
]

c_args = ['-DQUIET']
gimsatul_lib = static_library('gimsatul', sources: sources,
                              include_directories: include_directories('include'),
                              c_args: c_args)
gimsatul_dep = declare_dependency(
                  include_directories: include_directories('include'),
                  link_with: gimsatul_lib)
