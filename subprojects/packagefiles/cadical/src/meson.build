fs = import('fs')
version=fs.read('../VERSION').strip()

compiler = meson.get_compiler('cpp')
conf_data = configuration_data()
conf_data.set('version', version)
conf_data.set('compiler', compiler.version())
configure_file(input: 'build.hpp.in',
               output: 'build.hpp',
               configuration: conf_data)


sources = [
  'analyze.cpp',
  'arena.cpp',
  'assume.cpp',
  'averages.cpp',
  'backtrack.cpp',
  'backward.cpp',
  'bins.cpp',
  'block.cpp',
  'ccadical.cpp',
  'checker.cpp',
  'clause.cpp',
  'collect.cpp',
  'compact.cpp',
  'condition.cpp',
  'config.cpp',
  'constrain.cpp',
  'contract.cpp',
  'cover.cpp',
  'decide.cpp',
  'decompose.cpp',
  'deduplicate.cpp',
  'elim.cpp',
  'ema.cpp',
  'extend.cpp',
  'external.cpp',
  'external_propagate.cpp',
  'file.cpp',
  'flags.cpp',
  'flip.cpp',
  'format.cpp',
  'gates.cpp',
  'instantiate.cpp',
  'internal.cpp',
  'ipasir.cpp',
  'limit.cpp',
  'logging.cpp',
  'lookahead.cpp',
  'lratbuilder.cpp',
  'lratchecker.cpp',
  'lucky.cpp',
  'message.cpp',
  'minimize.cpp',
  'occs.cpp',
  'options.cpp',
  'parse.cpp',
  'phases.cpp',
  'probe.cpp',
  'profile.cpp',
  'proof.cpp',
  'propagate.cpp',
  'queue.cpp',
  'random.cpp',
  'reap.cpp',
  'reduce.cpp',
  'rephase.cpp',
  'report.cpp',
  'resources.cpp',
  'restart.cpp',
  'restore.cpp',
  'score.cpp',
  'shrink.cpp',
  'signal.cpp',
  'solution.cpp',
  'solver.cpp',
  'stats.cpp',
  'subsume.cpp',
  'terminal.cpp',
  'ternary.cpp',
  'tracer.cpp',
  'transred.cpp',
  'util.cpp',
  'var.cpp',
  'version.cpp',
  'vivify.cpp',
  'walk.cpp',
  'watch.cpp'
]

dependencies = []
if host_machine.system() == 'windows'
  cc = meson.get_compiler('cpp')
  dependencies += [cc.find_library('psapi')]
endif

cpp_args = []
if not compiler.has_function('getc_unlocked', prefix: '#include <cstdio>')
  cpp_args += ['-DNUNLOCKED']
endif

cadical_lib = library('cadical', sources: sources, cpp_args: cpp_args)
cadical_dep = declare_dependency(
                  include_directories: include_directories('.'),
                  link_with: cadical_lib,
                  dependencies: dependencies)

