compiler = meson.get_compiler('cpp')
conf_data = configuration_data()

conf_data.set('CMAKE_CXX_COMPILER', compiler.version())
conf_data.set('PROJECT_VERSION', '5.11.21')

conf_data.set('CMAKE_CXX_COMPILER', '')
conf_data.set('CMAKE_CXX_FLAGS', '')
conf_data.set('COMPILE_DEFINES', '')
conf_data.set('STATICCOMPILE', '')
conf_data.set('ONLY_SIMPLE', '')
conf_data.set('STATS', '')
conf_data.set('SQLITE3_FOUND', '')
conf_data.set('ZLIB_FOUND', '')
conf_data.set('VALGRIND_FOUND', '')
conf_data.set('ENABLE_TESTING', '')
conf_data.set('SLOW_DEBUG', '')
conf_data.set('ENABLE_ASSERTIONS', '')
conf_data.set('PYTHON_EXECUTABLE', '')
conf_data.set('PYTHON_LIBRARY', '')
conf_data.set('PYTHON_INCLUDE_DIRS', '')
conf_data.set('MY_TARGETS', '')
conf_data.set('LARGEMEM', '')
conf_data.set('LIMITMEM', '')
conf_data.set('BREAKID_LIBRARIES', '')
conf_data.set('BREAKID-VER', '')
conf_data.set('BOSPHORUS_LIBRARIES', '')
conf_data.set('BOSPH-VER', '')
conf_data.set('BOSPHORUS_VERSION_MAJOR', '')
conf_data.set('BOSPHORUS_VERSION_MINOR', '')
conf_data.set('BREAKID_VERSION_MAJOR', '')
conf_data.set('BREAKID_VERSION_MINOR', '')
conf_data.set('GIT_SHA1', '')

gitsha1_cpp = configure_file(input: 'GitSHA1.cpp.in',
                             output: 'GitSHA1.cpp',
                             configuration: conf_data)

sources = [
  'bva.cpp',
  'cardfinder.cpp',
  'ccnr.cpp',
  'ccnr_cms.cpp',
  'clauseallocator.cpp',
  'clausecleaner.cpp',
  'cnf.cpp',
  'completedetachreattacher.cpp',
  'cryptominisat.cpp',
  'cryptominisat_c.cpp',
  'datasync.cpp',
  'distillerbin.cpp',
  'distillerlitrem.cpp',
  'distillerlong.cpp',
  'distillerlongwithimpl.cpp',
  'frat.cpp',
  'gatefinder.cpp',
  'gaussian.cpp',
  'get_clause_query.cpp',
  'hyperengine.cpp',
  'intree.cpp',
  'lucky.cpp',
  'matrixfinder.cpp',
  'occsimplifier.cpp',
  'packedrow.cpp',
  'propengine.cpp',
  'reducedb.cpp',
  'sccfinder.cpp',
  'searcher.cpp',
  'searchstats.cpp',
  'sls.cpp',
  'solutionextender.cpp',
  'solver.cpp',
  'solverconf.cpp',
  'sqlstats.cpp',
  'str_impl_w_impl.cpp',
  'subsumeimplicit.cpp',
  'subsumestrengthen.cpp',
  'vardistgen.cpp',
  'varreplacer.cpp',
  'xorfinder.cpp',
  'picosat/picosat.c',
  'picosat/version.c',
  'oracle/oracle.cpp',
  gitsha1_cpp
]

cms_lib = library('cryptominisat5',
                  install: true,
                  sources: sources)

cms_dep = declare_dependency(
                  include_directories: include_directories(['..']),
                  link_with: cms_lib,
                  dependencies: dependency('threads'),
                  sources: header_targets)
