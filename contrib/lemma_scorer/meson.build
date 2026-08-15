# ---
# Build lemma scorer binary
#
# Development utility to score, rank and verify the abstraction lemma schemas
# of bit-vector operators. Not part of the Bitwuzla library and not built by
# default, build with:
#
#   meson compile -C <build dir> lemma-scorer
# ---

lemma_scorer_sources = files([
  '../../src/solver/abstract/abstraction_lemma_scorer.cpp',
  'main.cpp',
])

lemma_scorer_bin = executable('lemma-scorer', lemma_scorer_sources,
                              include_directories: include_directories('../../src'),
                              dependencies: [bitwuzla_dep],
                              cpp_args: cpp_args,
                              build_by_default: false,
                              install: false)

alias_target('lemma-scorer', lemma_scorer_bin)
