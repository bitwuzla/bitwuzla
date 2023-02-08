project('symfpu', 'cpp')

header_targets=[]

subdir('symfpu/core')
subdir('symfpu/utils')

inc = include_directories('.')
symfpu_dep = declare_dependency(include_directories: inc,
                                sources: header_targets)
