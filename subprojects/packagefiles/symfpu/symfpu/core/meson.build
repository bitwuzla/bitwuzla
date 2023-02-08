headers = [
  'add.h',
  'classify.h',
  'compare.h',
  'convert.h',
  'divide.h',
  'fma.h',
  'ite.h',
  'multiply.h',
  'operations.h',
  'packing.h',
  'remainder.h',
  'rounder.h',
  'sign.h',
  'sqrt.h',
  'unpackedFloat.h'
]

fs = import('fs')
foreach header : headers
  header_targets += [fs.copyfile(join_paths('../../core', header), header)]
endforeach
