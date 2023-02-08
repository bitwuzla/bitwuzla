headers = [
  'common.h',
  'numberOfRoundingModes.h',
  'properties.h'
]

fs = import('fs')
foreach header : headers
 header_targets += [fs.copyfile(join_paths('../../utils', header), header)]
endforeach
