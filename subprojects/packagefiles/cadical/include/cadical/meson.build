fs = import('fs')
headers = ['cadical.hpp', 'tracer.hpp']
foreach header : headers
  header_targets += [fs.copyfile(join_paths('../../src', header), header)]
endforeach
