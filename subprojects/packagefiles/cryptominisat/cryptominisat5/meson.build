fs = import('fs')
headers = [
  'cryptominisat.h',
  'solvertypesmini.h'
]
foreach header : headers
  header_targets += [fs.copyfile(join_paths('../src', header), header)]
endforeach
