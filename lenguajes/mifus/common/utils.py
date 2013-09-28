import re

class MifusException(Exception):
    pass

def file_lines(fn):
    f = open(fn, 'r')
    numline = 0
    for line in f:
        numline += 1
        line = line.split('#')[0].strip(' \t\r\n')
        if line == '': continue
        line = re.sub('[ \t]+', ' ', line)
        yield numline, line

def unzip(lst):
    return [x for (x, y) in lst], [y for (x, y) in lst]
