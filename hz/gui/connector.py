import subprocess

class Connector(object):

    def __init__(self, cmd):
        self._process = subprocess.Popen(cmd.split(' '), stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def call(self, msg):
        self._process.stdin.write(msg + '\n')
        return self._process.stdout.readline()[:-1]
    
    def end(self):
        self._process.stdin.write('END\n')

