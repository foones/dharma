#!/usr/bin/python

from gui.connector import Connector

#c = Connector('runghc -i:ai ai/Main.hs')
#print c.call('hola')
#c.end()

c = Connector('python gui/main.py')

#print c.call('start | c1 c2 c3 | p1 p2 p3 p4 p5 | p1')
print c.call('start | c1 c2 c3 | p1 p2 p3 p4 | p1')
print c.call('hand | c1 c2 c3 c1 c')
while True:
    x = raw_input('listo!')
    print c.call(x)

