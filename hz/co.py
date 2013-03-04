#!/usr/bin/python
from gui.connector import Connector

c = Connector('runghc -i:ia ia/IA.hs')
print c.call('hola')
c.end()

