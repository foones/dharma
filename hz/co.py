#!/usr/bin/python

from game.rules import all_cards, Game
from gui.connector import Connector

#c = Connector('runghc -i:ai ai/Main.hs')
#print c.call('hola')
#c.end()

player_names = ['N', 'E', 'S', 'W']
user = 'S'
players = {}

for name in player_names:
    players[name] = Connector('python gui/main.py')
    print player_names
    players[name].call('start | %s | %s | %s' % (' '.join(all_cards), ' '.join(player_names), name))

game = Game(player_names)
game.start()
for name in player_names:
    print 'HAND', game.hand(name)
    players[name].call('hand | %s' % (' '.join(game.hand(name)),))

while True:
    x = raw_input('listo!')
    #print c.call(x)

