
import re
import sys
import random
import math

import pygtk
pygtk.require('2.0')
import gtk
import gobject

def rotate_players(players, player):
    """Rotate the list of players for 'player' to be the first
       element in the list."""
    prev = []
    post = []
    self_seen = False
    for p in players:
        if p == player:
            self_seen = True
        if self_seen:
            prev.append(p)
        else:
            post.append(p)
    return prev + post

class GameState(object):
    pass

class GameGUI(object):
    pass

class App(object):

    def __init__(self):
        self._game = None

        self._gui = GameGUI()
        self._gui.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self._gui.window.show()
        self._gui.box = None
        self._gui.pixbuf_pool = {}

    def read_message(self):
        msg = sys.stdin.readline()
        msg = re.sub(r'[ \t\r\n]+', ' ', msg.strip(' \t\r\n'))
        msg = msg.split(' ')

        opcode, all_args = msg[0], msg[1:]

        args = []
        while all_args != []:
            assert all_args.pop(0) == '|'
            curlist = []
            while len(all_args) > 0 and all_args[0] != '|':
                curlist.append(all_args.pop(0))
            args.append(curlist)

        return opcode, args

    def send_message(self, msg):
        sys.stdout.write('%s\n' % (msg,))
        sys.stdout.flush()

    def read_message_with_ack(self):
        msg = self.read_message()
        self.send_message('ACK')
        return msg

#    def image_clicked(self, *args):
#        print 'CLICK', args
#
#    def deal_cards(self, cards, players, gui_player, gui_card):
#        self._cards = cards
#        self._players = players
#        self._gui_player = gui_player
#        self._gui_card = gui_card
#
#        #for card in cards:
#        #    button = gtk.Button()
#        #    image = gtk.Image()
#        #    image.set_from_file('test.png')
#        #    image.show()
#        #    button.add(image)
#        #    button.show()
#
#        self._window.add(button)
#        button.connect('clicked', self.image_clicked)

        #while True:
        #if not select.select([sys.stdin], [], [], 0.0)[0]:
        #    return True

    def _configure_event(self, *args):
        self._update_player_positions()
 
    def _update_player_positions(self):
        assert len(self._game.player_names) == 4
        p_i = -1

        relative_fracts_x = [
           (0.01, 0.10),
           (0.35, 0.65),
           (0.90, 0.99),
        ]
        relative_fracts_y = [
           (0.01, 0.25),
           (0.15, 0.85),
           (0.75, 0.99),
        ]
        player_positions = [
            (1, 2),
            (2, 1),
            (1, 0),
            (0, 1),
        ]
        width, height = self._gui.window.get_size()
        pi = -1
        for p in self._game.player_names:
            pi += 1
            posx, posy = player_positions[pi]
            xf0, xf1 = relative_fracts_x[posx]
            yf0, yf1 = relative_fracts_y[posy]
            x0_px = int(xf0 * width)
            y0_px = int(yf0 * height)
            x1_px = int(xf1 * width)
            y1_px = int(yf1 * height)
            self._gui.box.move(self._gui.player_box[p], x0_px, y0_px)
            self._gui.player_box[p].set_usize(x1_px - x0_px, y1_px - y0_px)
            self._gui.player_box[p].modify_bg(gtk.STATE_NORMAL, gtk.gdk.color_parse('red'))
            self._gui.player_orientation[p] = 'horizontal' if pi % 2 == 0 else 'vertical'

    def _start_game(self, cards, player_names, player_name):

        if self._gui.box is not None:
            self._gui.window.remove(self._gui.box)

        player_name = player_name[0]

        self._game = GameState()
        self._game.player_name = player_name
        self._game.player_names = rotate_players(player_names, player_name)

        self._gui.box = gtk.Fixed()
        self._gui.player_box = {}
        self._gui.player_orientation = {}

        for p in player_names:
            pbox = gtk.Frame()
            pbox.show()
            self._gui.player_box[p] = pbox
            self._gui.box.put(pbox, 0, 0)

        self._gui.box.show()
        self._gui.window.add(self._gui.box)
        
        self._gui.window.connect('realize', self._configure_event)
        self._gui.window.connect('configure-event', self._configure_event)
        self._update_player_positions()
        return True

    def _card_widget(self, card):
        if card not in self._gui.pixbuf_pool:
            pixbuf = gtk.gdk.pixbuf_new_from_file_at_size('gui/img/%s.svg' % (card,), 128, 256)
            self._gui.pixbuf_pool[card] = pixbuf
        img = gtk.Image()
        img.set_from_pixbuf(self._gui.pixbuf_pool[card])
        img.show()
        btn = gtk.Button()
        btn.add(img)
        btn.show()
        return btn
        #   #image.set_size_request(32, 64) #
        #   btn.connect('button_press_event', self.image_clicked)
        #   bbox.add(btn)
        #   bbox.pack_end(btn)
        #   bbox.show()

    def _add_cards(self, player_name, cards):
        box_class = {
            'horizontal': gtk.HBox,
            'vertical': gtk.VBox,
        } 
        box = box_class[self._gui.player_orientation[player_name]]()
        for card in cards:
            btn = self._card_widget(card)
            box.add(btn)
        box.show()
        self._gui.player_box[player_name].add(box)

    def _hand(self, cards):
        sys.stderr.write('CARDS %s' % (cards,))
        for p in self._game.player_names:
            sys.stderr.write('CARGO PARA %s %s\n' % (p, self._game.player_name,))
            if p != self._game.player_name:
                self._add_cards(p, ['back' for i in range(len(cards))])
            else:
                self._add_cards(p, cards)
        return True

#       #bbox = gtk.HButtonBox()
#       bbox = gtk.HBox()
#       #bbox.set_layout(gtk.BUTTONBOX_SPREAD)
#       #bbox.set_spacing(10)
#       
#        nums = map(str, range(1, 11)) + ['J', 'Q', 'K']
#        
#        for num in nums:
#            #btn = gtk.EventBox()
#            btn = gtk.Button()
#
#            image = gtk.Image()
#            image.set_from_file('gui/img/%sC.svg' % (num,))
#
#            image.show()
#            #image.set_size_request(32, 64) #
#            btn.add(image)
#            btn.show()
#            btn.connect('button_press_event', self.image_clicked)
#            bbox.add(btn)
#            bbox.pack_end(btn)
#        bbox.show()
#
#        self._gui.window.add(bbox)

    def dispatch(self, *args):
        opcode, args = self.read_message_with_ack()

        if opcode == 'END':
            return False

        elif opcode == 'start':
            self._start_game(*args)
            return True

        elif opcode == 'hand':
            self._hand(*args)
            return True

        else:
            raise Exception('unknown opcode: "%s"' % (opcode,))

    def main(self):
        gobject.io_add_watch(
            sys.stdin,
            gobject.IO_IN | gobject.IO_HUP,
            self.dispatch
        )
        gtk.main()

#sys.stdin.read()

#import select
#if select.select([sys.stdin,],[],[],0.0)[0]:
#    print "Have data!"
#else:
#    print "No data"

#print help(gtk.timeout_add_full)

if __name__ == '__main__':
    app = App()
    app.main()

