# coding:utf-8

class Termino(object):
    "Cada instancia representa un término del lenguaje."

    def __init__(self, tokens=[]):
        self._tokens = tokens

class TEntero(Termino):
    "Términos que representan números enteros."

    def __init__(self, numero, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)

        assert isinstance(numero, int) or isinstance(numero, long)
        self._numero = numero

    def __unicode__(self):
        return 'TEntero(%u)' % (self._numero,)
