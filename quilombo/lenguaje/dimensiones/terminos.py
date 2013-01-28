
from lenguaje.terminos import Termino, TNada

class TDefinicionDeDimension(Termino):

    def __init__(self, nombre_dimension, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre_dimension = nombre_dimension

    def __unicode__(self):
        return u'TDefinicionDeDimension(%s)' % (self._nombre_dimension,)

    def evaluar_en(self, estado):
        # TODO
        print unicode(self)
        yield TNada()

