from lenguaje.terminos import Termino

class TMeterElemento(Termino):

    def __init__(self, elemento):
        self._elemento = elemento

    def __unicode__(self):
        return u'TMeterElemento(%s)' % (self._elemento,)

    def evaluar_en(self, estado):
        for elemento in self._elemento.evaluar_en(estado):
            estado.push(elemento)
            yield elemento

