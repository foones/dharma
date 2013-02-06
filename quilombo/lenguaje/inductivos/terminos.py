from comunes.utiles import identar
from lenguaje.terminos import Termino, TNada

class TDeclaracionConstructorConParametros(Termino):

    def __init__(self, nombre_constructor, nombres_parametros):
        self._nombre_constructor = nombre_constructor
        self._nombres_parametros = nombres_parametros

    def __unicode__(self):
        return u'TDeclaracionConstructorConParametros(%s, [\n%s\n])' % (
            self._nombre_constructor,
            identar('\n'.join(map(unicode, self._nombres_parametros))),
        )

    def evaluar_en(self, estado):
        yield TNada()

class TDefinicionDeTipoInductivo(Termino):

    def __init__(self, nombre_tipo, constructores):
        self._nombre_tipo = nombre_tipo
        self._constructores = constructores

    def __unicode__(self):
        return u'TDefinicionDeTipoInductivo(%s, [\n%s\n])' % (
            self._nombre_tipo,
            identar('\n'.join(map(unicode, self._constructores))),
        )

    def evaluar_en(self, estado):
        yield TNada()

