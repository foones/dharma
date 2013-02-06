from comunes.utiles import identar
from lenguaje.tesoro import tesoro_actual
from lenguaje.terminos import Termino, TNada

class TTipoInductivo(Termino):

    def __init__(self, nombre_tipo):
        self._nombre_tipo = nombre_tipo
        self._constructores = []

    def agregar_constructor(self, constructor):
        self._constructores.append(constructor)

    def __unicode__(self):
        return self._nombre_tipo

class TConstructor(Termino):
    """Nota: un constructor 0-ario se identifica con una "instancia"
       del correspondiente tipo.

       En cambio, un constructor n-ario con n > 0 no es un valor del tipo."""

    def __init__(self, tipo, nombre_constructor, nombres_parametros):
        self._tipo = tipo
        self._nombre_constructor = nombre_constructor
        self._nombres_parametros = nombres_parametros

    def __unicode__(self):
        return self._nombre_constructor

class TDeclaracionConstructorConParametros(Termino):

    def __init__(self, nombre_constructor, nombres_parametros):
        self.nombre_constructor = nombre_constructor
        self.nombres_parametros = nombres_parametros

    def __unicode__(self):
        return u'TDeclaracionConstructorConParametros(%s, [\n%s\n])' % (
            self.nombre_constructor,
            identar('\n'.join(map(unicode, self.nombres_parametros))),
        )

class TDefinicionDeTipoInductivo(Termino):

    def __init__(self, nombre_tipo, declaraciones_constructores):
        self._nombre_tipo = nombre_tipo
        self._declaraciones_constructores = declaraciones_constructores

    def __unicode__(self):
        return u'TDefinicionDeTipoInductivo(%s, [\n%s\n])' % (
            self._nombre_tipo,
            identar('\n'.join(map(unicode, self._declaraciones_constructores))),
        )

    def evaluar_en(self, estado):
        tipo = TTipoInductivo(
            tesoro_actual().sustantivo_comun_singular(self._nombre_tipo)
        )
        for decl in self._declaraciones_constructores:
            constructor = TConstructor(
                self,
                tesoro_actual().sustantivo_comun_singular(
                    decl.nombre_constructor
                ),
                decl.nombres_parametros,
            )
            estado.entorno.declarar(decl.nombre_constructor, constructor)
            tipo.agregar_constructor(constructor)
        estado.entorno.declarar(self._nombre_tipo, tipo)
        yield TNada()

