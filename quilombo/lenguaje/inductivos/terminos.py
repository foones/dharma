# coding:utf-8

from comunes.utiles import identar, QuilomboException
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
    u"""Nota: un constructor n-ario se identifica con una "instancia"
        del correspondiente tipo en cuanto tiene todos sus parámetros
        instanciados."""

    def __init__(self, tipo, nombre_constructor, nombres_parametros, valores_parametros=None):
        self._tipo = tipo
        self._nombre_constructor = nombre_constructor
        self._nombres_parametros = nombres_parametros
        if valores_parametros is None:
            self._valores_parametros = {}
        else:
            self._valores_parametros = valores_parametros

    def currificar(self, arg):
        for param in self._nombres_parametros:
            if param not in self._valores_parametros:
                valores = {}
                for k, v in self._valores_parametros.items():
                    valores[k] = v
                valores[param] = arg
                return TConstructor(self._tipo, self._nombre_constructor, self._nombres_parametros, valores)
        raise QuilomboException(u'no se le puede pasar un parámetro más al constructor %s, pues ya es un valor' % (self,))

    def __unicode__(self):
        res = []
        for param in self._nombres_parametros:
            if param in self._valores_parametros:
                res.append(u'%s = %s' % (param, self._valores_parametros[param]))
        if res == []:
            return self._nombre_constructor
        else:
            return self._nombre_constructor + '(' + ', '.join(res) + ')'

    def aridad(self):
        return len(self._nombres_parametros) - len(self._valores_parametros)

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

class TAplicacionTotalConstructor(Termino):

    def __init__(self, constructor):
        self._constructor = constructor

    def __unicode__(self):
        return u'TAplicacionTotalConstructor(%s)' % (self._constructor,)

    def evaluar_en(self, estado):
        for constructor in self._constructor.evaluar_en(estado):
            if not isinstance(constructor, TConstructor):
                raise QuilomboException(u'%s no es un constructor' % (constructor,))
            npop = min(estado.tam_pila(), constructor.aridad())

            args = []
            for i in range(npop):
                args.append(estado.pop())

            constructor_ap = constructor
            for arg in reversed(args):
                constructor_ap = constructor_ap.currificar(arg)

            estado.push(constructor_ap)
            yield constructor_ap

class TAplicacionParcialConstructor(Termino):
    pass

