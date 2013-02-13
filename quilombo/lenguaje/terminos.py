# coding:utf-8

from comunes.utiles import QuilomboException, identar

def unicode_list(xs, sep=u', '):
    return sep.join([unicode(x) for x in xs])

class Termino(object):
    "Cada instancia representa un término del lenguaje."

    def __init__(self, tokens=[]):
        self._tokens = tokens

    def tokens(self):
        return self._tokens

    #def __repr__(self):
    #    return unicode(self)

    def es_nada(self):
        return False

def evaluar_lista_en(xs, estado):
    if xs == []:
        yield []
    else:
        for y in xs[0].evaluar_en(estado):
            for ys in evaluar_lista_en(xs[1:], estado):
                yield [y] + ys

class TerminoConstante(Termino):

    def evaluar_en(self, estado):
        yield self

class TNada(TerminoConstante):
    def __unicode__(self):
        return 'nada'

    def evaluar_en(self, estado):
        yield self

    def es_nada(self):
        return True

class TVariable(Termino):
    "Términos que representan variable."

    def __init__(self, nombre, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre = nombre

    def __unicode__(self):
        return u'TVariable(%s)' % (self._nombre,)

    def nombre(self):
        return self._nombre

    def evaluar_en(self, estado):
        yield estado.entorno.valor(self._nombre)

class TParametro(Termino):
    "Argumentos de una función."

    def __init__(self, preposicion, variable, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._preposicion = preposicion
        self._variable = variable

    def __unicode__(self):
        return u'TParametro(%s, %s)' % (
            self._preposicion,
            self._variable
        )

class TDefinicionDeFuncion(Termino):
    "Definición de función."

    def __init__(self, verbo, parametros, cuerpo, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._verbo = verbo
        self._parametros = parametros
        self._cuerpo = cuerpo

    def __unicode__(self):
        return u'TDefinicionDeFuncion(%s, [%s],\n%s\n)' % (
            self._verbo,
            unicode_list(self._parametros),
            identar(unicode(self._cuerpo))
        )

    def evaluar_en(self, estado):
        # TODO
        print unicode(self)
        yield TNada()

class TInvocarVerbo(Termino):
    u"Aplicación de un verbo a parámetros."

    def __init__(self, verbo, argumentos, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._verbo = verbo
        self._argumentos = argumentos

    def __unicode__(self):
        return u'TInvocarVerbo(%s, [\n%s\n])' % (
            self._verbo,
            identar(unicode_list(self._argumentos, sep=u',\n'))
        )

    def evaluar_en(self, estado):
        # TODO
        print unicode(self)
        yield TNada()

class TBloque(Termino):
    "Bloque."

    def __init__(self, subterminos, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._subterminos = subterminos

    def __unicode__(self):
        return u'TBloque([\n%s\n])' % (identar(unicode_list(self._subterminos, sep=u',\n')),)

    def evaluar_en(self, estado, i=0):
        terminos = self._subterminos
        if i == len(terminos):
            yield TNada()
            return

        ti = terminos[i]
        for ri in ti.evaluar_en(estado):
            if i + 1 < len(terminos):
                for rs in self.evaluar_en(estado, i + 1):
                    yield rs
            else:
                yield ri

