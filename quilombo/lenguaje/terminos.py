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

    def es_nada(self): return False
    def es_constante(self): return False
    def es_variable(self): return False
    def es_bloque(self): return False
    def es_invocacion_verbo(self): return False
    def es_definicion_de_funcion(self): return False

class TerminoConstante(Termino):
    def es_constante(self):
        return True

class TNada(TerminoConstante):
    def __unicode__(self):
        return 'nada'

    def es_nada(self):
        return True

class TVariable(Termino):
    "Términos que representan variable."

    def __init__(self, nombre, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre = nombre

    def __unicode__(self):
        return u'TVariable(%s)' % (self._nombre,)

    def es_variable(self):
        return True

    def nombre_variable(self):
        return self._nombre

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

    def es_definicion_de_funcion(self):
        return True

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

    def es_invocacion_verbo(self):
        return True

class TBloque(Termino):
    "Bloque."

    def __init__(self, subterminos, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._subterminos = subterminos

    def __unicode__(self):
        return u'TBloque([\n%s\n])' % (identar(unicode_list(self._subterminos, sep=u',\n')),)

    def es_bloque(self):
        return True

    def subterminos(self):
        return self._subterminos

