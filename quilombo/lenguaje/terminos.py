# coding:utf-8

class Termino(object):
    "Cada instancia representa un término del lenguaje."

    def __init__(self, tokens=[]):
        self._tokens = tokens

    def __repr__(self):
        return unicode(self)

class TEntero(Termino):
    "Términos que representan números enteros."

    def __init__(self, numero, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)

        assert isinstance(numero, int) or isinstance(numero, long)
        self._numero = numero

    def __unicode__(self):
        return u'TEntero(%u)' % (self._numero,)

class TVariable(Termino):
    "Términos que representan variable."

    def __init__(self, nombre, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre = nombre

    def __unicode__(self):
        return u'TVariable(%s)' % (self._nombre,)

class TArgumento(Termino):
    "Argumentos de una función."

    def __init__(self, preposicion, variable, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._preposicion = preposicion
        self._variable = variable

    def __unicode__(self):
        return u'TArgumento(%s, %s)' % (self._preposicion, self._variable)

class TDefinicionDeFuncion(Termino):
    "Definición de función."

    def __init__(self, verbo, parametros, cuerpo, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._verbo = verbo
        self._parametros = parametros
        self._cuerpo = cuerpo

    def __unicode__(self):
        return u'TDefinicionDeFuncion(%s, [%s], %s)' % (
            self._verbo,
            ', '.join([unicode(param) for param in self._parametros]),
             self._cuerpo
        )

class TBegin(Termino):
    "Bloque."

    def __init__(self, expresiones, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._expresiones = expresiones

    def __unicode__(self):
        return u'TBegin([%s])' % (
            ', '.join([unicode(expr) for expr in self._expresiones]),
        )

