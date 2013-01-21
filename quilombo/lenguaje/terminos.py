# coding:utf-8

def unicode_list(xs):
    return ', '.join([unicode(x) for x in xs])

class Termino(object):
    "Cada instancia representa un término del lenguaje."

    def __init__(self, tokens=[]):
        self._tokens = tokens

    def tokens(self):
        return self._tokens

    def __repr__(self):
        return unicode(self)

class TNumero(Termino):
    "Términos que representan números."

    def __init__(self, numero, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)

        assert isinstance(numero, int) or \
               isinstance(numero, long) or \
               isinstance(numero, float)
        self._numero = numero

    def __add__(self, otro):
        return TNumero(self._numero + otro._numero, tokens=self.tokens())

    def __mul__(self, otro):
        return TNumero(self._numero * otro._numero, tokens=self.tokens())

    def __unicode__(self):
        return u'TNumero(%s)' % (self._numero,)

class TVariable(Termino):
    "Términos que representan variable."

    def __init__(self, nombre, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre = nombre

    def __unicode__(self):
        return u'TVariable(%s)' % (self._nombre,)

class TParametro(Termino):
    "Argumentos de una función."

    def __init__(self, preposicion, variable, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._preposicion = preposicion
        self._variable = variable

    def __unicode__(self):
        return u'TParametro(%s, %s)' % (self._preposicion, self._variable)

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
            unicode_list(self._parametros),
             self._cuerpo
        )

class TInvocarVerbo(Termino):
    u"Aplicación de un verbo a parámetros."

    def __init__(self, verbo, argumentos, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._verbo = verbo
        self._argumentos = argumentos

    def __unicode__(self):
        return u'TInvocarVerbo(%s, [%s])' % (
            self._verbo,
            unicode_list(self._argumentos)
        )


class TBegin(Termino):
    "Bloque."

    def __init__(self, expresiones, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._expresiones = expresiones

    def __unicode__(self):
        return u'TBegin([%s])' % (unicode_list(self._expresiones),)

