# coding:utf-8

from comunes.utiles import QuilomboException, identar

def unicode_list(xs, sep=u', '):
    return sep.join([unicode(x) for x in xs])

class Entorno(object):
    "Un entorno es una pila de 'costillas' que asocian nombres a valores."

    def __init__(self):
        self._entorno = [{}]

    def push(self):
        self._entorno.append({})

    def pop(self):
        self._entorno.pop(-1)

    def declarar(self, nombre, valor=None):
        if nombre in self._entorno[-1]:
            raise QuilomboException('Epa: "%s" ya estaba declarada.' % (nombre,))
        self._entorno[-1][nombre] = valor

    def asignar(self, nombre, valor):
        for costilla in reversed(self._entorno):
            if nombre in costilla:
                costilla[nombre] = valor
                return valor
        raise QuilomboException('Epa: "%s" no estaba ligada.' % (nombre,))

    def valor(self, nombre):
        for costilla in reversed(self._entorno):
            if nombre in costilla:
                return costilla[nombre]
        raise QuilomboException('Epa: "%s" no estaba ligada.' % (nombre,))

class Termino(object):
    "Cada instancia representa un término del lenguaje."

    def __init__(self, tokens=[]):
        self._tokens = tokens

    def tokens(self):
        return self._tokens

    #def __repr__(self):
    #    return unicode(self)

class TNumero(Termino):
    "Términos que representan números."

    def __init__(self, numero, pico=0, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)

        assert isinstance(numero, int) or \
               isinstance(numero, long) or \
               isinstance(numero, float)
        self._numero = numero
        self._pico = pico

    def __add__(self, otro):
        return TNumero(
            self._numero + otro._numero,
            pico=self._pico + otro._pico,
            tokens=self.tokens()
        )

    def __mul__(self, otro):
        return TNumero(
            self._numero * otro._numero,
            pico=self._pico * otro._numero + otro._pico * self._numero + self._pico * otro._pico,
            tokens=self.tokens()
        )

    def __unicode__(self):
        if self._pico == 0:
            return u'TNumero(%s)' % (self._numero,)
        else:
            return u'TNumero(%s + pico=%s)' % (self._numero, self._pico)

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

class TBegin(Termino):
    "Bloque."

    def __init__(self, expresiones, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._expresiones = expresiones

    def __unicode__(self):
        return u'TBegin([\n%s\n])' % (identar(unicode_list(self._expresiones, sep=u',\n')),)

