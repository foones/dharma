# coding:utf-8

import fractions
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

    def __init__(self, numero=None, pico=0, a=None, b=None, *args, **kwargs):
        "Representa un número inexacto con aritmética de intervalos."
        Termino.__init__(self, *args, **kwargs)

        if numero is not None:
            assert isinstance(numero, int) or \
                   isinstance(numero, long) or \
                   isinstance(numero, fractions.Fraction)
            assert a is None and b is None
            assert pico >= 0
            if not isinstance(numero, fractions.Fraction):
                numero = fractions.Fraction(numero, 1)
            if pico == 0:
                a, b = numero, numero
            elif numero >= 0:
                a, b = numero, numero + pico
            else:
                a, b = numero - pico, numero
        else:
            assert a is not None and b is not None
        self._a, self._b = a, b

    def __add__(self, otro):
        return TNumero(
            a=self._a + otro._a,
            b=self._b + otro._b,
            tokens=self.tokens()
        )

    def __mul__(self, otro):
        aa = self._a * otro._a
        ab = self._a * otro._b
        ba = self._b * otro._a
        bb = self._b * otro._b
        return TNumero(
            a=min(aa, ab, ba, bb),
            b=max(aa, ab, ba, bb),
            tokens=self.tokens()
        )

    def _numero_escrito_10(self, base, pico):
        assert 0 <= base and base < 10
        sbase = {
            0: '',
            1: 'un@',
            2: 'dos',
            3: 'tres',
            4: 'cuatro',
            5: 'cinco',
            6: 'seis',
            7: 'siete',
            8: 'ocho',
            9: 'nueve',
          }[base]
        if pico == 1: sbase += ' y pico'
        return sbase

    def _numero_escrito_100(self, base, pico):
        assert 0 <= base and base < 100
        if base < 10:
            return self._numero_escrito_10(base, pico)
        elif base < 30:
            sbase = {
                10: 'diez', 11: 'once', 12: 'doce', 13: 'trece',
                14: 'catorce', 15: 'quince', 16: u'dieciséis',
                17: 'diecisiete', 18: 'dieciocho', 19: 'diecinueve',
                20: 'veinte', 21: 'veintiun@', 22: u'veintidós',
                23: u'veintitrés', 24: 'veinticuatro', 25: 'veinticinco',
                26: u'veintiséis', 27: 'veintisiete', 28: 'veintiocho',
                29: 'veintinueve',
            }[base]
        else:
            decena = base // 10
            unidad = base % 10
            sdecena = {
                3: 'treinta', 4: 'cuarenta', 5: 'cincuenta',
                6: 'sesenta', 7: 'setenta', 8: 'ochenta',
                9: 'noventa',
            }[decena]
            sunidad = self._numero_escrito_10(unidad, pico)
            if unidad == 0:
                sbase = sdecena
            else:
                sbase = '%s y %s' % (sdecena, sunidad)
        if pico == 10:
            if sbase == 'veinte':
                sbase = 'veintipico'
            else:
                sbase += ' y pico'
        return sbase

    def _numero_escrito_1000(self, base, pico):
        assert 0 <= base and base < 1000
        if base < 100:
            return self._numero_escrito_100(base, pico)
        centena = base // 100
        resto = base % 100
        scentena = {
            1: 'ciento',
            2: 'doscient@s',
            3: 'trescient@s',
            4: 'cuatrocient@s',
            5: 'quinient@s',
            6: 'seiscient@s',
            7: 'setecient@s',
            8: 'ochocient@s',
            9: 'novecient@s',
        }[centena]
        sresto = self._numero_escrito_100(resto, pico)
        if centena == 1 and resto == 0 and pico != 100:
            sbase = 'cien'
        elif resto == 0:
            sbase = scentena
        else:
            sbase = '%s %s' % (scentena, sresto)
        if pico == 100:
            sbase += ' y pico'
        return sbase

    def _numero_escrito_millon(self, base, pico):
        assert 0 <= base and base < 10 ** 6
        if base < 1000:
            return self._numero_escrito_1000(base, pico)
        miles = base // 1000
        resto = base % 1000
        smiles = self._numero_escrito_1000(miles, pico // 1000)
        sresto = self._numero_escrito_1000(resto, pico)

        if miles == 1:
            smiles = ''

        if resto == 0:
            sbase = '%s mil' % (smiles,)
        else:
            sbase = '%s mil %s' % (smiles, sresto)

        if pico == 1000:
            sbase += ' y pico'
        return sbase

    def _numero_escrito(self, base, pico):
        assert 0 <= base and base < 10 ** (10 * 6)
        llones = [
            '', u'mill', u'bill', u'trill', u'cuatrill',
            u'quintill', u'sextill', u'septill', u'octill',
            u'nonill', u'decill'
        ]
        if base == 0:
            sbase = 'cero'
            if pico == 1:
                sbase += ' y pico'
            return sbase
        partes = []
        while base > 0:
            pot = 0
            while 10 ** (pot * 6) <= base:
                pot += 1
            pot -= 1
            potllon = 10 ** (pot * 6)
            cabeza = base // potllon 
            scabeza = self._numero_escrito_millon(cabeza, pico // potllon)

            if pot > 0 and cabeza > 1:
                sllon = ' ' + llones[pot] + u'ones'
            elif pot > 0:
                sllon = ' ' + llones[pot] + u'ón'
            else:
                sllon = ''

            if cabeza < 10 and scabeza.endswith(' y pico'):
                scabeza = scabeza[:-len(' y pico')]
            if pico == potllon:
                sllon += ' y pico'

            partes.append(scabeza + sllon)
            base = base % potllon

        return ' '.join(partes)

    def numero_escrito(self, genero='f'):
        assert genero in ['msust', 'f', 'madj']

        ancho = self._b - self._a
        pico = 1
        while pico < ancho:
            pico *= 10
        if ancho == 0:
            pico = 0

        if pico == 0:
            restante = self._a - int(self._a)
            base = int(self._a)
        else:
            restante = 0
            base = (int(self._a) // pico) * pico

        escrito = self._numero_escrito(base, pico) + '=== CON DECIMALES %s' % (restante,)
        if genero == 'msust':
            escrito = escrito.replace('veintiun@ ', u'veintiún ')
            escrito = escrito.replace('un@ ', u'un ')
            escrito = escrito.replace('@', 'o')
        elif genero == 'f':
            print 'antes', escrito
            escrito = escrito.replace('veintiun@ ', u'veintiún ')
            escrito = escrito.replace('un@ ', u'un ')
            escrito = escrito.replace('@', 'a')
        elif genero == 'madj':
            escrito = escrito.replace('veintiun@', u'veintiún')
            escrito = escrito.replace('un@', u'un')
        return escrito

    def __unicode__(self):
        return self.numero_escrito()

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

