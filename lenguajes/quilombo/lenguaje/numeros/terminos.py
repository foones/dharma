# coding:utf-8

import fractions

from comunes.utiles import frac

from lenguaje.terminos import TerminoConstante

class TNumero(TerminoConstante):
    "Términos que representan números."

    def __init__(self, numero=None, pico=0, a=None, b=None, *args, **kwargs):
        "Representa un número inexacto con aritmética de intervalos."
        TerminoConstante.__init__(self, *args, **kwargs)

        if numero is not None:
            assert isinstance(numero, int) or \
                   isinstance(numero, long) or \
                   isinstance(numero, fractions.Fraction)
            assert a is None and b is None
            assert pico >= 0
            if not isinstance(numero, fractions.Fraction):
                numero = frac(numero, 1)
            if pico == 0:
                a, b = numero, numero
            elif numero >= 0:
                a, b = numero, numero + pico
            else:
                a, b = numero - pico, numero
        else:
            assert a is not None and b is not None
        self._a, self._b = a, b

    def inf(self):
        return self._a

    def es_exacto(self):
        return self._a == self._b

    def valor_inferior(self):
        return self._a

    def es_singular(self):
        return self.es_exacto() and self.valor_inferior() == 1

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

    def __cmp__(self, otro):
        if not isinstance(otro, TNumero):
            return -1

        if self._a > otro._b:
            return 1
        elif self._b < otro._a:
            return -1
        else:
            return 0

    def __neg__(self):
        return self * TNumero(-1)

    def __div__(self, otro):
        return self * otro.inverso()

    def inverso(self):
        return TNumero(a=1 / self._a, b=1 / self._b)

    def __pow__(self, otro):
        if isinstance(otro, int) or isinstance(otro, long):
            if otro == 0:
                return TNumero(1)

            base = self
            if otro < 0:
                base = base.inverso()
                otro = -otro

            res = TNumero(1)
            while otro > 0:
                if otro % 2 == 1:
                    res = res * base
                otro = otro // 2
                base = base * base
            return res
        else:
            raise Exception(u'potencia de números en general no implementada')

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
        #if pico == 1: sbase += ' y pico'
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
        sbase = sbase.strip(' ')

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
            #if pico == 1: sbase += ' y pico'
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

    def _escribir_decimales(self, decimales):
        pals = []
        i = 0

        significativos = 0

        max_significativos = 1000
        max_i = 20

        while significativos < max_significativos or i < max_i:
            decimales *= 100
            num = int(decimales)
            decimales = decimales - num
            i += 2
            if num == 0:
                pals.append('cero')
                significativos *= 10
            elif num < 10:
                significativos = significativos * 10 + 1
                pals.append('cero')
                pals.append(self._numero_escrito_10(num, 0))
            elif num < 100:
                significativos += significativos * 100 + 1
                if num % 10 == 0:
                    pals.append(self._numero_escrito_10(num // 10, 0))
                    pals.append('cero')
                else:
                    pals.append(self._numero_escrito_100(num, 0))

        while pals != [] and pals[-1] == 'cero':
            pals.pop(-1)
        if pals == []:
            return ''
        else:
            sdec = ' coma ' + ' '.join(pals)
            sdec = sdec.replace('@', 'o')
            return sdec

    def numero_escrito(self, genero='f'):
        assert genero in ['msust', 'f', 'madj']

        ancho = self._b - self._a
        pico = 1
        while pico < ancho:
            pico *= 10
        if ancho == 0:
            pico = 0

        if pico != 0:
            while pico > 1 and int(self._a) // pico == 0:
                pico = pico // 10

        pico_decimal = False
        if pico == 0:
            restante = self._a - int(self._a)
            base = int(self._a)
        elif pico == 1:
            pico_decimal = True
            pico = 0
            min_restante = self._a - int(self._a)
            max_restante = self._b - int(self._b)

            nshifts = 0
            while nshifts < 20:
                nshifts += 1
                min_restante *= 10
                max_restante *= 10
                if int(min_restante) != int(max_restante):
                    break
            restante = float(int(min_restante)) / 10.0 ** nshifts
            base = int(self._a)
        else:
            restante = 0
            base = (int(self._a) // pico) * pico

        escrito = self._numero_escrito(base, pico)
        if genero == 'msust':
            escrito = escrito.replace('veintiun@ ', u'veintiún ')
            escrito = escrito.replace('un@ ', u'un ')
            escrito = escrito.replace('@', 'o')
        elif genero == 'f':
            escrito = escrito.replace('veintiun@ ', u'veintiún ')
            escrito = escrito.replace('un@ ', u'un ')
            escrito = escrito.replace('@', 'a')
        elif genero == 'madj':
            if restante == 0:
                escrito = escrito.replace('veintiun@', u'veintiún')
                escrito = escrito.replace('un@', u'un')
                escrito = escrito.replace('@', 'o')
            else:
                escrito = escrito.replace('veintiun@ ', u'veintiún ')
                escrito = escrito.replace('un@ ', u'un ')
                escrito = escrito.replace('@', 'o')

        if restante != 0:
            escrito += self._escribir_decimales(restante)
        if pico_decimal:
            escrito += ' y pico'
        return escrito

    def __unicode__(self):
        return self.numero_escrito()

