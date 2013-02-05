# coding:utf-8

from comunes.utiles import QuilomboException
from lenguaje.terminos import Termino, TerminoConstante, TNada
from lenguaje.tesoro import tesoro_actual
from lenguaje.numeros.terminos import TNumero

class TDimension(TerminoConstante):
    u"""Representa una dimensión. Por ejemplo "distancia",
        "distancia sobre tiempo", etc."""

    def __init__(self, potencias, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._potencias = {}
        for k, v in potencias.items():
            if v == 0:
                continue
            self._potencias[k] = v

    def __unicode__(self):
        positivos = []
        negativos = []
        for k, v in self._potencias.items():
            if v > 0:
                dst = positivos
                mul = 1
            else:
                dst = negativos
                mul = -1
            v = mul * v
            if v == 1:
                dst.append(u'%s' % (k,))
            else:
                dst.append(u'%s^%s' % (k, v))

        positivos = ' '.join(positivos)
        negativos = ' '.join(negativos)
        if positivos == '':
            positivos = 1
        if negativos == '':
            return u'%s' % (positivos,)
        else:
            return u'%s sobre %s' % (positivos, negativos)

class TUnidadDeMedidaBasica(TerminoConstante):
    u"""Representa una unidad de medida. Por ejemplo "metro",
        "peso", etc."""

    def __init__(self, nombre_unidad, dimension, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._nombre_unidad = nombre_unidad
        self._dimension = dimension

    def __unicode__(self):
        return u'%s' % (self._nombre_unidad,)

class TUnidadDeMedidaDerivada(TerminoConstante):
    u"""Representa una unidad de medida derivada (múltiplo) de otra.
        Por ejemplo "kilómetro" (1000 metros), etc."""

    def __init__(self, nombre_unidad, cantidad, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._nombre_unidad = nombre_unidad
        self._cantidad = cantidad

    def cantidad(self):
        return self._cantidad

    def __unicode__(self):
        return u'%s' % (self._nombre_unidad,)

class TDefinicionDeDimension(Termino):

    def __init__(self, nombre_dimension, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre_dimension = nombre_dimension

    def __unicode__(self):
        return u'TDefinicionDeDimension(%s)' % (self._nombre_dimension,)

    def evaluar_en(self, estado):
        estado.entorno.declarar(self._nombre_dimension,
            TDimension({self._nombre_dimension: 1})
        )
        yield TNada()

class TDefinicionDeUnidadBasica(Termino):

    def __init__(self, nombre_unidad, dimension, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre_unidad = nombre_unidad
        self._dimension = dimension

    def __unicode__(self):
        return u'TDefinicionDeUnidadBasica(%s, %s)' % (self._nombre_unidad, self._dimension)

    def evaluar_en(self, estado):
        for dimension in self._dimension.evaluar_en(estado):
            estado.entorno.declarar(self._nombre_unidad,
                TCantidad(
                    TNumero(1),
                    TUnidadDeMedidaBasica(self._nombre_unidad, dimension)
                )
            )
        yield TNada()

class TDefinicionDeUnidadDerivada(Termino):

    def __init__(self, nombre_unidad, cantidad, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._nombre_unidad = nombre_unidad
        self._cantidad = cantidad

    def __unicode__(self):
        return u'TDefinicionDeUnidadDerivada(%s, %s)' % (
            self._nombre_unidad,
            self._cantidad,
        )

    def evaluar_en(self, estado):
        for cantidad in self._cantidad.evaluar_en(estado):
            estado.entorno.declarar(self._nombre_unidad,
                TCantidad(
                    TNumero(1),
                    TUnidadDeMedidaDerivada(self._nombre_unidad, cantidad),
                )
            )
        yield TNada()

def _real_unidad(unidad):
    u = unidad
    while isinstance(u, TCantidad):
        u = u.unidad
    return u

class TCantidad(Termino):

    def __init__(self, numero, unidad, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self.numero = numero
        self.unidad = unidad

    def __unicode__(self):
        unidad = _real_unidad(self.unidad)
        nombre_unidad_normalizado = unicode(unidad)

        if self.numero.es_singular():
            nombre_unidad = tesoro_actual().sustantivo_comun_singular(nombre_unidad_normalizado)
        else:
            nombre_unidad = tesoro_actual().sustantivo_comun_plural(nombre_unidad_normalizado)

        if tesoro_actual().sustantivo_comun_es_masculino(nombre_unidad_normalizado):
            genero = 'madj'
        else:
            genero = 'f'

        numero_escrito = self.numero.numero_escrito(genero)

        intval = int(self.numero.valor_inferior())
        llon_redondo = intval % 10 ** 6 == 0 and intval != 0
        if not self.numero.es_exacto() or llon_redondo:
            sep = u' de '
        else:
            sep = u' '

        return numero_escrito + sep + nombre_unidad

    def evaluar_en(self, estado):
        for numero in self.numero.evaluar_en(estado):
            for unidad in self.unidad.evaluar_en(estado):
                yield TCantidad(numero, unidad)

class TExpresarCantidadEn(Termino):

    def __init__(self, unidad, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._unidad = unidad

    def __unicode__(self):
        return u'TExpresarCantidadEn(%s)' % (self._unidad,)

    def _reducir(self, unidad):
        n = TNumero(1)
        u = unidad
        while True:
            if isinstance(u, TCantidad):
                n = n * u.numero
                u = u.unidad
            elif isinstance(u, TUnidadDeMedidaDerivada):
                u = u.cantidad()
            else:
                break
        return n, u

    def evaluar_en(self, estado):
        #for cantidad in self._cantidad.evaluar_en(estado):
        cantidad = estado.pop()
        for unidad in self._unidad.evaluar_en(estado):
            np, up = self._reducir(cantidad)
            nq, uq = self._reducir(unidad)
            if up != uq:
                raise QuilomboException(u'la cantidad "%s" no se puede expresar en la unidad "%s"' % (cantidad, unidad))
            yield TCantidad(np / nq, _real_unidad(unidad))

