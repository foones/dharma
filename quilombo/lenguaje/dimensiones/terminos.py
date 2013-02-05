# coding:utf-8

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
                    TUnidadDeMedidaBasica(self._nombre_unidad, self._dimension)
                )
            )
        yield TNada()

class TCantidad(TerminoConstante):

    def __init__(self, numero, unidad, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._numero = numero
        while isinstance(unidad, TCantidad):
            unidad = unidad._unidad
        self._unidad = unidad

    def __unicode__(self):
        nombre_unidad_normalizado = unicode(self._unidad)

        if self._numero.es_singular():
            nombre_unidad = tesoro_actual().sustantivo_comun_singular(nombre_unidad_normalizado)
        else:
            nombre_unidad = tesoro_actual().sustantivo_comun_plural(nombre_unidad_normalizado)

        if tesoro_actual().sustantivo_comun_es_masculino(nombre_unidad_normalizado):
            genero = 'madj'
        else:
            genero = 'f'

        numero_escrito = self._numero.numero_escrito(genero)
        if not self._numero.es_exacto() or int(self._numero.valor_inferior()) % 10 ** 6 == 0:
            sep = ' de '
        else:
            sep = ' '

        return numero_escrito + sep + nombre_unidad

