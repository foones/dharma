# coding:utf-8

from lenguaje.terminos import Termino, TerminoConstante, TNada

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
                TUnidadDeMedidaBasica(self._nombre_unidad, self._dimension)
            )
        yield TNada()

class TCantidad(TerminoConstante):

    def __init__(self, numero, unidad, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._numero = numero
        self._unidad = unidad

    def __unicode__(self):
        return self._numero.numero_escrito() + ' ' + unicode(self._unidad)

