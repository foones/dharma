# coding:utf-8

from comunes.utiles import QuilomboException
from lenguaje.terminos import Termino, TerminoConstante, TNada
from lenguaje.tesoro import tesoro_actual
from lenguaje.numeros.terminos import TNumero

INDICADOR_RECIPROCO = 'por'

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
        negativos = ' '.join([u'%s %s' % (INDICADOR_RECIPROCO, n,) for n in negativos])
        if positivos == '':
            positivos = 1
        if negativos == '':
            return u'%s' % (positivos,)
        else:
            return u'%s %s' % (positivos, negativos)

    def __repr__(self):
        return unicode(self)

    def __mul__(self, otra_dimension):
        a = self
        b = otra_dimension
        d = {}
        for k, v in a._potencias.items():
            d[k] = v
        for k, v in b._potencias.items():
            d[k] = d.get(k, 0) + v
        return TDimension(d)

    def __pow__(self, p):
        d = {}
        if p == 0:
            return TDimension({})
        for k, v in self._potencias.items():
            d[k] = v * p
        return TDimension(d)

    def __cmp__(self, otra_dimension):
        assert isinstance(otra_dimension, TDimension)
        a = self
        b = otra_dimension
        for k in a._potencias.keys():
            if k not in b._potencias:
                return -1
        for k in b._potencias.keys():
            if k not in a._potencias:
                return 1
        for k in a._potencias.keys():
            c = cmp(a._potencias[k], b._potencias[k])
            if c != 0:
                return c
        return 0

class TUnidadDeMedidaBasica(TerminoConstante):
    u"""Representa una unidad de medida. Por ejemplo "metro",
        "peso", etc."""

    def __init__(self, nombre_unidad, dimension, *args, **kwargs):
        TerminoConstante.__init__(self, *args, **kwargs)
        self._nombre_unidad = nombre_unidad
        self._dimension = dimension

    def __unicode__(self):
        return u'%s' % (self._nombre_unidad,)

    def mostrar(self, flexion_numero):
        if flexion_numero == 's':
            return tesoro_actual().sustantivo_comun_singular(self._nombre_unidad)
        else:
            return tesoro_actual().sustantivo_comun_plural(self._nombre_unidad)

    def identificador(self):
        return self._nombre_unidad

    def dimension(self):
        return self._dimension

    def __cmp__(self, otra_unidad_basica):
        assert isinstance(otra_unidad_basica, TUnidadDeMedidaBasica)
        return self._nombre_unidad == otra_unidad_basica._nombre_unidad

    def en_unidades_basicas(self):
        return TUnidadDeMedidaCompuesta({self: 1})

    def en_unidades_naturales(self):
        return self.en_unidades_basicas()

    def __pow__(self, p):
        return TUnidadDeMedidaCompuesta({self: p})

class TUnidadDeMedidaCompuesta(TerminoConstante):

    def __init__(self, unidades_potencias, coeficiente=None, nombre=None):

        u"""`unidades_potencias' es un diccionario con items de la forma
            (u, p) donde u es una unidad básica o compuesta
            y p es un entero (que puede ser negativo).

            Internamente se guarda siempre como un diccionario
            que mapea nombres de unidades básicas a potencias, y
            un coeficiente multiplicativo.

            El diccionario vacío con coeficiente 1 representa la unidad
            adimensional."""
        self._potencias = {}
        for u, p in unidades_potencias.items():
            if p == 0:
                continue
            self._potencias[u] = p

        if coeficiente == None:
            coeficiente = TNumero(1)
        self._coeficiente = coeficiente

        self._nombre = nombre

    def dimension(self):
        dimension = TDimension({})
        for u, p in self._potencias.items():
            dimension = dimension * u.dimension() ** p
        return dimension

    def __pow__(self, p):
        return TUnidadDeMedidaCompuesta({self: p})

    def __mul__(self, otra_unidad):
        return TUnidadDeMedidaCompuesta({self: 1, otra_unidad: 1})

    def true_pow(self, p):
        d = {}
        for k, v in self._potencias.items():
            d[k] = v * p
        return TUnidadDeMedidaCompuesta(d, coeficiente=self._coeficiente ** p)

    def true_mul(self, otra_unidad):
        assert isinstance(otra_unidad, TUnidadDeMedidaCompuesta)
        a = self
        b = otra_unidad
        d = {}
        for k, v in a._potencias.items():
            d[k] = v
        for k, v in b._potencias.items():
            d[k] = d.get(k, 0) + v
        return TUnidadDeMedidaCompuesta(d, coeficiente=self._coeficiente * otra_unidad._coeficiente)

    def __unicode__(self):
        return self.mostrar('s')

    def mostrar(self, flexion_numero):
        if self._nombre is not None:
            if flexion_numero == 's':
                return tesoro_actual().sustantivo_comun_singular(self._nombre)
            else:
                return tesoro_actual().sustantivo_comun_plural(self._nombre)
        res = []
        for k, v in self._potencias.items():
            if v < 0:
                s = '%s ' % (INDICADOR_RECIPROCO,)
                neg = True
                v = -v
            else:
                neg = False
                s = ''
            s += u'%s' % (k.mostrar(flexion_numero if not neg else 's'),)
            if v > 1:
                s += '^%s' % (v,)
            res.append(s)

        if not self._coeficiente.es_singular():
            return '<' + unicode(self._coeficiente) + ' ' + ' '.join(res) + '>'
        else:
            return ' '.join(res)

    def en_unidades_basicas(self):
        res = TUnidadDeMedidaCompuesta({}, self._coeficiente)
        for u, p in self._potencias.items():
            u2 = u.en_unidades_basicas()
            res = res.true_mul(u2.true_pow(p))
        return res

    def en_unidades_naturales(self):
        if self._nombre is not None:
            return self
        d = {}
        for u, p in self._potencias.items():
            u2 = u.en_unidades_naturales()
            d[u2] = d.get(u2, 0) + p
        return TUnidadDeMedidaCompuesta(d, self._coeficiente)

    def extraer_coeficiente(self):
        return self._coeficiente, TUnidadDeMedidaCompuesta(self._potencias)

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
                    TUnidadDeMedidaCompuesta({
                        TUnidadDeMedidaBasica(self._nombre_unidad, dimension): 1,
                    }),
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
                    TUnidadDeMedidaCompuesta(
                        {cantidad.unidad: 1},
                        coeficiente=cantidad.numero,
                        nombre=self._nombre_unidad,
                    )
                )
            )
        yield TNada()

def _real_unidad(unidad):
    u = unidad
    while isinstance(u, TCantidad):
        u = u.unidad
    return u

def _reducir_unidad(unidad):
    n = TNumero(1)
    u = unidad
    while True:
        if isinstance(u, TCantidad):
            n = n * u.numero
            u = u.unidad
        else:
            break
    return n, u

class TCantidad(Termino):

    def __init__(self, numero, unidad, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self.numero = numero
        self.unidad = unidad

    def __unicode__(self):
        if isinstance(self.unidad, TUnidadDeMedidaCompuesta) or isinstance(self.unidad, TCantidad):
            return self.mostrar('s')
        else:
            return u'TCantidad(%s, %s)' % (self.numero, self.unidad)

    def mostrar(self, flexion_numero):
        numero = self.numero
        factor, unidad = self.unidad.en_unidades_naturales().extraer_coeficiente()
        numero = numero * factor

        fn = 's' if numero.es_singular() else 'p'
        nombre_unidad_normalizado = unidad.mostrar(fn)

        nombre_unidad = nombre_unidad_normalizado
        if ' ' in nombre_unidad_normalizado or nombre_unidad_normalizado == '':
            nombre_unidad = u'<%s>' % (nombre_unidad_normalizado,)

        nombre_unidad_normalizado = nombre_unidad_normalizado.split(' ')[0]
        if tesoro_actual().sustantivo_comun_es_masculino(nombre_unidad_normalizado):
            genero = 'madj'
        else:
            genero = 'f'

        numero_escrito = numero.numero_escrito(genero)

        intval = int(numero.valor_inferior())
        llon_redondo = intval % 10 ** 6 == 0 and intval != 0
        if not numero.es_exacto() or llon_redondo:
            sep = u' de '
        else:
            sep = u' '

        return numero_escrito + sep + nombre_unidad

    def __mul__(self, otro):
        assert isinstance(otro, TCantidad)
        return TCantidad(
            self.numero * otro.numero,
            self.unidad * otro.unidad,
        )

    def __pow__(self, potencia):
        if isinstance(potencia, int) or isinstance(potencia, long):
            return TCantidad(
                self.numero ** potencia,
                self.unidad ** potencia,
            )
        else:
            raise Exception(u'potencia de una cantidad a otra cosa que no sea un entero no implementada')

    def evaluar_en(self, estado):
        for numero in self.numero.evaluar_en(estado):
            for unidad in self.unidad.evaluar_en(estado):
                yield TCantidad(numero, unidad)

    def en_unidades_basicas(self):
        basica = self.unidad.en_unidades_basicas()
        return basica.true_mul(TUnidadDeMedidaCompuesta({}, coeficiente=self.numero))

    def en_unidades_naturales(self):
        natural = self.unidad.en_unidades_naturales()
        return TUnidadDeMedidaCompuesta({natural: 1}, coeficiente=self.numero)

class TExpresarCantidadEn(Termino):

    def __init__(self, unidad, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._unidad = unidad

    def __unicode__(self):
        return u'TExpresarCantidadEn(%s)' % (self._unidad,)

    def evaluar_en(self, estado):
        cantidad = estado.pop()
        for unidad in self._unidad.evaluar_en(estado):
            np, up = _reducir_unidad(cantidad)
            nq, uq = _reducir_unidad(unidad)
            dp = up.dimension()
            dq = uq.dimension()
            if dp != dq:
                raise QuilomboException(u'la cantidad "%s" es de dimensión "%s" y no se puede expresar en la unidad "%s" que es de dimensión "%s"' % (cantidad, dp, unidad, dq))
            #np, up = _reducir_unidad(cantidad)
            #nq, uq = _reducir_unidad(unidad)
            #if up != uq:
            #    raise QuilomboException(u'la cantidad "%s" no se puede expresar en la unidad "%s"' % (cantidad, unidad))
            #yield TCantidad(np / nq, _real_unidad(unidad))
            yield TNada()

class TProductoCantidades(Termino):

    def __init__(self, cantidades, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._cantidades = cantidades

    def __unicode__(self):
        return u'TProductoCantidades(%s)' % (self._cantidades,)

    def _evaluar_lista_en(self, xs, estado):
        if xs == []:
            yield []
        else:
            for y in xs[0].evaluar_en(estado):
                for ys in self._evaluar_lista_en(xs[1:], estado):
                    yield [y] + ys

    def evaluar_en(self, estado):
        if len(self._cantidades) == 0:
            yield TCantidad(TNumero(1), TUnidadDeMedidaCompuesta({}))
            return

        for cs in self._evaluar_lista_en(self._cantidades, estado):
            res = cs[0]
            for c in cs[1:]:
                res = res * c
            yield res

class TPotenciaCantidad(Termino):

    def __init__(self, cantidad, potencia, *args, **kwargs):
        Termino.__init__(self, *args, **kwargs)
        self._cantidad = cantidad
        self._potencia = potencia

    def __unicode__(self):
        return u'TPotenciaCantidad(%s, %s)' % (self._cantidad, self._potencia)

    def evaluar_en(self, estado):
        for cantidad in self._cantidad.evaluar_en(estado):
            yield cantidad ** self._potencia

