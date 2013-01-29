from lenguaje.parser import PSecuenciaConAccion
from lenguaje.basico.parser import PVocativo, PApelativo, PComa, PNominal, PPalabras
from lenguaje.numeros.parser import (
    PNumeroEspecificado,
)
from lenguaje.dimensiones.terminos import (
    TDefinicionDeDimension, TDefinicionDeUnidadBasica, TCantidad
)

class PDefinicionDeDimension(PSecuenciaConAccion):

    def __init__(self, **kwargs):
        def accion(xs):
            return TDefinicionDeDimension(xs[3])
        PSecuenciaConAccion.__init__(self, accion,
            PVocativo(), PApelativo(), PComa(),
            PNominal(),
            PPalabras('es una dimension'),
        )

class PDefinicionDeUnidadBasica(PSecuenciaConAccion):

    def __init__(self, parser_dimension, **kwargs):
        def accion(xs):
            return TDefinicionDeUnidadBasica(xs[3], xs[5])
        PSecuenciaConAccion.__init__(self, accion,
            PVocativo(), PApelativo(), PComa(),
            PNominal(),
            PPalabras('mide'),
            parser_dimension,
        )

class PCantidad(PNumeroEspecificado):
    def __init__(self):
        PNumeroEspecificado.__init__(self,
            parser_especificador_unidad=PNominal(),
            envolver=lambda numero, unidad: TCantidad(numero, unidad)
        )


#class PUnidadMonetaria(PAlternativa):
#    def __init__(self):
#        PAlternativa.__init__(self,
#            PEnteroEnDiccionario(NUMEROS_CARDINALES['unidad-monetaria']),
#            PValor(10 ** 6,
#                PAlternativa(
#                    PPalabras('palo verde'),
#                    PPalabras('palos verdes')
#                )
#            ),
#        )
#
