from lenguaje.parser import PAlternativa, PSecuenciaConAccion
from lenguaje.basico.parser import (
    PVocativo, PApelativo, PComa, PNominal, PPalabras, PAlternativaPalabras,
    PVerboInfinitivo,
)
from lenguaje.terminos import TVariable
from lenguaje.numeros.parser import (
    PNumeroEspecificado,
)
from lenguaje.dimensiones.terminos import (
    TDefinicionDeDimension, TDefinicionDeUnidadBasica, TDefinicionDeUnidadDerivada,
    TCantidad, TExpresarCantidadEn,
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

    def __init__(self, parser_expresion, **kwargs):
        def accion(xs):
            return TDefinicionDeUnidadBasica(xs[3], xs[5])
        PSecuenciaConAccion.__init__(self, accion,
            PVocativo(), PApelativo(), PComa(),
            PNominal(),
            PPalabras('mide'),
            PAlternativa(
                PNominal(devolver_variable=True),
                parser_expresion,
            )
        )

class PDefinicionDeUnidadDerivada(PSecuenciaConAccion):

    def __init__(self, parser_expresion, **kwargs):
        def accion(xs):
            return TDefinicionDeUnidadDerivada(xs[3], xs[5])
        PSecuenciaConAccion.__init__(self, accion,
            PVocativo(), PApelativo(), PComa(),
            PNominal(),
            PAlternativaPalabras(['es', 'son']),
            parser_expresion,
        )

class PCantidad(PNumeroEspecificado):
    def __init__(self):
        PNumeroEspecificado.__init__(self,
            parser_especificador_unidad=PNominal(),
            envolver=lambda numero, unidad: TCantidad(numero, TVariable(unidad))
        )

class PExpresarCantidadEn(PSecuenciaConAccion):

    def __init__(self, parser_expresion):
        def accion(xs):
            return TExpresarCantidadEn(xs[2])
        PSecuenciaConAccion.__init__(self, accion,
            PVerboInfinitivo('expres*'), PPalabras('en'),
            PNominal(devolver_variable=True),
            #PAlternativa(
            #    parser_expresion,
            #),
        )

