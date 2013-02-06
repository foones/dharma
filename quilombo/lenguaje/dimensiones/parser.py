from lenguaje.parser import (
    PAlternativa, PSecuenciaConAccion, POpcional, PClausuraConTerminadorConAccion,
    PPuntuacion, PPalabra, PTokenNumerico,
)
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
    TCantidad, TExpresarCantidadEn, TProductoCantidades, TPotenciaCantidad,
    INDICADOR_RECIPROCO,
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

class PUnidad(PAlternativa):

    def __init__(self):

        def accion(xs):
            return xs[1]

        def accion_clausura(xs):
            return TProductoCantidades(xs)

        def accion_interna(xs):
            if xs[0] == ():
                p = 1
            else:
                p = -1
            if xs[2] != ():
                p = p * xs[2][0]
            return TPotenciaCantidad(xs[1], p)

        PAlternativa.__init__(self,
            PNominal(devolver_variable=True),
            PSecuenciaConAccion(accion,
                PPuntuacion('<'),
                PClausuraConTerminadorConAccion(accion_clausura,
                    PSecuenciaConAccion(accion_interna,
                        POpcional(PPalabra(INDICADOR_RECIPROCO)),
                        PNominal(devolver_variable=True),
                        POpcional(
                            PSecuenciaConAccion(lambda xs: xs[1],
                                PPuntuacion('^'),
                                PTokenNumerico(),
                            )
                        )
                    ),
                    terminador=PPuntuacion('>'),
                )
            )
        )

class PCantidad(PNumeroEspecificado):

    def __init__(self):
        PNumeroEspecificado.__init__(self,
            parser_especificador_unidad=PUnidad(),
            envolver=lambda numero, unidad: TCantidad(numero, unidad)
        )

class PExpresarCantidadEn(PSecuenciaConAccion):
    def __init__(self, parser_expresion):
        def accion(xs):
            return TExpresarCantidadEn(xs[2])
        PSecuenciaConAccion.__init__(self, accion,
            PVerboInfinitivo('expres*'), PPalabras('en'),
            PUnidad(),
        )

