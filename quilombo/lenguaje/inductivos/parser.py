from lenguaje.parser import (
    PSecuenciaConAccion, PPuntuacion, PAlternativa,
    PClausuraConTerminador, PClausuraConTerminadorConAccion,
    PLookahead, PPalabra, POpcional,
)
from lenguaje.basico.parser import (
    PPalabras, PApelativo, PVocativo, PComa, PPreposicion, PNominal,
)
from lenguaje.inductivos.terminos import (
    TDefinicionDeTipoInductivo, TDeclaracionConstructorConParametros,
)

class PSeparadorUnionDisjunta(PAlternativa):

    def __init__(self):
        PAlternativa.__init__(self,
            PComa(),
            PPalabras('o quiza'),
            PPalabras('o quizas'),
            PPalabras('o capaz'),
            PPalabras('o tal vez'),
            PPalabras('o por ahi'),
        )

class PDeclaracionConstructorConParametros(PSecuenciaConAccion):

    def __init__(self):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TDeclaracionConstructorConParametros(xs[0], xs[1]),
            PNominal(),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: xs[2],
                    POpcional(PPalabra('y')),
                    POpcional(PPreposicion()),
                    PNominal(),
                ),
                terminador=PLookahead(
                               PAlternativa(
                                   PSeparadorUnionDisjunta(),
                                   PApelativo(),
                               ),
                           ),
            ),
        )

class PDefinicionDeTipoInductivo(PSecuenciaConAccion):

    def __init__(self):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TDefinicionDeTipoInductivo(xs[2], xs[4]),
            PVocativo(), PPuntuacion(','),
            PNominal(), # nombre del tipo
            PPalabras('puede ser'),
            PClausuraConTerminadorConAccion(lambda xs: xs,
                PDeclaracionConstructorConParametros(),
                terminador=PApelativo(),
                separador=PSeparadorUnionDisjunta(),
            ),
        )

