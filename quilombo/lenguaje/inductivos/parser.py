from lenguaje.parser import (
    PSecuenciaConAccion, PPuntuacion, PAlternativa,
    PClausuraConTerminadorConAccion, PLookahead,
)
from lenguaje.basico.parser import (
    PPalabras, PApelativo, PVocativo, PComa, PPreposicion, PNominal,
)
from lenguaje.terminos import TNada

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

class PConstructorConParametros(PSecuenciaConAccion):

    def __init__(self):
        PSecuenciaConAccion.__init__(self, lambda xs: TNada(),
            PNominal(),
            PClausuraConTerminadorConAccion(lambda xs: xs,
                PSecuenciaConAccion(lambda xs: xs,
                    PPreposicion(),
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
        PSecuenciaConAccion.__init__(self, lambda xs: TNada(),
            PVocativo(), PPuntuacion(','),
            PNominal(), # nombre del tipo
            PPalabras('puede ser'),
            PClausuraConTerminadorConAccion(lambda xs: xs,
                PConstructorConParametros(),
                terminador=PApelativo(),
                separador=PSeparadorUnionDisjunta(),
            ),
        )

