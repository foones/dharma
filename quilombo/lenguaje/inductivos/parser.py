from lenguaje.parser import (
    PSecuenciaConAccion, PPuntuacion, PAlternativa,
    PClausuraConTerminador, PClausuraConTerminadorConAccion,
    PLookahead, PPalabra, POpcional,
)
from lenguaje.basico.parser import (
    PPalabras, PApelativo, PVocativo, PComa, PPreposicion, PNominal,
    PAlternativaPalabras, PVerboInfinitivo,
)
from lenguaje.inductivos.terminos import (
    TDefinicionDeTipoInductivo, TDeclaracionConstructorConParametros,
    TAplicacionTotalConstructor, TAplicacionParcialConstructor,
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

from lenguaje.terminos import TNada

class PAplicacionTotalConstructor(PSecuenciaConAccion):

    def __init__(self, parser_expresion):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TAplicacionTotalConstructor(xs[1]),
            PAlternativa(
                PVerboInfinitivo('cre*'),
                PVerboInfinitivo('constru*'),
            ),
            parser_expresion,
        )

class PAplicacionParcialConstructor(PSecuenciaConAccion):

    def __init__(self, parser_expresion):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TAplicacionParcialConstructor(xs[1], xs[3]),
            PAlternativaPalabras(['cuyo', 'cuya', 'cuyos', 'cuyas']),
            PNominal(),
            PAlternativaPalabras(['es', 'son', 'sea', 'sean']),
            parser_expresion,
        )

