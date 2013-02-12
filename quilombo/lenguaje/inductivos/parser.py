from lenguaje.parser import (
    PSecuencia, PSecuenciaConAccion, PPuntuacion, PAlternativa,
    PClausuraConTerminador, PClausuraConTerminadorConAccion,
    PLookahead, PPalabra, POpcional,
)
from lenguaje.basico.parser import (
    PPalabras, PApelativo, PVocativo, PComa, PPreposicion, PNominal,
    PAlternativaPalabras, PVerboInfinitivo, PTerminadorFrase,
)
from lenguaje.inductivos.terminos import (
    TDefinicionDeTipoInductivo, TDeclaracionConstructorConParametros,
    TAplicacionDirectaConstructor, TAplicacionTotalConstructor,
    TAplicacionParcialConstructor,
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

class PAplicacionDirectaConstructor(PSecuenciaConAccion):

    def __init__(self, parser_expresion, parser_terminador_constructor):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TAplicacionDirectaConstructor(xs[0], xs[2]),
            PNominal(devolver_variable=True),
            PSecuencia(
                PPalabras('que'),
                PAlternativaPalabras(['tiene', 'tienen', 'tenga', 'tengan']),
            ),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: (xs[1], xs[3]),
                    POpcional(PPreposicion()),
                    PNominal(),
                    POpcional(PPuntuacion(':')),
                    parser_expresion,
                ),
                separador=PPuntuacion(','),
                terminador=parser_terminador_constructor,
            ),
        )

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

class PAnalisisDeCasosTopePila(PSecuenciaConAccion):

    def __init__(self, parser_expresion):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TNada(),
            PVerboInfinitivo('fij*'),
            PClausuraConTerminador(
                PSecuencia(
                    PPalabra('si'),
                    PAlternativaPalabras(['es', 'son']),
                    PAlternativa(
                        PSecuencia(PNominal(), PPalabra('entonces')),
                        PAplicacionDirectaConstructor(parser_expresion, PPalabra('entonces')),
                    ),
                    parser_expresion,
                ),
                separador=PPuntuacion(','),
                terminador=PTerminadorFrase(),
            ),
        )

