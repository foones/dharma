from lenguaje.parser import PSecuenciaConAccion, PAlternativa, POpcional
from lenguaje.basico.parser import PVerboInfinitivo, PPalabras
from lenguaje.pila.terminos import TMeterElemento

class PMeterElemento(PSecuenciaConAccion):

    def __init__(self, parser_expresion):
        PSecuenciaConAccion.__init__(self,
            lambda xs: TMeterElemento(xs[2]),
            PAlternativa(
                PVerboInfinitivo('met*'),
                PVerboInfinitivo('guard*'),
            ),
            POpcional(PPalabras('el resultado de')),
            parser_expresion,
        )

