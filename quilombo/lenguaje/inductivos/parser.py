from lenguaje.parser import PSecuenciaConAccion
from lenguaje.basico.parser import PPalabras

class PDefinicionDeTipoInductivo(PSecuenciaConAccion):

    def __init__(self):
        PSecuenciaConAccion.__init__(self, lambda xs: xs[1],
            PPalabras('che'),
        )

