from lenguaje.parser import PSecuenciaConAccion
from lenguaje.basico.parser import PVocativo, PApelativo, PComa, PNominal, PPalabras
from lenguaje.dimensiones.terminos import TDefinicionDeDimension

class PDefinicionDeDimension(PSecuenciaConAccion):
    def __init__(self, **kwargs):
        def accion(xs):
            return TDefinicionDeDimension(xs[3])
        PSecuenciaConAccion.__init__(self, accion,
            PVocativo(), PApelativo(), PComa(),
            PNominal(),
            PPalabras('es una dimension'),
        )
