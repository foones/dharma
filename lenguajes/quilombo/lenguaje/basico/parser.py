# coding:utf-8

from lenguaje.parser import (
    Parser, PToken, PSecuencia, PSecuenciaConAccion, PAlternativa,
    PClausura1ConTerminadorConAccion,
    PComplemento, POpcional, PValor, PPalabra,
    PPalabras, PPuntuacion, PClausuraConTerminadorConAccion,
)
from lenguaje.ortografia import (
    normalizar_sustantivo_comun,
    es_verbo_infinitivo,
    normalizar_verbo_infinitivo,
)
from lenguaje.gramatica import (
    ARTICULOS, PREPOSICIONES, VOCATIVOS, APELATIVOS, NUMEROS_CARDINALES,
    PALABRAS_CLAVE,
)
from lenguaje.terminos import TVariable
from lenguaje.numeros.parser import PEnteroEnDiccionario

class PVerboInfinitivo(PToken):
    "Parser para verbos en infinitivo fijos."
    def __init__(self, raiz, **kwargs):
        PToken.__init__(self,
                        tipo='palabra',
                        predicado=lambda tok:
                                    es_verbo_infinitivo(tok.valor) and \
                                    normalizar_verbo_infinitivo(tok.valor) == raiz,
                        func_resultado=lambda tok: normalizar_verbo_infinitivo(tok.valor),
                        **kwargs
        )

class PVerboNuevoInfinitivoBasico(PToken):
    "Parser para nuevos verbos en infinitivo definidos por el usuario."

    def __init__(self, **kwargs):
        PToken.__init__(self,
                        tipo='palabra',
                        predicado=lambda tok: es_verbo_infinitivo(tok.valor, nuevo=True),
                        func_resultado=lambda tok: normalizar_verbo_infinitivo(tok.valor),
                        **kwargs
        )

class PVerboNuevoInfinitivo(PSecuenciaConAccion):
    """Parser para verbos en infinitivo definidos por el usuario,
       posiblemente decorados."""

    def __init__(self, **kwargs):

        def accion(lista):
            return lista[1]

        def accion_clausura(lista):
            return ' '.join(lista)

        def accion_interna(lista):
            res = lista[1]
            if lista[0] != ():
                res = lista[0][0] + ' ' + res
            return res

        PSecuenciaConAccion.__init__(self, accion,
            POpcional(
                PPalabras('agarrar y'),
            ),
            PAlternativa(
                PSecuenciaConAccion(lambda xs: u'<%s %s>' % (xs[1], xs[2]),
                    PPuntuacion('<'),
                    PVerboNuevoInfinitivoBasico(),
                    PClausuraConTerminadorConAccion(accion_clausura,
                        PSecuenciaConAccion(accion_interna,
                            POpcional(PPreposicion()),
                            PNominal()
                        ),
                        terminador=PPuntuacion('>'),
                    )
                ),
                PVerboNuevoInfinitivoBasico(),
            ),
            descripcion='un verbo en infinitivo',
            **kwargs
        )

class PAlternativaPalabras(PAlternativa):

    def __init__(self, palabras, **kwargs):
        PAlternativa.__init__(self, *[
                PPalabra(pal, resultado=pal)
                for pal in palabras
            ],
            **kwargs
        )

class PVocativo(PAlternativaPalabras):

    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, VOCATIVOS, **kwargs)

    def descripcion(self):
        return u'un vocativo (ej. `che\', `cuchame\')'

class PApelativo(PAlternativaPalabras):

    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, APELATIVOS, **kwargs)

    def descripcion(self):
        return u'un apelativo (ej. `boludo\', `hermano\')'

class PArticulo(PAlternativaPalabras):

    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, ARTICULOS, **kwargs)

    def descripcion(self):
        return u'un artículo (ej. `la\', `unos\')'

class PPreposicion(PAlternativaPalabras):

    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, PREPOSICIONES, **kwargs)

    def descripcion(self):
        return u'una preposición (ej. `de\', `contra\')'

class PSustantivoComun(PToken):

    def __init__(self, **kwargs):
        PToken.__init__(self,
            tipo='palabra',
            predicado=lambda tok: normalizar_sustantivo_comun(tok.valor) not in PALABRAS_CLAVE and \
                                  normalizar_sustantivo_comun(tok.valor)[:1].lower() == normalizar_sustantivo_comun(tok.valor)[:1],
            func_resultado=lambda tok: normalizar_sustantivo_comun(tok.valor),
            descripcion=u"un sustantivo común (ej. `moneda\', `bondi\')",
            **kwargs
        )

class PSustantivoPropioBasico(PToken):
    def __init__(self, **kwargs):
        PToken.__init__(self,
            tipo='palabra',
            predicado=lambda tok: tok.valor[:1].upper() == tok.valor[:1],
            func_resultado=lambda tok: tok.valor,
            descripcion=u"un sustantivo propio (ej. `Fulanito', `Juan Pérez')",
            **kwargs
        )

class PSustantivoPropio(PClausura1ConTerminadorConAccion):

    def __init__(self, devolver_variable=False, **kwargs):
        if devolver_variable:
            envolver = lambda x: TVariable(x)
        else:
            envolver = lambda x: x

        PClausura1ConTerminadorConAccion.__init__(self, lambda xs: envolver(' '.join(xs)),
            PSustantivoPropioBasico(),
            terminador=PComplemento(PSustantivoPropioBasico())
        )

class PNominal(PAlternativa):

    def __init__(self, articulo_obligatorio=False, devolver_variable=False, **kwargs):

        def accion(lista):
            art, sust = lista
            if art == ():
                palabras = [sust]
            else:
                palabras = [art[0], sust]
            if devolver_variable:
                return TVariable(sust)
            else:
                return sust

        art = PArticulo()
        if not articulo_obligatorio:
            art = POpcional(art)

        PAlternativa.__init__(self,
            PSustantivoPropio(devolver_variable=devolver_variable),
            PSecuenciaConAccion(accion, 
                art,
                PSustantivoComun(),
                **kwargs
            )
        )

    def descripcion(self):
        return u'una construcción nominal ' + \
               u'(ej. frase nominal común como `el mazo\' o nombre propio como `Juan Iberra\')'

class PComa(PPuntuacion):
    def __init__(self, **kwargs):
        PPuntuacion.__init__(self, ',', **kwargs)

class PPuntoFinal(PPuntuacion):
    def __init__(self, **kwargs):
        PPuntuacion.__init__(self, '.', **kwargs)

class PTerminadorFrase(PSecuencia):
    def __init__(self):
        PSecuencia.__init__(self,
            PPalabra('y'),
            PAlternativa(
                PPalabras('chau'),
                PPalabras('listo'),
                PPalabras('punto'),
                PPalabras('nada'),
                PPalabras('nada mas'),
                PPalabras('eso'),
                PPalabras('ya esta'),
            )
        )

