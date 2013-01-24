# coding:utf-8

from parser import (
    Parser, PToken, PSecuencia, PSecuenciaConAccion, PAlternativa,
    PClausuraConTerminador, PClausuraConTerminadorConAccion,
    PComplemento, PLookahead, POpcional, PValor, PPalabra,
    PPalabras, PPuntuacion,
)
from idioma.gramatica import (
    ARTICULOS, PREPOSICIONES, VOCATIVOS, APELATIVOS, NUMEROS_CARDINALES,
    PALABRAS_CLAVE,
)
from lenguaje.terminos import (
    TVariable, TParametro, TDefinicionDeFuncion, TInvocarVerbo, TBloque,
)
from lenguaje.numeros.parser import (
    PEnteroEnDiccionario, PNumeroEspecificado
)

VERBOS_RESERVADOS = ['agarrar']

class PVerboNuevoInfinitivoBasico(PToken):
    "Parser para nuevos verbos en infinitivo definidos por el usuario."

    def __init__(self, **kwargs):

        desinencias = ['ar', 'er', 'ir']
        sufijos = ['lo', 'le', 'los', 'les', 'se', 'selo', 'selos']

        def es_verbo_infinitivo(tok):
            if tok.valor[:1].lower() != tok.valor[:1]:
                return False
            if tok.valor in VERBOS_RESERVADOS:
                return False
            for d in desinencias:
                for s in [''] + sufijos:
                    if tok.valor.endswith(d + s):
                        return True
            return False

        def sacar_sufijos(tok):
            res = tok.valor
            for s in sufijos:
                if res.endswith(s):
                    res = res[:-len(s)]
                    break
            for d in desinencias:
                if res.endswith(d):
                    res = res[:-len(d)]
                    break
            return res + '*'

        PToken.__init__(self,
                        tipo='palabra',
                        predicado=es_verbo_infinitivo,
                        func_resultado=sacar_sufijos,
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
            **kwargs
        )

class PUnidadMonetaria(PAlternativa):
    def __init__(self):
        PAlternativa.__init__(self,
            PEnteroEnDiccionario(NUMEROS_CARDINALES['unidad-monetaria']),
            PValor(10 ** 6,
                PAlternativa(
                    PPalabras('palo verde'),
                    PPalabras('palos verdes')
                )
            ),
        )

class PPlata(PNumeroEspecificado):
    def __init__(self):
        PNumeroEspecificado.__init__(self,
            parser_especificador_unidad=PUnidadMonetaria(),
            envolver=lambda valor, unidad: valor * unidad
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

class PApelativo(PAlternativaPalabras):
    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, APELATIVOS, **kwargs)

class PArticulo(PAlternativaPalabras):
    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, ARTICULOS, **kwargs)

class PPreposicion(PAlternativaPalabras):
    def __init__(self, **kwargs):
        PAlternativaPalabras.__init__(self, PREPOSICIONES, **kwargs)

class PSustantivoComun(PToken):

    def __init__(self, **kwargs):
        PToken.__init__(self,
            tipo='palabra',
            predicado=lambda tok: tok.valor not in PALABRAS_CLAVE and \
                                  tok.valor[:1].lower() == tok.valor[:1],
            func_resultado=lambda tok: tok.valor,
            **kwargs
        )

class PSustantivoPropioBasico(PToken):
    def __init__(self, **kwargs):
        PToken.__init__(self,
            tipo='palabra',
            predicado=lambda tok: tok.valor[:1].upper() == tok.valor[:1],
            func_resultado=lambda tok: tok.valor,
            **kwargs
        )

class PSustantivoPropio(PSecuenciaConAccion):

    def __init__(self, devolver_variable=False, **kwargs):
        if devolver_variable:
            envolver = lambda x: TVariable(x)
        else:
            envolver = lambda x: x

        PSecuenciaConAccion.__init__(self,
            lambda xs: envolver(' '.join([xs[0]] + xs[1])),
            PSustantivoPropioBasico(),
            PClausuraConTerminador(
                PSustantivoPropioBasico(),
                terminador=PComplemento(PSustantivoPropioBasico())
            )
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

class PCabezaDefinicionDeFuncion(PAlternativa):

    def __init__(self, **kwargs):
        cabezas = [
            "la posta para",
            "la posta pa",
            "la posta pa'",
            "la posta si queres",
        ]
        alts = [PPalabras(cabeza) for cabeza in cabezas]
        return PAlternativa.__init__(self, *alts, **kwargs)

class PVariable(PNominal):

    def __init__(self, **kwargs):
        PNominal.__init__(self,
            articulo_obligatorio=True,
            devolver_variable=True,
            **kwargs
        )

class PExpresion(PAlternativa):
    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            PVariable(),
            PPlata(),
            lambda: PInvocacionVerboInfinitivo(),
            lambda: PDefinicionDeFuncion(),
            **kwargs
        )

class PComa(PPuntuacion):
    def __init__(self, **kwargs):
        PPuntuacion.__init__(self, ',', **kwargs)

class PPuntoFinal(PPuntuacion):
    def __init__(self, **kwargs):
        PPuntuacion.__init__(self, '.', **kwargs)

class PSeparadorExpresiones(PAlternativa):

    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            PComa(),

            PSecuencia(
                POpcional(PPalabra('y')),
                PAlternativa(
                    PPalabra(u'después'),
                    PSecuencia(
                        PPalabras('a el final'),
                        POpcional(PPalabras('de todo')),
                    )
                )
            ),
            **kwargs
        )

class PCuerpoDeFuncion(PSecuenciaConAccion):
    """El cuerpo de una función consta de expresiones separadas por ",".
       y terminadas por un terminador dado."""
    def __init__(self, terminador_cuerpo_funcion=PPuntoFinal(), **kwargs):

        def accion(expresiones):
            return TBloque(expresiones)

        PSecuenciaConAccion.__init__(self, lambda xs: xs[1],
            POpcional(PPalabra('primero')),
            PClausuraConTerminadorConAccion(accion,
                PExpresion(),
                separador=PSeparadorExpresiones(),
                terminador=terminador_cuerpo_funcion,
            ),
            **kwargs
        )

class PInvocacionVerboInfinitivo(PSecuenciaConAccion):
    def __init__(self):

        def accion(lista):
            verbo, expresion, argumentos = lista
            if expresion != ():
                argumentos = [TParametro('*', expresion[0])] + argumentos
            return TInvocarVerbo(verbo, argumentos)

        PSecuenciaConAccion.__init__(self, accion,
            PVerboNuevoInfinitivo(),
            POpcional(PExpresion()),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: TParametro(*xs), PPreposicion(), PExpresion()),
                terminador=PLookahead(
                               PAlternativa(
                                   PPuntoFinal(),
                                   PApelativo(),
                                   PSeparadorExpresiones(),
                               )
                           )
            )
        )

class PDefinicionDeFuncionBasico(PSecuenciaConAccion):
    """Definiciones de funciones son de la forma:

            <cabeza-definicion-de-funcion> <verbo> [<nominal>] [<prep> <nominal>]* es <cuerpo>

    """
    def __init__(self, terminador_cuerpo_funcion=PPuntoFinal(), **kwargs):

        def accion(lista):
            def_, verbo, nominal, argumentos, cuerpo = lista
            if nominal != ():
                argumentos = [TParametro('*', nominal)] + argumentos
            return TDefinicionDeFuncion(verbo, argumentos, cuerpo)

        PSecuenciaConAccion.__init__(self, accion,
            PCabezaDefinicionDeFuncion(),
            PVerboNuevoInfinitivo(),
            POpcional(PNominal()),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: TParametro(*xs), PPreposicion(), PNominal()),
                terminador=PPalabra('es'),
            ),
            PCuerpoDeFuncion(terminador_cuerpo_funcion),
            **kwargs
        )

class PDefinicionDeFuncion(PAlternativa):

    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            #PDefinicionDeFuncionBasico(),
            #PSecuenciaConAccion(lambda xs: xs[3],
            #    POpcional(
            #        PSecuencia(
            #            PVocativo(),
            #            POpcional(PToken(tipo='puntuacion', valor=','))
            #        )
            #    ),
            #    PApelativo(),
            #    PToken(tipo='puntuacion', valor=','),
            #    PDefinicionDeFuncionBasico(),
            #),
            PSecuenciaConAccion(lambda xs: xs[2],
                PVocativo(),
                PComa(),
                PDefinicionDeFuncionBasico(
                    terminador_cuerpo_funcion=PApelativo(),
                ),
            ),
            descripcion=u'declaración de una función usando "la posta".'
        )

