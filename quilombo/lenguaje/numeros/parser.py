# coding:utf-8

from comunes.utiles import frac

from idioma.ortografia import normalizar
from idioma.gramatica import NUMEROS_CARDINALES

from lenguaje.parser import (
    Parser, PSecuencia, PSecuenciaConAccion, PAlternativa,
    PClausuraConTerminadorConAccion, PComplemento, PLookahead,
    POpcional, PValor, PPalabra,
    PPalabras,
)
from lenguaje.numeros.terminos import TNumero

class PEnteroEnDiccionario(Parser):
    "Parser para palabras que representan números enteros dadas por un diccionario."

    def __init__(self, diccionario, **kwargs):
        self._diccionario = diccionario
        Parser.__init__(self, **kwargs)

    def match(self, it):
        tok = it.token_actual()
        valor = normalizar(tok.valor) 
        if valor in self._diccionario:
            num = self._diccionario[valor]
            if isinstance(num, tuple):
                num, pico = num
            else:
                pico = 0
            yield TNumero(num, tokens=[tok], pico=pico), it.avanzar()

def accion_sumar_par(lista):
    cabeza, resto = lista
    res = cabeza
    if resto != ():
        res += resto[0]
    return res

class PEnteroMenorQueCien(PAlternativa):
    """Parser para números enteros."""

    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            # 0..9
            PSecuenciaConAccion(accion_sumar_par,
                PEnteroEnDiccionario(NUMEROS_CARDINALES['unidades']),
                POpcional(PValor(TNumero(0, pico=1), PPalabras('y pico'))),
            ),
            # 10..19
            PEnteroEnDiccionario(NUMEROS_CARDINALES['diez-y']),
            PValor(TNumero(10, pico=10), PPalabras('diez y pico')),
            # 20..99 (formas contractas)
            PEnteroEnDiccionario(NUMEROS_CARDINALES['formas-contractas']),
            PEnteroEnDiccionario(NUMEROS_CARDINALES['formas-contractas-y-pico']),
            # 20..99 (formas largas)
            PSecuenciaConAccion(accion_sumar_par,
                PEnteroEnDiccionario(NUMEROS_CARDINALES['decenas']),
                POpcional(
                    PAlternativa(
                        PSecuenciaConAccion(lambda xs: xs[1],
                            PPalabra('y'),
                            PEnteroEnDiccionario(NUMEROS_CARDINALES['unidades'])
                        ),
                        PValor(TNumero(0, pico=10), PPalabras('y pico')),
                    )
                )
            )
        )

class PEnteroMenorQueMil(PAlternativa):

    def __init__(self, **kwargs):

        PAlternativa.__init__(self,
            # 0..99
            PEnteroMenorQueCien(),
            # 100..999
            PSecuenciaConAccion(accion_sumar_par,
                PEnteroEnDiccionario(NUMEROS_CARDINALES['centenas']),
                POpcional(
                    PAlternativa(
                        PEnteroMenorQueCien(),
                        PValor(TNumero(0, pico=100), PPalabras('y pico')),
                    )
                )
            )
        )

class PEnteroMenorQueUnMillon(PAlternativa):
    def __init__(self, **kwargs):

        def accion_sumar_mil(lista):
            pre, mil, post = lista

            res = TNumero(1000)

            if pre != ():
                res = pre[0] * res

            if post != ():
                res = post[0] + res

            return res

        PAlternativa.__init__(self,
            # 0..999
            PEnteroMenorQueMil(),
            # 1000..999 999
            PSecuenciaConAccion(accion_sumar_mil,
                POpcional(PEnteroMenorQueMil()),
                PPalabra('mil'),
                POpcional(
                    PAlternativa(
                        PEnteroMenorQueMil(),
                        PValor(TNumero(0, pico=1000), PPalabras('y pico')),
                    )
                )
            )
        )

class PParteDecimal(PSecuenciaConAccion):
    def __init__(self):
        def sumar_digitos(xs):
            longitud = 0
            suma = 0
            for x in xs:
                if x.inf() < 10:
                    longitud += 1
                    suma = suma * 10 + x.inf()
                elif x.inf() < 100:
                    longitud += 2
                    suma = suma * 100 + x.inf()
                else:
                    longitud += 3
                    suma = suma * 1000 + x.inf()
            return TNumero(suma / frac(10 ** longitud, 1))

        PSecuenciaConAccion.__init__(self, lambda xs: sumar_digitos([xs[1]] + xs[2]),
            PPalabra('coma'),
            PEnteroMenorQueMil(),
            PClausuraConTerminadorConAccion(lambda xs: xs,
                PEnteroMenorQueMil(),
                terminador=PComplemento(
                    PEnteroMenorQueMil(),
                )
            )
        )

class PNumeroEspecificado(PSecuenciaConAccion):
    "Analiza sintácticamente un entero seguido de un especificador."

    def __init__(self, parser_especificador_unidad, envolver, **kwargs):

        separadores = [
                sep[0]
                for sep in sorted(
                    NUMEROS_CARDINALES['separadores-millones'].items(),
                    key=lambda x: -x[1]
                )
        ]

        def accion_sumar_millones(lista):
            res = TNumero(0)
            for s in lista:
                base = NUMEROS_CARDINALES['separadores-millones'][s[1]]
                mult = TNumero(base)
                res = res + s[0] * mult
                if s[2] != ():
                    if s[2][0] == 'pico':
                        ag = TNumero(0, base)
                    elif s[2][0] == 'medio':
                        ag = TNumero(base / 2)
                    else:
                        ag = TNumero(0)
                    res += ag
            return res

        def accion_sumar_final(lista):
            millones = lista[0]
            miles, decimales, unidad_de_medida = lista[1]
            algo_mas = lista[2]
            numero = millones + miles + decimales
            if algo_mas == ('medio',):
                numero = numero + frac(1, 2)
            return envolver(numero, unidad_de_medida)

        def entuplar(xs):
            if xs[0] != ():
                num = xs[0][0]
            else:
                num = TNumero(0)
            if xs[1] != ():
                decimales = xs[1][0]
            else:
                decimales = TNumero(0)
            return num, decimales, xs[3]

        algun_separador = PAlternativa(*[
            PValor(sep,
                PAlternativa(
                    PPalabra(sep),
                    PPalabra(sep + 'es'),
                )
            )
            for sep in separadores
        ])

        terminador = PSecuenciaConAccion(entuplar,
            POpcional(PEnteroMenorQueUnMillon()),
            POpcional(PParteDecimal()),
            POpcional(PPalabra('de')),
            parser_especificador_unidad,
        )

        PSecuenciaConAccion.__init__(self, accion_sumar_final,
            PClausuraConTerminadorConAccion(accion_sumar_millones,
                PSecuencia(
                    PEnteroMenorQueUnMillon(),
                    algun_separador,
                    POpcional(
                        PAlternativa(
                            PValor('pico', PPalabras('y pico')),
                            PValor('medio', PPalabras('y medio')),
                            PValor('medio', PPalabras('y media')),
                        )
                    )
                ),
                terminador=PLookahead(terminador)
            ),
            terminador,
            POpcional(
                PAlternativa(
                    PValor('medio', PPalabras('y medio')),
                    PValor('medio', PPalabras('y media')),
                )
            )
        )

