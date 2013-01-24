# coding:utf-8

from comunes.utiles import QuilomboException, identar, frac
from idioma.ortografia import normalizar
from idioma.gramatica import (
    ARTICULOS,
    PREPOSICIONES,
    VOCATIVOS,
    APELATIVOS,
    NUMEROS_CARDINALES,
    PALABRAS_CLAVE,
)
from lenguaje.terminos import (
    TNumero,
    TVariable,
    TParametro,
    TDefinicionDeFuncion,
    TInvocarVerbo,
    TBegin,
)

LETRAS_MINUSCULAS = u'abcdefghijklmnopqrstuvwxyzáéíóúüñ'
LETRAS_MAYUSCULAS = u'ABCDEFGHIJKLMNOPQRSTUVWXYZÁÉÍÓÚÜñ'
LETRAS = LETRAS_MINUSCULAS + LETRAS_MAYUSCULAS + "'"

class Posicion(object): 
    u"Representa una posición dentro de un archivo."

    def __init__(self, nombre_archivo, texto, linea=1, columna=1):
        self._nombre_archivo = nombre_archivo
        self._texto = texto
        self._linea = linea
        self._columna = columna

    def __unicode__(self):
        return u'[ %s ] línea: %u columna: %u' % (
                    self._nombre_archivo,
                    self._linea,
                    self._columna
        )

    def avanzar(self, texto):
        u"""Devuelve la posición que resulta partiendo de la posición
            actual después de leer el texto dado."""
        linea = self._linea
        columna = self._columna
        for c in texto:
            if c == '\n':
                linea += 1
                columna = 1
            else:
                columna += 1
        return Posicion(self._nombre_archivo, self._texto, linea, columna)

class Token(object): 
    "Representa un terminal."

    def __init__(self, tipo, valor, pos_inicial, pos_final):
        self.tipo = tipo
        self.valor = valor
        self._pos_inicial = pos_inicial
        self._pos_final = pos_final

    def __unicode__(self):
        return u'Token(%s, %s, %s, %s)' % (
                    self.tipo,
                    self.valor,
                    self._pos_inicial,
                    self._pos_final
        )

def stream_de_tokens(texto, nombre_archivo='...'):
    "Devuelve un generador que itera sobre un stream de tokens."

    i = 0
    pos = Posicion(nombre_archivo, texto)
    while i < len(texto):

        while i < len(texto) and texto[i] in ' \t\r\n':
            # Se come los espacios
            pos = pos.avanzar(texto[i])
            i += 1

        if i >= len(texto):
            yield Token('EOF', 'EOF', pos, pos)
            return

        if texto[i] in LETRAS:
            j = i
            pos_final = pos
            while j < len(texto) and texto[j] in LETRAS:
                pos_final = pos_final.avanzar(texto[j])
                j += 1

            # Contracciones se manejan a nivel léxico
            if texto[i:j] == 'al':
                yield Token('palabra', 'a', pos, pos_final)
                yield Token('palabra', 'el', pos, pos_final)

            elif texto[i:j] == 'del':
                yield Token('palabra', 'de', pos, pos_final)
                yield Token('palabra', 'el', pos, pos_final)

            else:
                yield Token('palabra', texto[i:j], pos, pos_final)

            i = j
            pos = pos_final
        elif texto[i] in [',', '.', '<', '>', '$']:
            j = i + 1
            pos_final = pos.avanzar(texto[i:j])
            yield Token('puntuacion', texto[i:j], pos, pos_final)
            i = j
            pos = pos_final
        else:
            raise QuilomboException(u'Análisis léxico: no se entiende una goma.',
                                    cerca_de=pos)

###

class IteradorTokens(object):
    """Representa un iterador sobre una lista de tokens."""

    def __init__(self, tokens, pos=0):
        self._tokens = tokens
        self._pos = pos

    def __unicode__(self):
        return 'IteradorTokens(' + \
               '[\n' + '\n'.join(['\t' + unicode(tok) for tok in self._tokens]) + '\n]' + \
               ',\n' + \
               '\t%u\n' % (self._pos,) + \
               ')'

    def avanzar(self, n=1):
        return IteradorTokens(self._tokens, self._pos + n)

    def hay_token(self):
        return self._pos < len(self._tokens)

    def token_actual(self):
        assert self.hay_token()
        return self._tokens[self._pos]

def tokenizar(texto, nombre_archivo='...'):
    "Devuelve el iterador de tokens que resulta del texto dado."
    return IteradorTokens(list(stream_de_tokens(texto, nombre_archivo)))

###

class Parser(object):
    """Representa un analizador sintáctico. Toda subclase implementa un
       método self.match(it) que recibe un iterador de tokens y devuelve
       un generador de matches."""

    def __init__(self, descripcion=None):
        self._descripcion = descripcion

    def descripcion_completa(self):
        if self._descripcion:
            return self._descripcion
        else:
            return self.descripcion()

    def descripcion(self):
        return repr(self)

    def mensaje_de_error(self, it):
        msj = 'Tu programa es fruta.'
        d = self.descripcion_completa()
        if d is not None:
            msj += '\nEsperaba: ' + d
        return msj

def coincide(referencia, x):
    if referencia is None:
        return True
    else:
        return referencia == x

def texto_coincide(referencia, x):
    if referencia is None:
        return True
    else:
        return normalizar(referencia) == normalizar(x)

class PToken(Parser):
    """Analizador que exige coincidencia literal con un terminal,
       ya sea por su tipo, su valor o ambos."""

    def __init__(self, predicado=None, tipo=None, valor=None, resultado=None, func_resultado=None, **kwargs):
        assert resultado is None or func_resultado is None

        Parser.__init__(self, **kwargs)

        self._tipo = tipo
        self._valor = valor
        self._predicado = predicado
        self._resultado = resultado
        self._func_resultado = func_resultado

    def match(self, it):
        ok = True
        tok = it.token_actual()

        if self._predicado is not None:
            ok = ok and self._predicado(tok)

        ok = ok and coincide(self._tipo, tok.tipo)
        ok = ok and texto_coincide(self._valor, tok.valor)

        if self._func_resultado is not None:
            resultado = self._func_resultado(tok)
        elif self._resultado is not None:
            resultado = self._resultado
        else:
            resultado = tok

        if ok:
            yield resultado, it.avanzar()

    def descripcion(self):
        if self._valor is not None:
            return 'el símbolo "' + self._valor + '"'
        elif self._tipo is not None:
            return 'un símbolo tipo <' + self._tipo + '>'
        else:
            return 'el símbolo esperado'

class PPalabra(PToken):
    def __init__(self, pal, **kwargs):
        PToken.__init__(self, tipo='palabra', valor=pal, **kwargs)

class PValor(PToken):

    def __init__(self, valor, parser):
        self._valor = valor
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield self._valor, it1

class PPuntuacion(PToken):
    def __init__(self, punt, **kwargs):
        PToken.__init__(self, tipo='puntuacion', valor=punt, **kwargs)

class PLookahead(object):
    u"Se fija que la entrada coincida con lo esperado sin consumirla."

    def __init__(self, parser):
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield res1, it

class PComplemento(object):
    u"Tiene éxito sii el parser dado no tiene éxito. No consume la entrada."

    def __init__(self, parser):
        self._parser = parser

    def match(self, it):
        exito = False
        for res1, it1 in self._parser.match(it):
            exito = True
            break
        if not exito:
            yield None, it

class PAlternativa(Parser):
    u"Introduce una alternativa no determinística entre varios parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = parsers

    def match(self, it):
        for p in self._parsers:
            if callable(p): p = p()
            for r in p.match(it):
                yield r

    def descripcion(self):
        ds = [d for p in self._parsers for d in [p.descripcion()] if d is not None]
        return 'alguna de estas cosas:\n' + identar('\n'.join(ds))

class PSecuencia(Parser):
    u"Yuxtaposición de parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = parsers

    def match(self, it):
        if self._parsers == ():
            yield [], it
        else:
            p = self._parsers[0]
            ps = PSecuencia(*self._parsers[1:])
            for res1, it1 in p.match(it):
                for res2, it2 in ps.match(it1):
                    yield [res1] + res2, it2

class PSecuenciaConAccion(PSecuencia):

    def __init__(self, accion, *parsers, **kwargs):
        PSecuencia.__init__(self, *parsers, **kwargs)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PSecuencia.match(self, it):
            yield self._accion(res1), it1

class PPalabras(PSecuencia):
    def __init__(self, palabras, **kwargs):
        PSecuencia.__init__(self, *[
            PPalabra(pal) for pal in palabras.split(' ')
        ])

class PClausuraConTerminador(Parser):

    def __init__(self, parser, terminador, separador=None, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser
        self._terminador = terminador
        self._separador = separador

    def match(self, it):
        if self._separador is None:
            for r in self._match_sin_separador(it): yield r
        else:

            for res1, it1 in self._terminador.match(it):
                yield [], it1
                return

            for r in self._match_con_separador(it): yield r

    def _match_sin_separador(self, it):
        for res1, it1 in self._terminador.match(it):
            yield [], it1
            return
        for res1, it1 in self._parser.match(it):
            for res2, it2 in self._match_sin_separador(it1):
                yield [res1] + res2, it2

    def _match_con_separador(self, it):

        for res1, it1 in self._parser.match(it):
            termina = False
            for res2, it2 in self._terminador.match(it1):
                termina = True 
                yield [res1], it2

            if termina: continue

            for res2, it2 in self._separador.match(it1):
                for res3, it3 in self._match_con_separador(it2):
                    yield [res1] + res3, it3

class PClausuraConTerminadorConAccion(PClausuraConTerminador):

    def __init__(self, accion, *args, **kwargs):
        PClausuraConTerminador.__init__(self, *args, **kwargs)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PClausuraConTerminador.match(self, it):
            yield self._accion(res1), it1

class POpcional(Parser):

    def __init__(self, parser, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield (res1,), it1
        yield (), it

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
            return TBegin(expresiones)

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

