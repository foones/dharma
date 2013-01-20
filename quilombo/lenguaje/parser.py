# coding:utf-8

from comunes.utiles import QuilomboException
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
    TEntero,
    TVariable,
    TArgumento,
    TDefinicionDeFuncion,
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
            yield Token('palabra', texto[i:j], pos, pos_final)
            i = j
            pos = pos_final
        elif texto[i] in [',', '.']:
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
    pass

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

    def __init__(self, predicado=None, tipo=None, valor=None, resultado=None, func_resultado=None):
        assert resultado is None or func_resultado is None

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

class PAlternativa(Parser):
    u"Introduce una alternativa no determinística entre varios parsers."

    def __init__(self, *parsers):
        self._parsers = parsers

    def match(self, it):
        for p in self._parsers:
            for r in p.match(it):
                yield r

class PSecuencia(Parser):
    u"Yuxtaposición de parsers."

    def __init__(self, *parsers):
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

    def __init__(self, accion, *parsers):
        PSecuencia.__init__(self, *parsers)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PSecuencia.match(self, it):
            yield self._accion(res1), it1

class PClausuraConTerminador(Parser):

    def __init__(self, parser, terminador, separador=None):
        self._parser = parser
        self._terminador = terminador
        self._separador = separador

    def match(self, it):
        if self._separador is None:
            return self._match_sin_separador(it)
        else:
            return self._match_con_separador(it)

    def _match_sin_separador(self, it):
        for res1, it1 in self._terminador.match(it):
            yield [], it1
            return
        for res1, it1 in self._parser.match(it):
            for res2, it2 in self.match(it1):
                yield [res1] + res2, it2

    def _match_con_separador(self, it):

        for res1, it1 in self._terminador.match(it):
            yield [], it1
            return

        for res1, it1 in self._parser.match(it):
            termina = False
            for res2, it2 in self._terminador.match(it1):
                termina = True 
                yield [res1], it2

            if termina: continue

            for res2, it2 in self._separador.match(it1):
                for res3, it3 in self.match(it2):
                    yield [res1] + res3, it3

class PClausuraConTerminadorConAccion(PClausuraConTerminador):

    def __init__(self, accion, *args, **kwargs):
        PClausuraConTerminador.__init__(self, *args, **kwargs)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PClausuraConTerminador.match(self, it):
            yield self._accion(res1), it1

class POpcional(PToken):

    def __init__(self, parser):
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield (res1,), it1
        yield (), it

VERBOS_RESERVADOS = ['agarrar']

class PVerboNuevoInfinitivoBasico(PToken):
    "Parser para nuevos verbos en infinitivo definidos por el usuario."

    def __init__(self):

        desinencias = ['ar', 'er', 'ir']
        sufijos = ['lo', 'le']

        def es_verbo_infinitivo(tok):
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
                        func_resultado=sacar_sufijos
        )

class PVerboNuevoInfinitivo(PSecuenciaConAccion):
    """Parser para verbos en infinitivo definidos por el usuario,
       posiblemente decorados."""

    def __init__(self):
        def accion(lista):
            return lista[1]
        PSecuenciaConAccion.__init__(self, accion,
            POpcional(
                PSecuencia(
                    PToken(tipo='palabra', valor='agarrar'),
                    PToken(tipo='palabra', valor='y'),
                )
            ),
            PVerboNuevoInfinitivoBasico()
        )

class PEntero(PAlternativa):
    """Parser para números enteros."""

    def __init__(self):
        lista = []
        for nombre, numero in NUMEROS_CARDINALES.items():
            def func(numero):
                return lambda tok: TEntero(numero, tokens=[tok])

            lista.append(PToken(tipo='palabra', valor=nombre, func_resultado=func(numero)))

        PAlternativa.__init__(self, *lista)

class PAlternativaPalabras(PAlternativa):
    def __init__(self, palabras):
        PAlternativa.__init__(self, *[
            PToken(tipo='palabra', valor=pal, resultado=pal)
            for pal in palabras
        ])

class PVocativo(PAlternativaPalabras):
    def __init__(self):
        PAlternativaPalabras.__init__(self, VOCATIVOS)

class PApelativo(PAlternativaPalabras):
    def __init__(self):
        PAlternativaPalabras.__init__(self, APELATIVOS)

class PArticulo(PAlternativaPalabras):
    def __init__(self):
        PAlternativaPalabras.__init__(self, ARTICULOS)

class PPreposicion(PAlternativaPalabras):
    def __init__(self):
        PAlternativaPalabras.__init__(self, PREPOSICIONES)

class PSustantivo(PToken):

    def __init__(self):
        PToken.__init__(self,
            tipo='palabra',
            #predicado=lambda tok: tok.valor[:1].upper() == tok.valor[:1],
            predicado=lambda tok: tok.valor not in PALABRAS_CLAVE,
            func_resultado=lambda tok: tok.valor
        )

class PNominal(PSecuenciaConAccion):

    def __init__(self, articulo_obligatorio=False, devolver_variable=False):

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
        PSecuenciaConAccion.__init__(self, accion, 
            art,
            PSustantivo(),
        )

class PCabezaDefinicionDeFuncion(PAlternativa):

    def __init__(self):
        cabezas = ["la posta para",
                   "la posta pa",
                   "la posta pa'",
                   "la posta si queres",
                  ]
        alts = []
        for cabeza in cabezas:
            seqs = []
            for pal in cabeza.split(' '):
                seqs.append(PToken(tipo='palabra', valor=pal, resultado=None))
            alts.append(PSecuenciaConAccion(lambda x: None, *seqs))

        return PAlternativa.__init__(self, *alts)

class PVariable(PNominal):
    def __init__(self):
        PNominal.__init__(self,
            articulo_obligatorio=True,
            devolver_variable=True
        )

class PExpresion(PAlternativa):
    def __init__(self):
        PAlternativa.__init__(self,
            PVariable(),
            PEntero(),
        )

class PComa(PToken):
    def __init__(self):
        PToken.__init__(self, tipo='puntuacion', valor=',')

class PPuntoFinal(PToken):
    def __init__(self):
        PToken.__init__(self, tipo='puntuacion', valor='.')

class PSeparadorExpresiones(PAlternativa):
    def __init__(self):
        PAlternativa.__init__(self,
            PComa(),
            PSecuencia(
                POpcional(PToken(tipo='palabra', valor='y')),
                PToken(tipo='palabra', valor=u'después'),
            )
        )

class PCuerpoDeFuncion(PClausuraConTerminadorConAccion):
    """El cuerpo de una función consta de expresiones separadas por ",".
       y terminadas por "."."""
    def __init__(self, terminador_cuerpo_funcion=PPuntoFinal()):

        def accion(expresiones):
            return TBegin(expresiones)

        PClausuraConTerminadorConAccion.__init__(self, accion,
            PExpresion(),
            separador=PSeparadorExpresiones(),
            terminador=terminador_cuerpo_funcion,
        )

class PDefinicionDeFuncionBasico(PSecuenciaConAccion):
    """Definiciones de funciones son de la forma:

            <cabeza-definicion-de-funcion> <verbo> [<nominal>] [<prep> <nominal>]* es <cuerpo>

    """
    def __init__(self, terminador_cuerpo_funcion=PPuntoFinal()):

        def accion(lista):
            def_, verbo, nominal, argumentos, cuerpo = lista
            if nominal != ():
                verbo = verbo + ' ' + nominal[0]
            return TDefinicionDeFuncion(verbo, argumentos, cuerpo)

        PSecuenciaConAccion.__init__(self, accion,
            PCabezaDefinicionDeFuncion(),
            PVerboNuevoInfinitivo(),
            POpcional(PNominal()),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: TArgumento(*xs), PPreposicion(), PNominal()),
                terminador=PToken(tipo='palabra', valor='es'),
            ),
            PCuerpoDeFuncion(terminador_cuerpo_funcion),
        )

class PDefinicionDeFuncion(PAlternativa):

    def __init__(self):
        PAlternativa.__init__(self,
            PDefinicionDeFuncionBasico(),
            PSecuenciaConAccion(lambda xs: xs[3],
                POpcional(
                    PSecuencia(
                        PVocativo(),
                        POpcional(PToken(tipo='puntuacion', valor=','))
                    )
                ),
                PApelativo(),
                PToken(tipo='puntuacion', valor=','),
                PDefinicionDeFuncionBasico(),
            ),
            PSecuenciaConAccion(lambda xs: xs[2],
                PVocativo(),
                PToken(tipo='puntuacion', valor=','),
                PDefinicionDeFuncionBasico(
                    terminador_cuerpo_funcion=
                        PSecuencia(
                            PApelativo(),
                            PPuntoFinal(),
                        )
                ),
            ),
        )

