# coding:utf-8

from comunes.utiles import QuilomboException
from idioma.ortografia import normalizar
from lenguaje.terminos import TEntero

LETRAS_MINUSCULAS = u'abcdefghijklmnopqrstuvwxyzáéíóúüñ'
LETRAS_MAYUSCULAS = u'ABCDEFGHIJKLMNOPQRSTUVWXYZÁÉÍÓÚÜñ'
LETRAS = LETRAS_MINUSCULAS + LETRAS_MAYUSCULAS

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

class PVerboNuevoInfinitivo(PToken):
    "Parser para nuevos verbos en infinitivo definidos por el usuario."

    def __init__(self):
        PToken.__init__(self,
                        tipo='palabra',
                        predicado=lambda tok:
                                    tok.valor.endswith('ar') or
                                    tok.valor.endswith('er') or
                                    tok.valor.endswith('ir'))

class PEntero(PAlternativa):
    """Parser para números enteros."""

    def __init__(self):
        basicos = {
            'cero': 0,
            'cerapio': 0,
            'uno': 1,
            'dos': 2,
            'duquesa': 2,
            'tres': 3,
            'tricota': 3,
            'cuatro': 4,
            'cinco': 5,
            'cocinero': 5,
            'seis': 6,
            'siete': 7,
            'ocho': 8,
            'nueve': 9,
            'diez': 10,
            'diego': 10,
            'once': 11,
            'doce': 12,
            'trece': 13,
            'catorce': 14,
            'quince': 15,
            u'dieciséis': 16,
            'diecisiete': 17,
            'dieciocho': 18,
            'diecinueve': 19,
            'veinte': 20,
        }

        lista = []
        for nombre, numero in basicos.items():
            def func(numero):
                return lambda tok: TEntero(numero, tokens=[tok])

            lista.append(PToken(tipo='palabra', valor=nombre, func_resultado=func(numero)))

        PAlternativa.__init__(self, *lista)

