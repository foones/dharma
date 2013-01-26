# coding:utf-8

u"""Analizador léxico para el lenguaje Quilombo. La función principal
    es tokenizar(texto) que devuelve un iterador de tokens (instancia de
    IteradorTokens."""

from comunes.utiles import QuilomboException

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
        return u'Token(%s, %s, %s --- %s)' % (
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
              '[\n' + \
               '\n'.join([
                   ('    >>> ' if i == self._pos else '        ') + unicode(tok)
                   for tok, i in zip(self._tokens, range(len(self._tokens)))
               ]) + \
               '\n]' + \
              ',\n' + \
              '\t%u\n' % (self._pos,) + \
              ')'

    def contexto(self):
        ztoks = zip(self._tokens, range(len(self._tokens)))[max(0, self._pos - 10):self._pos + 10]
        return ' '.join([
                   ('\n\t' if i == self._pos else '') + tok.valor + ('\n' if i == self._pos else '')
                   for tok, i in ztoks
               ])

    def avanzar(self, n=1):
        return IteradorTokens(self._tokens, self._pos + n)

    def hay_token(self):
        return self._pos < len(self._tokens)

    def token_actual(self):
        assert self.hay_token()
        return self._tokens[self._pos]

    def posicion(self):
        return self._pos

    def valor_hash(self):
        return id(self._tokens), self._pos

    def __cmp__(self, otro):
        assert False

def tokenizar(texto, nombre_archivo='...'):
    "Devuelve el iterador de tokens que resulta del texto dado."
    return IteradorTokens(list(stream_de_tokens(texto, nombre_archivo)))

