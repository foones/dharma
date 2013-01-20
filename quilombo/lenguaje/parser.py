# coding:utf-8

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
        return u'"%s" línea %u columna %u' % (
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

def tokenizar(texto, nombre_archivo='...'):
    "Genera un stream de tokens."

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

