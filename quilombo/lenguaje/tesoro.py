# coding:utf-8
from comunes.utiles import identar
from lenguaje.gramatica import (
    DATOS_ARTICULOS,
    NUMERO_SINGULAR,
    NUMERO_PLURAL,
    GENERO_MASCULINO,
    GENERO_FEMENINO,
)
from lenguaje.ortografia import (
    normalizar,
    normalizar_sustantivo_comun,
    singularizar_sustantivo_comun,
    pluralizar_sustantivo_comun,
)

class Tesoro(object):
    u"Guarda información sobre las clases de palabras."

    def __init__(self):
        self._sustantivos = {}

    def __unicode__(self):
        kvs = []
        for k, v in self._sustantivos.items():
            kvs.append(u'%s -> %s' % (k, v))
        return 'Tesoro(sustantivos = {\n' + identar(',\n'.join(kvs)) + '\n})'

    def declarar_sustantivo_comun(self, palabra, clase):
        normalizada = normalizar_sustantivo_comun(normalizar(palabra))
        if normalizada not in self._sustantivos:
            self._sustantivos[normalizada] = (palabra, clase)

    def sustantivo_comun_singular(self, palabra_normalizada):
        if palabra_normalizada not in self._sustantivos:
            return palabra_normalizada
        original, clase = self._sustantivos[palabra_normalizada]
        if NUMERO_SINGULAR in clase:
            return original
        else:
            return singularizar_sustantivo_comun(original)

    def sustantivo_comun_plural(self, palabra_normalizada):
        if palabra_normalizada not in self._sustantivos:
            return palabra_normalizada
        original, clase = self._sustantivos[palabra_normalizada]
        if NUMERO_PLURAL in clase:
            return original
        else:
            return pluralizar_sustantivo_comun(original)

    def sustantivo_comun_es_masculino(self, palabra_normalizada):
        if palabra_normalizada not in self._sustantivos:
            return True
        else:
            original, clase = self._sustantivos[palabra_normalizada]
            return GENERO_MASCULINO in clase

    def sustantivo_comun_singular_con_articulo_determinado(self, palabra_normalizada):
        if self.sustantivo_comun_es_masculino(palabra_normalizada):
            art = 'el'
        else:
            art = 'la'
        return art + ' ' + self.sustantivo_comun_singular(palabra_normalizada)

    def sustantivo_comun_singular_con_articulo_indeterminado(self, palabra_normalizada):
        if self.sustantivo_comun_es_masculino(palabra_normalizada):
            art = 'un'
        else:
            art = 'una'
        return art + ' ' + self.sustantivo_comun_singular(palabra_normalizada)

def armar_tesoro(lista_tokens):
    tesoro = Tesoro()
    n = len(lista_tokens)
    for i in range(n):
        if lista_tokens[i].valor in DATOS_ARTICULOS and i + 1 < n:
            tesoro.declarar_sustantivo_comun(lista_tokens[i + 1].valor, DATOS_ARTICULOS[lista_tokens[i].valor])
    return tesoro

#

PILA_TESOROS = []

def tesoro_empezar(iterador_tokens):
    PILA_TESOROS.append(armar_tesoro(iterador_tokens.lista_de_tokens()))

def tesoro_terminar():
    PILA_TESOROS.pop(-1)

def tesoro_actual():
    assert PILA_TESOROS != []
    return PILA_TESOROS[-1]

