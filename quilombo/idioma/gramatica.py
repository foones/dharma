# coding:utf-8

class Lexema(object):
    """Cada instancia de lexema representa una palabra, que puede
       llegar a tener varias formas. Por ejemplo, 'perro' podría
       ser un lexema."""
    pass

class Sustantivo(Lexema):
    "Clase de los lexemas nominales."

    def __init__(self, raiz):
        self._raiz = raiz

    def formas(self):
        pass

###

class Categoria(object):
    u"""Cada instancia de Categoria representa una categoría gramatical.
        Por ejemplo: 'número singular', 'tiempo pasado', etc."""
    pass

###

class Flexion(object):
    u"""Cada instancia de Flexion representa la flexión de un
        lexema expresando alguna categoría gramatical."""

    def __init__(self, lexema, categoria):
        self._lexema = lexema
        self._categoria = categoria
        self._texto = texto 

