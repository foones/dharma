# coding:utf-8

from comunes.utiles import QuilomboException
from lenguaje.terminos import TNada

class Entorno(object):
    "Un entorno es una pila de 'costillas' que asocian nombres a valores."

    def __init__(self):
        self._entorno = [{}]

    def push(self):
        self._entorno.append({})

    def pop(self):
        self._entorno.pop(-1)

    def declarar(self, nombre, valor=None):
        if nombre in self._entorno[-1]:
            raise QuilomboException('Epa: "%s" ya estaba declarada.' % (nombre,))
        self._entorno[-1][nombre] = valor

    def asignar(self, nombre, valor):
        for costilla in reversed(self._entorno):
            if nombre in costilla:
                costilla[nombre] = valor
                return valor
        raise QuilomboException('Epa: "%s" no estaba ligada.' % (nombre,))

    def valor(self, nombre):
        for costilla in reversed(self._entorno):
            if nombre in costilla:
                return costilla[nombre]
        raise QuilomboException('Epa: "%s" no estaba ligada.' % (nombre,))

class Estado(object):

    def __init__(self):
        self.entorno = Entorno()
        self.pila = []

    def push(self, x):
        self.pila.append(x)

    def pop(self):
        return self.pila.pop(-1)

def estado_inicial():
    return Estado()

def evaluar(termino, estado):
    if termino.es_constante():
        yield termino
    elif termino.es_variable():
        yield estado.entorno.valor(termino.nombre_variable())
    elif termino.es_bloque():
        for res in evaluar_bloque(termino.subterminos(), estado):
            yield res
    elif termino.es_definicion_de_funcion():
        print(u'TODO defino %s' % (termino,)).encode('utf-8')
        yield TNada()
    elif termino.es_invocacion_verbo():
        print(u'TODO invoco a %s' % (termino,)).encode('utf-8')
        yield TNada()
    else:
        assert False

def evaluar_bloque(terminos, estado, i=0):
    if i == len(terminos):
        yield TNada()
        return

    ti = terminos[i]
    for ri in evaluar(ti, estado):
        if not ri.es_nada():
            estado.pila.append(ri)
        if i + 1 < len(terminos):
            for rs in evaluar_bloque(terminos, estado, i + 1):
                yield rs
        else:
            yield ri

