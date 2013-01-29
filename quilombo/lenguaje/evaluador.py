# coding:utf-8

from comunes.utiles import QuilomboException, identar
from lenguaje.terminos import Termino, TNada

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

    def __unicode__(self):
        res = []
        for costilla in self._entorno:
            res_costilla = []
            for k, v in sorted(costilla.items()):
                res_costilla.append(u'%s -> %s' % (k, v))
            res.append(u'{%s}' % (', '.join(res_costilla),))
        return u'Entorno([\n%s\n])' % (identar(',\n'.join(res),))

class Estado(object):

    def __init__(self):
        self.entorno = Entorno()
        self.pila = []

    def push(self, x):
        self.pila.append(x)

    def pop(self):
        return self.pila.pop(-1)

    def __unicode__(self):
        return u'Estado(\n%s,\n%s\n)' % (
            identar(unicode(self.entorno)),
            identar('Pila([' + ', '.join(map(unicode, self.pila)) + '])')
        )

def estado_inicial():
    return Estado()

def evaluar(termino, estado):
    if not isinstance(termino, Termino):
        raise QuilomboException(u'%s no es un término' % (termino,))
    for r in termino.evaluar_en(estado):
        yield r

