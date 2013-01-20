#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo
from idioma.gramatica import Sustantivo
from lenguaje.parser import tokenizar

DICCIONARIO_INICIAL = [
    Sustantivo('mango'),
]

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Uso: %s archivo.qu\n' % (sys.argv[0],))
        sys.exit(1)

    nombre_archivo = sys.argv[1]

    contenido = leer_archivo(nombre_archivo)
    for tok in tokenizar(contenido, nombre_archivo=nombre_archivo):
        print unicode(tok)

if __name__ == '__main__':
    main()

