#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from idioma.gramatica import Sustantivo
from lenguaje.parser import tokenizar, IteradorTokens, TokenParser

DICCIONARIO_INICIAL = [
    Sustantivo('mango'),
]

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Uso: %s archivo.qu\n' % (sys.argv[0],))
        sys.exit(1)

    nombre_archivo = sys.argv[1]

    try:
        contenido = leer_archivo(nombre_archivo)
        iterador_tokens = tokenizar(contenido, nombre_archivo=nombre_archivo)

        analizador = TokenParser(tipo='palabra')

        while True:
            res, iterador_tokens = analizador.match(iterador_tokens)
            print unicode(res)

    except QuilomboException as e:
        print(unicode(e))

if __name__ == '__main__':
    main()

