#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from idioma.gramatica import Sustantivo
from lenguaje.parser import tokenizar, PNumero

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

        analizador = PNumero()
        print unicode(iterador_tokens)

        nmatches = 0
        matches = analizador.match(iterador_tokens)
        for match in matches:
            nmatches += 1
            res, iterador_tokens2 = match
            print 'resultado=', unicode(res)

        if nmatches == 0:
            print 'cannot parse'
            

    except QuilomboException as e:
        print(unicode(e))

if __name__ == '__main__':
    main()

