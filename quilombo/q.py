#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from lenguaje.lexer import tokenizar
from lenguaje.quilombo_parser import PPrograma
from lenguaje.evaluador import evaluar, estado_inicial

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Uso: %s archivo.qu\n' % (sys.argv[0],))
        sys.exit(1)

    nombre_archivo = sys.argv[1]

    try:
        contenido = leer_archivo(nombre_archivo)
        iterador_tokens = tokenizar(contenido, nombre_archivo=nombre_archivo)
        print('----tokenizacion----')
        print(unicode(iterador_tokens))

        analizador = PPrograma()

        nmatches = 0
        matches = analizador.match(iterador_tokens)
        for match in matches:
            nmatches += 1
            programa, iterador_tokens2 = match
            print('----arbol sintactico----')
            print(unicode(programa))
            print('----resultado de evaluar----')
            for resultado in evaluar(programa, estado_inicial()):
                print(unicode(resultado))

        if nmatches == 0:
            raise QuilomboException(analizador.mensaje_de_error(iterador_tokens))

    except QuilomboException as e:
        print(unicode(e))

if __name__ == '__main__':
    main()

