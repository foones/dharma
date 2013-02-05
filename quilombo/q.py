#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from lenguaje.lexer import tokenizar
from lenguaje.quilombo_parser import PPrograma
from lenguaje.evaluador import evaluar, estado_inicial
from lenguaje.tesoro import tesoro_empezar, tesoro_terminar

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Uso: %s archivo.qu\n' % (sys.argv[0],))
        sys.exit(1)

    nombre_archivo = sys.argv[1]

    try:
        contenido = leer_archivo(nombre_archivo)
        iterador_tokens = tokenizar(contenido, nombre_archivo=nombre_archivo)
        tesoro_empezar(iterador_tokens)

        #print(u'----tokenizacion----').encode('utf-8')
        #print(unicode(iterador_tokens)).encode('utf-8')

        analizador = PPrograma()

        nmatches = 0
        matches = analizador.match(iterador_tokens)
        for match in matches:
            nmatches += 1
            programa, iterador_tokens2 = match
            print(u'----arbol sintactico----').encode('utf-8')
            print(unicode(programa)).encode('utf-8')
            print(u'----resultado de evaluar----').encode('utf-8')
            estado = estado_inicial()
            for resultado in evaluar(programa, estado):
                print 'ESTADO', unicode(estado).encode('utf-8')
                print(unicode(resultado)).encode('utf-8')
            break

        if nmatches == 0:
            #for it, res in analizador.max_match(iterador_tokens):
            #    print it.posicion(), res
            raise QuilomboException(analizador.mensaje_de_error(iterador_tokens))

        tesoro_terminar()

    except QuilomboException as e:
        print(80 * u'-').encode('utf-8')
        print(unicode(e)).encode('utf-8')

if __name__ == '__main__':
    main()

