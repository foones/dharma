#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from lenguaje.lexer import tokenizar
from lenguaje.quilombo_parser import PPrograma, PToken, PSecuencia, PPalabra, PAlternativa, PComplemento, PClausuraConTerminador, POpcional
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

#       analizador = PSecuencia(
#           PPalabra('test'),
#           PComplemento(
#               PAlternativa(
#                   PSecuencia(
#                       PPalabra('buen'),
#                       PPalabra('dia'),
#                       PPalabra('putos'),
#                   ),
#                   PSecuencia(
#                       PPalabra('hola'),
#                       PPalabra('mundo')
#                   )
#               )
#           ),
#       )

        analizador = PClausuraConTerminador(
            PPalabra('a'),
            terminador=PPalabra('b'),
            separador=POpcional(PPalabra('c')),
        )

        nmatches = 0
        matches = analizador.match(iterador_tokens)
        MS = analizador.max_match(iterador_tokens)
        for it, prs in MS:
            print '--max matches--'
            print unicode(it) 
            print prs
        #for match in matches:
        #    nmatches += 1
        #    programa, iterador_tokens2 = match
        #    print('----arbol sintactico----')
        #    print(unicode(programa))

        #if nmatches == 0:
        #    raise QuilomboException(analizador.mensaje_de_error(iterador_tokens))

    except QuilomboException as e:
        print(unicode(e))

if __name__ == '__main__':
    main()

