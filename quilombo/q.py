#!/usr/bin/python
# coding:utf-8
import sys

from comunes.utiles import leer_archivo, QuilomboException
from lenguaje.parser import tokenizar, PDefinicionDeFuncion, PNominal, PPreposicion, PSecuenciaConAccion, PVerboNuevoInfinitivo, PNumero

def main():
    if len(sys.argv) != 2:
        sys.stderr.write('Uso: %s archivo.qu\n' % (sys.argv[0],))
        sys.exit(1)

    nombre_archivo = sys.argv[1]

    try:
        contenido = leer_archivo(nombre_archivo)
        iterador_tokens = tokenizar(contenido, nombre_archivo=nombre_archivo)

#        analizador = PSecuenciaConAccion(
#                        lambda xs: u'%s ---- %s' % tuple(xs),
#                        PVerboNuevoInfinitivo(),
#                        PNumero()
#                     )
        #analizador = PNumero()
        analizador = PDefinicionDeFuncion()
        #print unicode(iterador_tokens)

        nmatches = 0
        matches = analizador.match(iterador_tokens)
        for match in matches:
            nmatches += 1
            res, iterador_tokens2 = match
            print 'resultado=', unicode(res)

        if nmatches == 0:
            raise QuilomboException(analizador.mensaje_de_error(iterador_tokens))

    except QuilomboException as e:
        print(unicode(e))

if __name__ == '__main__':
    main()

