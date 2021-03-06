# coding:utf-8
import fractions

ENCODING = 'utf-8'

class QuilomboException(Exception):

    def __init__(self, mensaje, cerca_de=None):
        self._mensaje = mensaje 
        self._pos = cerca_de 

    def __unicode__(self):
        msj = self._mensaje
        if self._pos is not None:
            msj += u'\nEn %s' % (self._pos,)

        return '\n'.join(['quilombo: ' + linea for linea in msj.split('\n')])

def leer_archivo(nombre_archivo):
    "Lee el contenido de un archivo en el encoding apropiado."

    try:
        f = open(nombre_archivo, 'r')
        texto = f.read()
        f.close()
    except IOError:
        raise QuilomboException(
            u'No se puede leer el archivo [ %s ].\n' % (nombre_archivo,) +
            u'Fijate si existe o me mandaste fruta.' 
        )
    return texto.decode(ENCODING)

def identar(texto, sangria='    '):
    return '\n'.join([sangria + linea for linea in texto.split('\n')])

def frac(n, d):
    return fractions.Fraction(n, d)
