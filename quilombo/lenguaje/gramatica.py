# coding:utf-8
import random
from comunes.utiles import frac

class Flexion(object):
    def __init__(self, nombre_flexion):
        self._nombre_flexion = nombre_flexion

    def __unicode__(self):
        return self._nombre_flexion

    def __repr__(self):
        return unicode(self)

class Numero(Flexion):
    pass

class Genero(Flexion):
    pass

NUMERO_SINGULAR = Numero('plural')
NUMERO_PLURAL = Numero('singular')
GENERO_MASCULINO = Genero('masculino')
GENERO_FEMENINO = Genero('femenino')

##

PREPOSICIONES = u'a ante bajo cabe con contra de desde en entre hacia hasta para por segun sin so sobre tras mediante durante'.split(' ')

DATOS_ARTICULOS = {
    'un': [NUMERO_SINGULAR, GENERO_MASCULINO],
    'una': [NUMERO_SINGULAR, GENERO_FEMENINO],
    'unos': [NUMERO_PLURAL, GENERO_MASCULINO],
    'unas': [NUMERO_PLURAL, GENERO_FEMENINO],
    'el': [NUMERO_SINGULAR, GENERO_MASCULINO],
    'la': [NUMERO_SINGULAR, GENERO_FEMENINO],
    'los': [NUMERO_PLURAL, GENERO_MASCULINO],
    'las': [NUMERO_PLURAL, GENERO_FEMENINO],
    'lo': [NUMERO_SINGULAR, GENERO_MASCULINO],
    'este': [NUMERO_SINGULAR, GENERO_MASCULINO],
    'esta': [NUMERO_SINGULAR, GENERO_FEMENINO],
    'esto': [NUMERO_SINGULAR, GENERO_MASCULINO],
    'estos': [NUMERO_PLURAL, GENERO_MASCULINO],
    'estas': [NUMERO_PLURAL, GENERO_FEMENINO],
}

ARTICULOS = DATOS_ARTICULOS.keys()

VOCATIVOS = u'escuchame cuchame escucheme cucheme che eh'.split(' ')

APELATIVOS = u'boludo flaco pibe chabon man amigo guacho guachin hermano papa papi mama mami master maestro jefe maquina loco vieja viejo fiera capo'.split(' ')

ADVERBIOS_DE_DUDA = u'quizá quizás'.split(' ')

CONJUNCIONES = u'y o'.split(' ')

# Nota: representarlos sin tildes.

def _llon(n):
    return 10 ** (n * 6)

NUMEROS_CARDINALES = {
    'unidades': {
        'cero': 0,
        'cerapio': 0,
        'un': 1,
        'uno': 1,
        'una': 1,
        'dos': 2,
        'duquesa': 2,
        'tres': 3,
        'tricota': 3,
        'cuatro': 4,
        'cinco': 5,
        'cocinero': 5,
        'seis': 6,
        'siete': 7,
        'ocho': 8,
        'nueve': 9,
    },
    'diez-y': {
        'diez': 10,
        'diego': 10,
        'once': 11,
        'doce': 12,
        'trece': 13,
        'catorce': 14,
        'quince': 15,
        'dieciseis': 16,
        'diecisiete': 17,
        'dieciocho': 18,
        'diecinueve': 19,
    },
    'decenas': {
        'veinte': 20,
        'treinta': 30,
        'cuarenta': 40,
        'cincuenta': 50,
        'sesenta': 60,
        'setenta': 70,
        'ochenta': 80,
        'noventa': 90,
    },
    'centenas': {
        'cien': 100,
        'ciento': 100,
        'doscientos': 200, 'doscientas': 200,
        'trescientos': 300, 'trescientas': 300,
        'cuatrocientos': 400, 'cuatrocientas': 400,
        'quinientos': 500, 'quinientas': 500,
        'seiscientos': 600, 'seiscientas': 600,
        'setecientos': 700, 'setecientas': 700,
        'ochocientos': 800, 'ochocientas': 800,
        'novecientos': 900, 'novecientas': 900,
    },
    'miles': {
        'mil': 1000,
    },
    'separadores-millones': {
        'millon': _llon(1),
        'billon': _llon(2),
        'trillon': _llon(3),
        'cuatrillon': _llon(4),
        'quintillon': _llon(5),
        'sextillon': _llon(6),
        'septillon': _llon(7),
        'octillon': _llon(8),
        'nonillon': _llon(9),
        'decillon': _llon(10),
    },
}

NUMEROS_CARDINALES['separadores-millones-plural'] = {}
for sep in NUMEROS_CARDINALES['separadores-millones']:
    NUMEROS_CARDINALES['separadores-millones-plural'][sep + 'es'] = NUMEROS_CARDINALES['separadores-millones'][sep]

## Formas contractas (ej. veinticinco, o incorrectas como cuarentitres)

NUMEROS_CARDINALES['formas-contractas'] = {}
NUMEROS_CARDINALES['formas-contractas-y-pico'] = {}
for decena, valor_decena in [('veinti', 20),
                             ('treinti', 30),
                             ('trenti', 30),
                             ('trentai', 30),
                             ('cuarenti', 40),
                             ('cincuenti', 50),
                             ('sesenti', 60),
                             ('setenti', 70),
                             ('ochenti', 80),
                             ('noventi', 90),
                            ]:
    for unidad, valor_unidad in NUMEROS_CARDINALES['unidades'].items():
        NUMEROS_CARDINALES['formas-contractas'][decena + unidad] = valor_decena + valor_unidad
    NUMEROS_CARDINALES['formas-contractas-y-pico'][decena + 'pico'] = (valor_decena, 10)

##

PALABRAS_CLAVE = PREPOSICIONES + \
                 ARTICULOS + \
                 VOCATIVOS + \
                 APELATIVOS + \
                 CONJUNCIONES

PALABRAS_CLAVE.append('pico')
PALABRAS_CLAVE.append('medio')
PALABRAS_CLAVE.append('media')
PALABRAS_CLAVE.append('coma')
PALABRAS_CLAVE.append('posta')
PALABRAS_CLAVE.append('dimension')
PALABRAS_CLAVE.extend(['expresado', 'expresados', 'expresada', 'expresadas'])
for clave, diccionario in NUMEROS_CARDINALES.items():
    for nombre, numero in diccionario.items():
        PALABRAS_CLAVE.append(nombre)

d = {}
for k in PALABRAS_CLAVE:
    d[k] = True
PALABRAS_CLAVE = d

#class Lexema(object):
#    """Cada instancia de lexema representa una palabra, que puede
#       llegar a tener varias formas. Por ejemplo, 'perro' podría
#       ser un lexema."""
#    pass
#
#class Sustantivo(Lexema):
#    "Clase de los lexemas nominales."
#
#    def __init__(self, raiz):
#        self._raiz = raiz
#
#    def formas(self):
#        pass
#
####
#
#class Categoria(object):
#    u"""Cada instancia de Categoria representa una categoría gramatical.
#        Por ejemplo: 'número singular', 'tiempo pasado', etc."""
#    pass
#
####
#
#class Flexion(object):
#    u"""Cada instancia de Flexion representa la flexión de un
#        lexema expresando alguna categoría gramatical."""
#
#    def __init__(self, lexema, categoria):
#        self._lexema = lexema
#        self._categoria = categoria
#        self._texto = texto 
#
