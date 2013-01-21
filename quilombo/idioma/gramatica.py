# coding:utf-8

PREPOSICIONES = u'a ante bajo cabe con contra de desde en entre hacia hasta para por segun sin so sobre tras mediante durante'.split(' ')

ARTICULOS = u'un una unos unas el la los las lo este esta esto estos estas'.split(' ')

VOCATIVOS = u'escuchame cuchame escucheme cucheme che eh'.split(' ')

APELATIVOS = u'boludo flaco pibe chabon man amigo guacho guachin hermano papa papi mama mami master maestro jefe maquina loco vieja viejo'.split(' ')

CONJUNCIONES = u'y o'.split(' ')

# Nota: representarlos sin tildes.

NUMEROS_CARDINALES = {
    'unidad-monetaria': {
        'guita': 0.01,
        'guitas': 0.01,
        'chirola': 0.01,
        'chirolas': 0.01,
        'peso': 1,
        'pesos': 1,
        'mango': 1,
        'mangos': 1,
        'morlaco': 1,
        'morlacos': 1,
        'gamba': 100,
        'gambas': 100,
        'luca': 1000,
        'lucas': 1000,
        'palo': 10 ** 6,
        'palos': 10 ** 6,
    },
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
    'veinte-y': {
        'veinte': 20,
        'veintiuno': 21,
        'veintidos': 22,
        'veintitres': 23,
        'veinticuatro': 24,
        'veinticinco': 25,
        'veintiseis': 26,
        'veintisiete': 27,
        'veintiocho': 28,
        'veintinueve': 29,
    },
    'decenas': {
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
    'millones': {
        'millon': 10 ** 6,
        'millones': 10 ** 6,
    },
    'billones': {
        'billon': 10 ** 12,
        'billones': 10 ** 12,
    },
    'trillones': {
        'trillon': 10 ** 18,
        'trillones': 10 ** 18,
    },
    'cuatrillones': {
        'cuatrillon': 10 ** 24,
        'cuatrillones': 10 ** 24,
    },
    'quintillones': {
        'quintillon': 10 ** 30,
        'quintillones': 10 ** 30,
    },
}

## Formas incorrectas (ej. cuarentitres)

NUMEROS_CARDINALES['formas-incorrectas'] = {}
for decena, valor_decena in [('treinti', 30),
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
        NUMEROS_CARDINALES['formas-incorrectas'][decena + unidad] = valor_decena + valor_unidad

##

PALABRAS_CLAVE = PREPOSICIONES + \
                 ARTICULOS + \
                 VOCATIVOS + \
                 APELATIVOS + \
                 CONJUNCIONES

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
