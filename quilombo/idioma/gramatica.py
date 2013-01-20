# coding:utf-8

PREPOSICIONES = u'a ante bajo cabe con contra de desde en entre hacia hasta para por según sin so sobre tras mediante durante'.split(' ')

ARTICULOS = u'un una unos unas el la los las lo este esta esto estos estas'.split(' ')

VOCATIVOS = u'escuchame cuchame escucheme cucheme che eh'.split(' ')

APELATIVOS = u'boludo flaco pibe amigo guacho guachín hermano papá master maestro jefe máquina loco'.split(' ')

NUMEROS_CARDINALES = {
    'cero': 0,
    'cerapio': 0,
    'uno': 1,
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
    'diez': 10,
    'diego': 10,
    'once': 11,
    'doce': 12,
    'trece': 13,
    'catorce': 14,
    'quince': 15,
    u'dieciséis': 16,
    'diecisiete': 17,
    'dieciocho': 18,
    'diecinueve': 19,
    'veinte': 20,
}

PALABRAS_CLAVE = PREPOSICIONES + \
                 ARTICULOS + \
                 VOCATIVOS + \
                 APELATIVOS + \
                 NUMEROS_CARDINALES.keys()

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
