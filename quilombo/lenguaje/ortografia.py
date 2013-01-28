# coding:utf-8

def normalizar(texto):
    reemplazo = {
        u'á': 'a',
        u'é': 'e',
        u'í': 'i',
        u'ó': 'o',
        u'ú': 'u',
        u'ü': 'u',
        u'ñ': '`n',
        u'Á': 'A',
        u'É': 'E',
        u'Í': 'I',
        u'Ó': 'O',
        u'Ú': 'U',
        u'Ü': 'U',
        u'Ñ': '`N',
        "\'": 's',   # Identificar ' con s
    }
    for original, cambiado in reemplazo.items():
        texto = texto.replace(original, cambiado)
    return texto

def normalizar_sustantivo_comun(texto):
    if texto.endswith('ces'):
        texto = texto[:-3] + 'z' 
    elif texto.endswith('es'):
        texto = texto[:-2]
    elif texto.endswith('s'):
        texto = texto[:-1]
    return texto

