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

def singularizar_sustantivo_comun(palabra):
    if palabra.endswith('ces'):
        palabra = palabra[:-3] + 'z' 
    elif palabra.endswith('es'):
        palabra = palabra[:-2]
    elif palabra.endswith('s'):
        palabra = palabra[:-1]
    return palabra

def normalizar_sustantivo_comun(texto):
    return singularizar_sustantivo_comun(normalizar(texto))

def pluralizar_sustantivo_comun(palabra):
    vocales = ['a', 'e', 'i', 'o', 'u', u'á', u'é', u'ó']
    cerradas = [u'í', u'ú']
    if any([palabra.endswith(x) for x in vocales]):
        return palabra + 's'
    elif any([palabra.endswith(x) for x in cerradas]):
        return palabra + 'es'
    elif palabra.endswith('z'):
        return palabra[-1] + 'ces'
    else:
        return palabra + 'es'

