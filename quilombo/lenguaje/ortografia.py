# coding:utf-8
from lenguaje.gramatica import VERBOS_RESERVADOS

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

VERBO_INFINITIVO_DESINENCIAS = ['ar', 'er', 'ir']
VERBO_INFINITIVO_SUFIJOS = ['lo', 'la', 'le', 'las', 'los', 'les', 'se', 'selo', 'sela', 'selas', 'selos']

def normalizar_verbo_infinitivo(palabra):
    for s in VERBO_INFINITIVO_SUFIJOS:
        if palabra.endswith(s):
            palabra = palabra[:-len(s)]
            break
    for d in VERBO_INFINITIVO_DESINENCIAS:
        if palabra.endswith(d):
            palabra = palabra[:-len(d)]
            break
    return palabra + '*'

def es_verbo_infinitivo(palabra, nuevo=False):
    if palabra[:1].lower() != palabra[:1]:
        return False
    for d in VERBO_INFINITIVO_DESINENCIAS:
        for s in [''] + VERBO_INFINITIVO_SUFIJOS:
            if palabra.endswith(d + s):
                if nuevo and normalizar_verbo_infinitivo(palabra) in VERBOS_RESERVADOS:
                    return False
                else:
                    return True
    return False

