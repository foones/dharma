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
    }
    for original, cambiado in reemplazo.items():
        texto = texto.replace(original, cambiado)
    return texto

