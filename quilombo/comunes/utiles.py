
ENCODING = 'utf-8'

def leer_archivo(nombre_archivo):
    "Lee el contenido de un archivo en el encoding apropiado."

    f = open(nombre_archivo, 'r')
    texto = f.read()
    f.close()
    return texto.decode(ENCODING)
