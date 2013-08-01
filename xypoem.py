#!/usr/bin/python
# coding:utf-8:
import re
import os
import random
import sys

if len(sys.argv) < 2:
    print 'Uso: %s [archivo.xy]' % (sys.argv[0],)
    print '     %s html [archivo.xy]' % (sys.argv[0],)
    sys.exit(1)

def arrehtml(l):
    l = l.replace("á","&aacute;")
    l = l.replace("é","&eacute;")
    l = l.replace("í","&iacute;")
    l = l.replace("ó","&oacute;")
    l = l.replace("ú","&uacute;")
    l = l.replace("Á","&Aacute;")
    l = l.replace("É","&Eacute;")
    l = l.replace("Í","&Iacute;")
    l = l.replace("Ó","&Oacute;")
    l = l.replace("Ú","&Uacute;")
    l = l.replace("ü","&uuml;")
    l = l.replace("Ü","&Uuml;")
    l = l.replace("Ñ","&Ntilde;")
    l = l.replace("ñ","&ntilde;")
    l = l.replace("¿","&#191;")
    l = l.replace("¡","&#161;")
    return l

def leer_grafo(fn):

    nodos = {}
    ejes = {}

    f = file(fn, 'r')
    for line in f:
        line = line.strip(' \t\r\n')
        line = re.sub('[ \t\r\n]+', ' ', line)

        line = line.split(' ')
        id_nodo = line[0]
        line = ' '.join(line[1:])
        if '[' in line and ']' in line:
            line = line.split(']')
            descr_ejes = line[0][1:]
            texto = line[1].strip(' \t\r\n')
        else:
            texto = line
            descr_ejes = ''

        nodos[id_nodo] = texto

        direccion = 'outgoing'  
        for dd in descr_ejes.split(' '):
            if dd == '': continue
            if dd == 'a':
                direccion = 'outgoing'
            elif dd == 'de':
                direccion = 'incoming'
            else:
                if direccion == 'incoming':
                    src, tgt = dd, id_nodo
                elif direccion == 'outgoing':
                    src, tgt = id_nodo, dd
                ady = ejes.get(src, set())
                ady.add(tgt)
                ejes[src] = ady

    f.close()
    return nodos, ejes

def bfs(start, nodos, ejes):
    cola = [start]
    distancia = {start: 0} # map id_nodo -> dist
    vistos = set()
    while cola != []:
        nodo = cola.pop(0)
        ady = ejes.get(nodo, [])
        for vecino in ady:
            if vecino not in vistos:
                cola.append(vecino)
                vistos.add(vecino)
                distancia[vecino] = distancia[nodo] + 1

    invdist = {}
    for nodo, dist in distancia.items():
        lst = invdist.get(dist, [])
        lst.append(nodo)
        invdist[dist] = lst

    ds = sorted(invdist.keys())
    niveles = []
    for d in ds:
        niveles.append(sorted(invdist[d]))

    maxniv = 0
    for nivel in niveles:
        maxniv = max(maxniv, len(nivel))

    def completar(nivel):
        res = []
        j = 0
        ancho = float(len(nivel)) / maxniv
        for i in range(maxniv):
            if j + 0.5 < i * ancho and j < len(nivel):
                res.append(nivel[j])
                j += 1
            else:
                res.append(None)
        if j < len(nivel):
            res.extend(nivel[j:])
        return res

    niveles2 = []
    for nivel in niveles:
        nivel = completar(nivel)
        niveles2.append(nivel)
    return niveles2

def diff(p0, p1):
    i0, j0 = p0
    i1, j1 = p1

    if i0 < i1:
        ud = 'd' * (i1 - i0)
    else:
        ud = 'u' * (i0 - i1)

    if j0 < j1:
        lr = 'r' * (j1 - j0)
    else:
        lr = 'l' * (j0 - j1)
    return ud + lr

def armar_tabla(niveles, nodos, ejes, factor_flecha=(1,1)):
    donde_esta = {}

    i = -1
    for nivel in niveles:
        i += 1
        j = -1
        for id_nodo in nivel:
            j += 1
            donde_esta[id_nodo] = (i, j)

    res = []
    res.append('\\documentclass{article}\n')
    res.append('\\usepackage{amsmath}\n')
    res.append('\\usepackage[paperwidth=50cm, paperheight=50cm]{geometry}\n')
    res.append('\\usepackage[all]{xy}\n')
    res.append('\\usepackage[utf8]{inputenc}\n')
    res.append('\\begin{document}\n')
    res.append('$$\\xymatrix@C-=%.2fcm@R-=%.2fcm{\n' % factor_flecha)
    for nivel in niveles:
        for id_nodo in nivel:
            if id_nodo is not None:
                res.append('\\text{' + nodos[id_nodo] + '}')
                for id_vecino in ejes.get(id_nodo, []):
                    res.append('\\ar[' + diff(donde_esta[id_nodo], donde_esta[id_vecino]) + ']')
            res.append(' & ')
        res.append(' \\\\\n')
    res.append('}$$\n')
    res.append('\\end{document}\n')
    return ''.join(res)

def armar_tabla_html(niveles, nodos, ejes):
    donde_esta = {}

    i = -1
    for nivel in niveles:
        i += 1
        j = -1
        for id_nodo in nivel:
            j += 1
            donde_esta[id_nodo] = (i, j)

    res = []
    res.append('<table>')
    for nivel in niveles:
        res.append('</tr>')
        for id_nodo in nivel:
            if id_nodo is None:
                res.append('<td style="padding:10px">&nbsp;</td>')
            elif id_nodo is not None:
                res.append('<td style="padding:10px">' + arrehtml(nodos[id_nodo]) + '</td>')
                #for id_vecino in ejes.get(id_nodo, []):
                #    res.append('\\ar[' + diff(donde_esta[id_nodo], donde_esta[id_vecino]) + ']')
        res.append('</tr>')
    res.append('</table>')
    return ''.join(res)

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'html':
        fn = sys.argv[2]
        style = 'html'
    else:
        fn = sys.argv[1]
        style = 'tex'

    nodos, ejes = leer_grafo(fn)

    niveles = bfs('1', nodos, ejes)

    if style == 'tex':

        tabla = armar_tabla(niveles, nodos, ejes, (1.5, 1.5))
        if fn.endswith('.xy'):
            texfn = fn[:-3] + '.tex'
        else:
            texfn = fn + '.tex'

        f = file(texfn, 'w')
        print tabla
        f.write(tabla)
        f.close()
        print 'Wrote %s' % (texfn,)

        os.system('_pdflatex_evince %s' % (texfn,))

    else:

        tabla = armar_tabla_html(niveles, nodos, ejes)
        if fn.endswith('.xy'):
            htmlfn = fn[:-3] + '.html'
        else:
            htmlfn = fn + '.html'

        f = file(htmlfn, 'w')
        print tabla
        f.write(tabla)
        f.close()
        print 'Wrote %s' % (htmlfn,)

