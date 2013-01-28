# coding:utf-8

u"""Herramientas básicas para construir parsers combinatorios."""

import sys

from comunes.utiles import QuilomboException, identar
from lenguaje.ortografia import normalizar

def agregar_max_its(max_its, key):
    if max_its == [] or max_its[0][0].posicion() < key[0].posicion():
        while max_its != []:
            max_its.pop()
        max_its.append(key)
    elif key[0].posicion() == max_its[0][0].posicion():
        max_its.append(key)
    return max_its

class Parser(object):
    """Representa un analizador sintáctico. Toda subclase implementa un
       método self.match(it) que recibe un iterador de tokens y devuelve
       un generador de matches.

       Además, para reporte de errores, las subclases implementan
       self._max_match(it) que recibe un generador de tokens y genera
       los matches que consumen la mayor cantidad de la entrada posible."""

    def __init__(self, descripcion=None):
        self._descripcion = descripcion
        self._match_tabla = {}
        self._max_match_tabla = {}

    def descripcion_completa(self):
        if self._descripcion is not None:
            return self._descripcion
        else:
            return self.descripcion()

    def descripcion(self):
        return unicode(self)

    def match(self, it):
        """Memorización del método self._match implementado por cada
           subclase."""
        key = it.valor_hash()
        if key in self._match_tabla:
            for r in self._match_tabla[key]:
                yield r
        else:
            rs = []
            for r in self._match(it):
                yield r
                rs.append(r)
            self._match_tabla[key] = rs

    def max_match(self, it):
        """Memorización del método self._max_match implementado por cada
           subclase."""
        key = it.valor_hash()
        if key in self._max_match_tabla:
            for r in self._max_match_tabla[key]:
                yield r
        else:
            rs = []
            for r in self._max_match(it):
                yield r
                rs.append(r)
            self._max_match_tabla[key] = rs

    def mensaje_de_error(self, it):
        msj = u'Tu programa es fruta.'

        max_its = []
        for r in self.max_match(it):
            max_its = agregar_max_its(max_its, r)

        fallos = []
        for _it, subparser in max_its:
            descripcion = subparser.descripcion_completa()
            if descripcion is not None:
                fallos.append(descripcion)
            it2 = _it

        if fallos != []:
            if len(fallos) == 1:
                comentario = ''
            else:
                comentario = ' alguna de las siguientes cosas'
            msj += u'\nEsperaba%s:\n%s' % (comentario, identar('\n'.join(fallos)),)
            msj += u'\n---\nCerca de:\n\n%s\n' % (identar(it2.contexto()),)
        return msj

def coincide(referencia, x):
    if referencia is None:
        return True
    else:
        return referencia == x

def texto_coincide(referencia, x):
    if referencia is None:
        return True
    else:
        return normalizar(referencia) == normalizar(x)

class PToken(Parser):
    """Analizador que exige coincidencia literal con un terminal,
       ya sea por su tipo, su valor o ambos."""

    def __init__(self, predicado=None, tipo=None, valor=None, resultado=None, func_resultado=None, **kwargs):
        assert resultado is None or func_resultado is None

        Parser.__init__(self, **kwargs)

        self._tipo = tipo
        self._valor = valor
        self._predicado = predicado
        self._resultado = resultado
        self._func_resultado = func_resultado

    def _match(self, it):
        ok = True
        tok = it.token_actual()

        if self._predicado is not None:
            ok = ok and self._predicado(tok)

        ok = ok and coincide(self._tipo, tok.tipo)
        ok = ok and texto_coincide(self._valor, tok.valor)

        if self._func_resultado is not None:
            resultado = self._func_resultado(tok)
        elif self._resultado is not None:
            resultado = self._resultado
        else:
            resultado = tok

        if ok:
            yield resultado, it.avanzar()

    def _max_match(self, it):
        for _, it2 in self.match(it):
            yield it2, 'ok'
        yield it, self

    def descripcion(self):
        if self._valor is not None:
            return u'el símbolo "%s"' % (self._valor,)
        elif self._tipo is not None:
            return u'un símbolo de tipo <%s>' % (self._tipo,)
        else:
            return u'el símbolo esperado'

def max_match_wrapper(parser, it, subparsers):
    res = []
    i = -1
    for sub in subparsers:
        i += 1
        if callable(sub):
            sub = subparsers[i] = sub()
        for r in sub.max_match(it):
            res.append(r)

    yield_self = []
    for r in res:
        if r[0].posicion() == it.posicion() and r[1] != 'ok':
            yield_self.append(r)
        else:
            yield r

    if len(yield_self) > 1 or res == []:
        yield it, parser
    elif len(yield_self) == 1:
        yield yield_self[0]

class PValor(Parser):
    """PValor(valor, parser) reconoce las mismas entradas que el parser
       dado, pero ignora el valor devuelto por el parser y devuelve el
       valor dado."""

    def __init__(self, valor, parser, *args, **kwargs):
        Parser.__init__(self, *args, **kwargs)
        self._valor = valor
        self._parser = parser

    def _match(self, it):
        for res1, it1 in self._parser.match(it):
            yield self._valor, it1

    def _max_match(self, it):
        return max_match_wrapper(self, it, [self._parser])

    def descripcion(self):
        self._parser.descripcion()

class PLookahead(Parser):
    u"Se fija que la entrada coincida con lo esperado sin consumirla."

    def __init__(self, parser, *args, **kwargs):
        Parser.__init__(self, *args, **kwargs)
        self._parser = parser

    def _match(self, it):
        for res1, it1 in self._parser.match(it):
            yield res1, it

    def _max_match(self, it):
        for it1, ok_fail1 in max_match_wrapper(self, it, [self._parser]):
            if ok_fail1 == 'ok':
                yield it, 'ok'
            else:
                yield it1, ok_fail1

class PComplemento(Parser):
    u"Tiene éxito sii el parser dado no tiene éxito. No consume la entrada."

    def __init__(self, parser, *args, **kwargs):
        Parser.__init__(self, *args, **kwargs)
        self._parser = parser

    def _match(self, it):
        exito = False
        for res1, it1 in self._parser.match(it):
            exito = True
            break
        if not exito:
            yield None, it

    def _max_match(self, it):
        for it1, ok_fail1 in self._parser.max_match(it):
            if ok_fail1 == 'ok':
                yield it, self
                return
        yield it, 'ok'

class PAlternativa(Parser):
    u"Introduce una alternativa no determinística entre varios parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = list(parsers)

    def _match(self, it):
        i = -1
        for parser in self._parsers:
            i += 1
            if callable(parser):
                parser = parser()
                self._parsers[i] = parser

            for r in parser.match(it):
                yield r

    def descripcion(self):
        ds = []
        for p in self._parsers:
            if callable(p):
                ds.append('<thunk>')
                continue
            d = p.descripcion()
            if d is not None:
                ds.append(d)
        return 'alguna de las siguientes cosas:\n' + identar('\n'.join(ds))

    def _max_match(self, it):
        return max_match_wrapper(self, it, self._parsers)

class PSecuencia(Parser):
    u"Yuxtaposición de parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = parsers

    def _match(self, it):
        if self._parsers == ():
            yield [], it
        else:
            p = self._parsers[0]
            ps = PSecuencia(*self._parsers[1:])
            for res1, it1 in p.match(it):
                for res2, it2 in ps.match(it1):
                    yield [res1] + res2, it2

    def _max_match(self, it):
        if self._parsers == ():
            yield it, 'ok'
        else:
            p = self._parsers[0]
            ps = PSecuencia(*self._parsers[1:])
            for it1, ok_fail1 in p.max_match(it):
                if ok_fail1 == 'ok':
                    for it2, ok_fail2 in ps.max_match(it1):
                        yield it2, ok_fail2
                else:
                    yield it1, ok_fail1

    def descripcion(self):
        ds = [d for p in self._parsers for d in [p.descripcion()] if d is not None]
        return 'una secuencia de las siguientes cosas:\n' + identar('\n'.join(ds))

class PSecuenciaConAccion(PSecuencia):

    def __init__(self, accion, *parsers, **kwargs):
        PSecuencia.__init__(self, *parsers, **kwargs)
        self._accion = accion

    def _match(self, it):
        for res1, it1 in PSecuencia._match(self, it):
            yield self._accion(res1), it1

class PClausuraConTerminador(Parser):

    def __init__(self, parser, terminador, separador=None, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser
        self._terminador = terminador
        self._separador = separador

    def _match(self, it):
        if self._separador is None:
            for r in self._match_sin_separador(it): yield r
        else:

            for res1, it1 in self._terminador.match(it):
                yield [], it1
                return

            for r in self._match_con_separador(it): yield r

    def _match_sin_separador(self, it):
        for res1, it1 in self._terminador.match(it):
            yield [], it1
            return
        for res1, it1 in self._parser.match(it):
            for res2, it2 in self._match_sin_separador(it1):
                yield [res1] + res2, it2

    def _match_con_separador(self, it):

        for res1, it1 in self._parser.match(it):
            termina = False
            for res2, it2 in self._terminador.match(it1):
                termina = True 
                yield [res1], it2

            if termina: continue

            for res2, it2 in self._separador.match(it1):
                for res3, it3 in self._match_con_separador(it2):
                    yield [res1] + res3, it3

    def _max_match(self, it):
        max_its = []
        if self._separador is None:
            for r in self._max_match_sin_separador(it):
                yield r
        else:
            for it1, ok_fail1 in self._terminador.max_match(it):
                yield it1, ok_fail1
                if ok_fail1 == 'ok':
                    return
            for it1, ok_fail1 in self._max_match_con_separador(it):
                yield it1, ok_fail1

    def _max_match_sin_separador(self, it):
        for r in self._terminador.max_match(it):
            yield r
        for it1, ok_fail1 in self._parser.max_match(it):
            if ok_fail1 == 'ok':
                for r in self._max_match_sin_separador(it1):
                    yield r
            else:
                yield it1, ok_fail1

    def _max_match_con_separador(self, it):
        for it1, ok_fail1 in self._parser.max_match(it):
            if ok_fail1 == 'ok':

                termina = False
                for it2, ok_fail2 in self._terminador.max_match(it1):
                    if ok_fail2 == 'ok':
                        termina = True
                    yield it2, ok_fail2

                if termina: continue

                for it2, ok_fail2 in self._separador.max_match(it1):
                    if ok_fail2 == 'ok':
                        for r3 in self._max_match_con_separador(it2):
                            yield r3
                    else:
                        yield it2, ok_fail2
            else:
                yield it1, ok_fail1

    def descripcion(self):
        msj = 'una secuencia de cosas de la forma:\n' + identar(self._parser.descripcion())
        if self._separador is None:
            msj += '\n'
        else:
            msj += '\nseparadas por:\n' + identar(self._separador.descripcion()) + '\ny '
        msj += 'terminadas por:\n' + identar(self._terminador.descripcion())
        return msj

class PClausuraConTerminadorConAccion(PClausuraConTerminador):

    def __init__(self, accion, *args, **kwargs):
        PClausuraConTerminador.__init__(self, *args, **kwargs)
        self._accion = accion

    def _match(self, it):
        for res1, it1 in PClausuraConTerminador._match(self, it):
            yield self._accion(res1), it1

class PClausura1ConTerminadorConAccion(PSecuenciaConAccion):
    def __init__(self, accion, parser, terminador, separador=None, **kwargs):
        if separador is None:
            def accion2(lista):
                return accion([lista[0]] + lista[1])
            PSecuenciaConAccion.__init__(self, accion2,
                parser,
                PClausuraConTerminador(
                    parser,
                    terminador=terminador,
                    separador=separador,
                ),
                **kwargs
            )
        else:
            def accion2(lista):
                if lista[1] == ():
                    return accion([lista[0]])
                else:
                    return accion([lista[0]] + lista[1][0])
            PSecuenciaConAccion.__init__(self, accion2,
                parser,
                PAlternativa(
                    PValor((), terminador),
                    PSecuenciaConAccion(lambda xs: (xs[1],),
                        separador,
                        PClausuraConTerminador(
                            parser,
                            terminador=terminador,
                            separador=separador,
                        )
                    )
                ),
                **kwargs
            )

class PClausura1ConTerminador(PClausura1ConTerminadorConAccion):

    def __init__(self, parser, terminador, separador=None, **kwargs):
        PClausura1ConTerminadorConAccion.__init__(self,
            lambda x: x,
            parser,
            terminador=terminador,
            separador=separador,
            **kwargs
        )

class POpcional(Parser):

    def __init__(self, parser, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser

    def _match(self, it):
        for res1, it1 in self._parser.match(it):
            yield (res1,), it1
        yield (), it

    def _max_match(self, it):
        for it1, ok_fail1 in self._parser.max_match(it):
            yield it1, ok_fail1
        yield it, 'ok'

    def descripcion(self):
        return u'opcionalmente: %s' % (self._parser.descripcion(),)

class PEOF(PToken):

    def __init__(self, **kwargs):
        PToken.__init__(self, tipo='EOF', valor='EOF', **kwargs)

    def descripcion(self):
        return 'el final de la entrada'

class PDebug(PClausuraConTerminadorConAccion):
    def __init__(self, parser):
       self._parser = parser 

    def _match(self, it):
        for res1, it1 in self._parser.match(it):
            sys.stderr.write((u'Debugging %s %s' % (unicode(res1), unicode(it1))).encode('utf-8'))
            yield res1, it1

class PPalabra(PToken):

    def __init__(self, palabra, **kwargs):
        self._palabra = palabra
        PToken.__init__(self, tipo='palabra', valor=palabra, **kwargs)

    def descripcion(self):
        return u'la palabra: `%s\'' % (self._palabra,)

class PPuntuacion(PToken):

    def __init__(self, punt, **kwargs):
        PToken.__init__(self, tipo='puntuacion', valor=punt, **kwargs)

class PPalabras(PSecuencia):

    def __init__(self, palabras, **kwargs):
        self._palabras = palabras
        PSecuencia.__init__(self, *[
            PPalabra(pal) for pal in palabras.split(' ')
        ],
        **kwargs)

    def descripcion(self):
        return u'las palabras: `%s\'' % (self._palabras,)

