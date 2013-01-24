# coding:utf-8

u"""Herramientas básicas para construir parsers combinatorios."""

from comunes.utiles import identar
from idioma.ortografia import normalizar

class Parser(object):
    """Representa un analizador sintáctico. Toda subclase implementa un
       método self.match(it) que recibe un iterador de tokens y devuelve
       un generador de matches."""

    def __init__(self, descripcion=None):
        self._descripcion = descripcion

    def descripcion_completa(self):
        if self._descripcion:
            return self._descripcion
        else:
            return self.descripcion()

    def descripcion(self):
        return repr(self)

    def mensaje_de_error(self, it):
        msj = 'Tu programa es fruta.'
        d = self.descripcion_completa()
        if d is not None:
            msj += '\nEsperaba: ' + d
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

    def match(self, it):
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

    def descripcion(self):
        if self._valor is not None:
            return 'el símbolo "' + self._valor + '"'
        elif self._tipo is not None:
            return 'un símbolo tipo <' + self._tipo + '>'
        else:
            return 'el símbolo esperado'

class PValor(PToken):
    """PValor(valor, parser) reconoce las mismas entradas que el parser
       dado, pero ignora el valor devuelto por el parser y devuelve el
       valor dado."""

    def __init__(self, valor, parser):
        self._valor = valor
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield self._valor, it1

class PLookahead(object):
    u"Se fija que la entrada coincida con lo esperado sin consumirla."

    def __init__(self, parser):
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield res1, it

class PComplemento(object):
    u"Tiene éxito sii el parser dado no tiene éxito. No consume la entrada."

    def __init__(self, parser):
        self._parser = parser

    def match(self, it):
        exito = False
        for res1, it1 in self._parser.match(it):
            exito = True
            break
        if not exito:
            yield None, it

class PAlternativa(Parser):
    u"Introduce una alternativa no determinística entre varios parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = parsers

    def match(self, it):
        for p in self._parsers:
            if callable(p): p = p()
            for r in p.match(it):
                yield r

    def descripcion(self):
        ds = [d for p in self._parsers for d in [p.descripcion()] if d is not None]
        return 'alguna de estas cosas:\n' + identar('\n'.join(ds))

class PSecuencia(Parser):
    u"Yuxtaposición de parsers."

    def __init__(self, *parsers, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parsers = parsers

    def match(self, it):
        if self._parsers == ():
            yield [], it
        else:
            p = self._parsers[0]
            ps = PSecuencia(*self._parsers[1:])
            for res1, it1 in p.match(it):
                for res2, it2 in ps.match(it1):
                    yield [res1] + res2, it2

class PSecuenciaConAccion(PSecuencia):

    def __init__(self, accion, *parsers, **kwargs):
        PSecuencia.__init__(self, *parsers, **kwargs)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PSecuencia.match(self, it):
            yield self._accion(res1), it1

class PClausuraConTerminador(Parser):

    def __init__(self, parser, terminador, separador=None, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser
        self._terminador = terminador
        self._separador = separador

    def match(self, it):
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

class PClausuraConTerminadorConAccion(PClausuraConTerminador):

    def __init__(self, accion, *args, **kwargs):
        PClausuraConTerminador.__init__(self, *args, **kwargs)
        self._accion = accion

    def match(self, it):
        for res1, it1 in PClausuraConTerminador.match(self, it):
            yield self._accion(res1), it1

class POpcional(Parser):

    def __init__(self, parser, **kwargs):
        Parser.__init__(self, **kwargs)
        self._parser = parser

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            yield (res1,), it1
        yield (), it

class PEOF(PToken):
    def __init__(self, **kwargs):
        PToken.__init__(self, tipo='EOF', valor='EOF', **kwargs)

class PDebug(PClausuraConTerminadorConAccion):
    def __init__(self, parser):
       self._parser = parser 

    def match(self, it):
        for res1, it1 in self._parser.match(it):
            print 'Debugging', unicode(res1), unicode(it1)
            yield res1, it1

class PPalabra(PToken):
    def __init__(self, pal, **kwargs):
        PToken.__init__(self, tipo='palabra', valor=pal, **kwargs)

class PPuntuacion(PToken):
    def __init__(self, punt, **kwargs):
        PToken.__init__(self, tipo='puntuacion', valor=punt, **kwargs)

class PPalabras(PSecuencia):
    def __init__(self, palabras, **kwargs):
        PSecuencia.__init__(self, *[
            PPalabra(pal) for pal in palabras.split(' ')
        ])

