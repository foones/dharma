# coding:utf-8

from comunes.utiles import identar, QuilomboException
from lenguaje.tesoro import tesoro_actual
from lenguaje.terminos import Termino, TNada, evaluar_lista_en

class TTipoInductivo(Termino):

    def __init__(self, nombre_tipo):
        self._nombre_tipo = nombre_tipo
        self._constructores = []

    def agregar_constructor(self, constructor):
        self._constructores.append(constructor)

    def __unicode__(self):
        return self._nombre_tipo

class TConstructor(Termino):
    u"""Nota: un constructor n-ario se identifica con una "instancia"
        del correspondiente tipo en cuanto tiene todos sus parámetros
        instanciados."""

    def __init__(self, tipo, nombre_constructor, nombres_parametros, valores_parametros=None):
        self._tipo = tipo
        self._nombre_constructor = nombre_constructor
        self._nombres_parametros = nombres_parametros
        if valores_parametros is None:
            self._valores_parametros = {}
        else:
            self._valores_parametros = valores_parametros

    def currificar(self, arg):
        for param in self._nombres_parametros:
            if param not in self._valores_parametros:
                valores = {}
                for k, v in self._valores_parametros.items():
                    valores[k] = v
                valores[param] = arg
                return TConstructor(self._tipo, self._nombre_constructor, self._nombres_parametros, valores)
        raise QuilomboException(u'no se le puede pasar un parámetro más al constructor %s, pues ya es un valor' % (self,))

    def currificar_parametro(self, param, arg):
        if param not in self._nombres_parametros:
            raise QuilomboException(u'el constructor %s no tiene un campo %s' % (self._nombre_constructor, param))
        if param in self._valores_parametros:
            raise QuilomboException(u'el constructor %s ya tiene el campo %s definido' % (self, param))
        valores = {}
        for k, v in self._valores_parametros.items():
            valores[k] = v
        valores[param] = arg
        return TConstructor(self._tipo, self._nombre_constructor, self._nombres_parametros, valores)

    def __unicode__(self):
        res = []
        for param in self._nombres_parametros:
            if param in self._valores_parametros:
                param_s = tesoro_actual().sustantivo_comun_singular(param)
                res.append(u'%s: %s' % (param_s, self._valores_parametros[param]))

        if res == []:
            nombre_s = tesoro_actual().sustantivo_comun_singular_con_articulo_determinado(self._nombre_constructor)
            return nombre_s
        elif len(res) == 1:
            nombre_s = tesoro_actual().sustantivo_comun_singular_con_articulo_indeterminado(self._nombre_constructor)
            return nombre_s + ' que tiene como ' + res[0]
        else:
            nombre_s = tesoro_actual().sustantivo_comun_singular_con_articulo_indeterminado(self._nombre_constructor)
            return nombre_s + ' que tiene\n' + identar(',\n'.join(res[:-1]) + '\ny ' + res[-1])

    def aridad(self):
        return len(self._nombres_parametros) - len(self._valores_parametros)

    def valores_parametros(self):
        return self._valores_parametros

    def nombre_constructor(self):
        return self._nombre_constructor

class TDeclaracionConstructorConParametros(Termino):

    def __init__(self, nombre_constructor, nombres_parametros):
        self.nombre_constructor = nombre_constructor
        self.nombres_parametros = nombres_parametros

    def __unicode__(self):
        return u'TDeclaracionConstructorConParametros(%s, [\n%s\n])' % (
            self.nombre_constructor,
            identar('\n'.join(map(unicode, self.nombres_parametros))),
        )

class TDefinicionDeTipoInductivo(Termino):

    def __init__(self, nombre_tipo, declaraciones_constructores):
        self._nombre_tipo = nombre_tipo
        self._declaraciones_constructores = declaraciones_constructores

    def __unicode__(self):
        return u'TDefinicionDeTipoInductivo(%s, [\n%s\n])' % (
            self._nombre_tipo,
            identar('\n'.join(map(unicode, self._declaraciones_constructores))),
        )

    def evaluar_en(self, estado):
        tipo = TTipoInductivo(
            tesoro_actual().sustantivo_comun_singular(self._nombre_tipo)
        )
        for decl in self._declaraciones_constructores:
            constructor = TConstructor(
                self,
                decl.nombre_constructor,
                decl.nombres_parametros,
            )
            estado.entorno.declarar(decl.nombre_constructor, constructor)
            tipo.agregar_constructor(constructor)
        estado.entorno.declarar(self._nombre_tipo, tipo)
        yield TNada()

class TAplicacionDirectaConstructor(Termino):

    def __init__(self, constructor, parametros):
        self._constructor = constructor
        self._parametros = parametros

    def __unicode__(self):
        ps = []
        for p, v in self._parametros:
            ps.append(u'%s = %s' % (p, v))
        return u'TAplicacionDirectaConstructor(%s, [\n%s\n])' % (
            self._constructor,
            identar('\n'.join(map(unicode, ps)))
        )

    def nombre_constructor(self):
        return self._constructor

    def evaluar_en(self, estado):
        for constructor in self._constructor.evaluar_en(estado):
            nombres_parametros = map(lambda xs: xs[0], self._parametros)
            argumentos_no_evaluados = map(lambda xs: xs[1], self._parametros)
            for args in evaluar_lista_en(argumentos_no_evaluados, estado):
                constructor_ap = constructor

                for nombre_parametro, arg in zip(nombres_parametros, args):
                    constructor_ap = constructor_ap.currificar_parametro(
                        nombre_parametro, 
                        arg
                    )

                yield constructor_ap

class TAplicacionTotalConstructor(Termino):

    def __init__(self, constructor):
        self._constructor = constructor

    def __unicode__(self):
        return u'TAplicacionTotalConstructor(%s)' % (self._constructor,)

    def evaluar_en(self, estado):
        for constructor in self._constructor.evaluar_en(estado):

            if not isinstance(constructor, TConstructor):
                raise QuilomboException(u'%s no es un constructor' % (constructor,))

            npop = min(estado.tam_pila(), constructor.aridad())

            args = []
            for i in range(npop):
                args.append(estado.pop())

            constructor_ap = constructor
            for arg in reversed(args):
                constructor_ap = constructor_ap.currificar(arg)

            # No meterlo en la pila. Para meterlo usar:
            #
            #    guardar el resultado de construir ...
            # O:
            #    meter el resultado de construir ...
            #
            # En lugar de:
            #    construir ...
            #
            #estado.push(constructor_ap)
            yield constructor_ap

class TAplicacionParcialConstructor(Termino):

    def __init__(self, nombre_parametro, valor):
        self._nombre_parametro = nombre_parametro
        self._valor = valor

    def __unicode__(self):
        return u'TAplicacionParcialConstructor(%s, %s)' % (self._nombre_parametro, self._valor)

    def evaluar_en(self, estado):
        constructor = estado.pop()
        for valor in self._valor.evaluar_en(estado):
            if not isinstance(constructor, TConstructor):
                raise QuilomboException(u'%s no es un constructor' % (constructor,))
            constructor_ap = constructor.currificar_parametro(
                self._nombre_parametro, 
                valor
            )
            estado.push(constructor_ap)
            yield constructor_ap

class TMatcheable(Termino):

    def __init__(self, nombre_variable):
        self._nombre_variable = nombre_variable

    def __unicode__(self):
        return u'%s?' % (self._nombre_variable,)

    def nombre(self):
        return self._nombre_variable

    def evaluar_en(self, entorno):
        yield self

def es_matcheable(x):
    return len(x) > 0 and x[0].upper() == x[0]

def join_matches(patron, match1, match2):
    for k, v in match2.items():
        if k in match1:
            raise QuilomboException(u'el patrón "%s" no es un patrón lineal' % (patron,))
        match1[k] = v
    return match1

def pattern_matching(patron, valor):
    if isinstance(patron, TMatcheable):
        return {patron.nombre(): valor}
    elif isinstance(patron, TConstructor):
        if not isinstance(valor, TConstructor):
            return None
        else:
            pn = patron.nombre_constructor()
            vn = valor.nombre_constructor()
            if pn != vn: return None
            ps = patron.valores_parametros()
            vs = valor.valores_parametros()

            match = {}
            for nombre_parametro, subpatron in ps.items():
                if nombre_parametro not in vs:
                    return None
                subvalor = vs[nombre_parametro]
                submatch = pattern_matching(subpatron, subvalor)
                if submatch is None:
                    return None
                else:
                    match = join_matches(patron, match, submatch)
            return match
    else:
        if patron == valor:
            return {}
        else:
            return None

def evaluar_casos_en(valor, casos, estado):
    for patron_no_evaluado, cuerpo in casos:
        for patron in patron_no_evaluado.evaluar_en(estado):
            sustitucion = pattern_matching(patron, valor)
            if sustitucion is not None:
                estado2 = estado.extender(sustitucion)
                for res in cuerpo.evaluar_en(estado2):
                    yield res
                return
    yield TNada()

class TAnalisisDeCasosTopePila(Termino):

    def __init__(self, casos):
        self._casos = casos 

    def __unicode__(self):
        s = []
        for k, v in self._casos:
            s.append(u'%s => %s' % (k, v))
        return u'TAnalisisDeCasosTopePila([\n%s\n])' % (
                    identar(',\n'.join(s)),
                )

    def evaluar_en(self, estado):
        valor = estado.pop()
        for res in evaluar_casos_en(valor, self._casos, estado):
            yield res

class TAnalisisDeCasosExpresion(Termino):

    def __init__(self, expresion, casos):
        self._expresion = expresion 
        self._casos = casos 

    def __unicode__(self):
        s = []
        for k, v in self._casos:
            s.append(u'%s => %s' % (k, v))
        return u'TAnalisisDeCasosExpresion(%s, [\n%s\n])' % (
                    self._expresion,
                    identar(',\n'.join(s)),
                )

    def evaluar_en(self, estado):
        for valor in self._expresion.evaluar_en(estado):
            for res in evaluar_casos_en(valor, self._casos, estado):
                yield res

