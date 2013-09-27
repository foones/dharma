# coding:utf-8

from lenguaje.parser import (
    Parser, PToken, PSecuencia, PSecuenciaConAccion, PAlternativa,
    PClausuraConTerminador, PClausuraConTerminadorConAccion,
    PClausura1ConTerminador, PClausura1ConTerminadorConAccion,
    PComplemento, PLookahead, POpcional, PValor, PPalabra,
    PPalabras, PPuntuacion, PEOF,
)
from lenguaje.gramatica import (
    ARTICULOS, PREPOSICIONES, VOCATIVOS, APELATIVOS, NUMEROS_CARDINALES,
    PALABRAS_CLAVE,
)
from lenguaje.terminos import (
    TVariable, TParametro, TInvocarVerbo, TBloque, TNada,
    TDefinicionDeFuncion,
)
from lenguaje.basico.parser import (
    PVerboNuevoInfinitivo, PVocativo, PApelativo, PComa, PPuntoFinal,
    PNominal, PPreposicion, PAlternativaPalabras, PTerminadorFrase,
)
from lenguaje.dimensiones.parser import (
    PDefinicionDeDimension, PDefinicionDeUnidadBasica, PDefinicionDeUnidadDerivada,
    PCantidad, PNumeroPuro, PExpresarCantidadEn,
)
from lenguaje.inductivos.parser import (
    PDefinicionDeTipoInductivo, PAplicacionDirectaConstructor,
    PAplicacionTotalConstructor, PAplicacionParcialConstructor,
    PAnalisisDeCasosTopePila, PAnalisisDeCasosExpresion,
    PMatcheable,
)
from lenguaje.pila.parser import (
    PMeterElemento,
)

class PCabezaDefinicionDeFuncion(PAlternativa):

    def __init__(self, **kwargs):
        cabezas = [
            "la posta para",
            "la posta pa",
            "la posta pa'",
            "la posta si queres",
        ]
        alts = [PPalabras(cabeza) for cabeza in cabezas]
        return PAlternativa.__init__(self, *alts, **kwargs)

class PVariable(PNominal):

    def __init__(self, **kwargs):
        PNominal.__init__(self,
            articulo_obligatorio=True,
            devolver_variable=True,
            **kwargs
        )

class PSeparadorExpresiones(PAlternativa):

    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            PEOF(),

            PComa(),

            PSecuencia(
                POpcional(PPalabra('y')),
                PAlternativa(
                    PPalabra(u'después'),
                    PSecuencia(
                        PAlternativa(
                            PPalabras('a el final'),
                            PPalabras('a el fin'),
                        ),
                        POpcional(PPalabras('de todo')),
                    )
                )
            ),

            PPalabra('pero'),
            **kwargs
        )

    def descripcion(self):
        return u'un separador de expresiones (ej. `,\', `después\', `y al final\')'

class PBloque(PSecuenciaConAccion):
    """El cuerpo de una función consta de expresiones separadas por ",".
       y terminadas por un terminador dado."""
    def __init__(self, terminador_bloque=PPuntoFinal(), **kwargs):

        def accion(expresiones):
            return TBloque(expresiones)

        PSecuenciaConAccion.__init__(self, lambda xs: xs[1],
            POpcional(PPalabra('primero')),
            PClausuraConTerminadorConAccion(accion,
                PExpresion(),
                separador=PSeparadorExpresiones(),
                terminador=terminador_bloque,
            ),
            **kwargs
        )

    def descripcion(self):
        return u'un bloque de expresiones'

class PInvocacionVerboInfinitivo(PSecuenciaConAccion):
    def __init__(self):

        def accion(lista):
            verbo, expresion, argumentos = lista
            if expresion != ():
                argumentos = [TParametro('*', expresion[0])] + argumentos
            return TInvocarVerbo(verbo, argumentos)

        PSecuenciaConAccion.__init__(self, accion,
            PVerboNuevoInfinitivo(),
            POpcional(PExpresion()),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: TParametro(*xs), PPreposicion(), PExpresion()),
                terminador=PLookahead(
                               PAlternativa(
                                   PPuntoFinal(),
                                   PApelativo(),
                                   PSeparadorExpresiones(),
                                   PEOF(),
                               )
                           )
            )
        )

class PDefinicionDeFuncionBasico(PSecuenciaConAccion):
    """Definiciones de funciones son de la forma:

            <cabeza-definicion-de-funcion> <verbo> [<nominal>] [<prep> <nominal>]* es <cuerpo>

    """
    def __init__(self, terminador_bloque=PPuntoFinal(), **kwargs):

        def accion(lista):
            def_, verbo, nominal, argumentos, cuerpo = lista
            if nominal != ():
                argumentos = [TParametro('*', nominal)] + argumentos
            return TDefinicionDeFuncion(verbo, argumentos, cuerpo)

        PSecuenciaConAccion.__init__(self, accion,
            PCabezaDefinicionDeFuncion(),
            PVerboNuevoInfinitivo(),
            POpcional(PNominal()),
            PClausuraConTerminador(
                PSecuenciaConAccion(lambda xs: TParametro(*xs), PPreposicion(), PNominal()),
                terminador=PPalabra('es'),
            ),
            PBloque(terminador_bloque),
            **kwargs
        )

class PBloqueEntreLlaves(PSecuenciaConAccion):
    def __init__(self):
        PSecuenciaConAccion.__init__(self, lambda xs: xs[1],
            PPuntuacion('{'),
            PBloque(terminador_bloque=PPuntuacion('}')),
        )

class PDefinicionDeFuncion(PAlternativa):
    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            PSecuenciaConAccion(lambda xs: xs[2],
                PVocativo(),
                PComa(),
                PDefinicionDeFuncionBasico(
                    terminador_bloque=PApelativo(),
                ),
            ),
            descripcion=u'una declaración de función, usando `che, la posta para ... es ... boludo\'',
            **kwargs
        )

class PExpresion(PAlternativa):
    def __init__(self, **kwargs):
        PAlternativa.__init__(self,
            # un numero
            # Fulano De Tal 
            PVariable(),
            lambda: PBloqueEntreLlaves(),

            # salir
            # sumar ... con ...
            lambda: PInvocacionVerboInfinitivo(),

            # che, la posta para salir es ... boludo
            # che, la posta para sumar una cosa con otra es ... boludo
            lambda: PDefinicionDeFuncion(),

            ## Dimensiones, unidades y cantidades
    
            # che boludo, la distancia es una dimension
            lambda: PDefinicionDeDimension(),

            # che boludo, un metro mide distancia
            lambda: PDefinicionDeUnidadBasica(parser_expresion=PExpresion()),

            # che boludo, un kilometro son mil metros
            # che boludo, un kmph es un <kilometro por hora>
            lambda: PDefinicionDeUnidadDerivada(parser_expresion=PExpresion()),

            # veintipico de kilometros
            # cuatro <kilometros por hora>
            PCantidad(),

            # el número ciento cuatro
            lambda: PNumeroPuro(PSeparadorExpresiones()),

            # expresar en metros
            # expresarlo en <kilometros por hora>
            lambda: PExpresarCantidadEn(parser_expresion=PExpresion()),

            ## Tipos inductivos

            # che, un booleano puede ser posta o quizás ni_en_pedo boludo
            PDefinicionDeTipoInductivo(),

            # un círculo que tenga
            #    centro: un metro,
            #    radio: dos metros
            #    y en color: azul
            lambda: PAplicacionDirectaConstructor(parser_expresion=PExpresion()),

            # dos metros, un metro, crear un círculo
            lambda: PAplicacionTotalConstructor(parser_expresion=PExpresion()),

            # un círculo, cuyo centro es un metro, cuyo radio es dos metros
            lambda: PAplicacionParcialConstructor(parser_expresion=PExpresion()),

            # un valor?
            # X?
            PMatcheable(),

            # fijarse
            #    si es ... entonces ...,
            #    si es ... entonces ...
            #  y si es ... entonces ...
            lambda: PAnalisisDeCasosTopePila(parser_expresion=PExpresion()),

            # fijarse qué pinta tiene ...
            #    si es ... entonces ...,
            #    si es ... entonces ...
            #  y si es ... entonces ...
            #
            lambda: PAnalisisDeCasosExpresion(parser_expresion=PExpresion()),

            ## Manipulación de la pila
            lambda: PMeterElemento(parser_expresion=PExpresion()),

            **kwargs
        )

    def descripcion(self):
        return u'una expresión'

class PPrograma(PBloque):
    def __init__(self, **kwargs):
        PBloque.__init__(self, terminador_bloque=PEOF())

