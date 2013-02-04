#!/usr/bin/python
import re

class MifusException(Exception):
    pass

class ComponentDefinition(object):

    def __init__(self, name, params):
        self.name = name
        self._external_connectors = sorted(params)
        self._internal_connectors = []
        self._subcomponents = []

    def declare_connector(self, connector_name):
        if not self.is_connector(connector_name):
            self._internal_connectors.append(connector_name)

    def is_connector(self, connector_name):
        return connector_name in self._external_connectors or \
               connector_name in self._internal_connectors

    def params(self):
        return self._external_connectors

    def check_params(self, params):
        return self._external_connectors == sorted(params)

    def add_subcomponent(self, subcomponent_def, params, args):
        assert subcomponent_def.check_params(params)
        assert len(params) == len(args)
        for conn in args:
            assert self.is_connector(conn)
        self._subcomponents.append((subcomponent_def, zip(params, args)))

    def __repr__(self):
        return '<component %s %s>' % (self.name, ' '.join(self._external_connectors))

FALSE_COMPONENT = ComponentDefinition('False', ['a'])
NAND_COMPONENT = ComponentDefinition('Nand', ['a', 'b', 'c'])

def file_lines(fn):
    f = open(fn, 'r')
    numline = 0
    for l in f:
        numline += 1
        l = l.split('#')[0].strip(' \t\r\n')
        if l == '': continue
        l = re.sub('[ \t]+', ' ', l)
        yield numline, l

def read_component_defs_from_file(fn):
    numline = None

    def or_die(cond, msg):
        if not cond:
            raise MifusException('"%s":%u: ' % (fn, numline,) + msg)

    component_defs = {'False': FALSE_COMPONENT, 'Nand': NAND_COMPONENT}
    current_component_def = None

    for numline1, l in file_lines(fn):
        numline = numline1
        if l.startswith('component '):
            l = l.split(' ')
            name = l[1]
            params = l[2:] if len(l) > 2 else []
            or_die(name not in component_defs, 'component "%s" already defined' % (name,))
            current_component_def = ComponentDefinition(name, params)
        elif l == 'end':
            or_die(current_component_def is not None, 'no component to end')
            component_defs[current_component_def.name] = current_component_def
            current_component_def = None
        else:
            or_die(current_component_def is not None, 'component usage outside of a definition')
            l = l.split(' ')
            name = l[0]
            args = l[1:]
            or_die(name in component_defs, 'component "%s" is not defined' % (l[0],))
            subcomponent_def = component_defs[name]

            parameters = []
            arguments = []
            for arg in args:
                kvarg = arg.split('=')
                or_die(len(kvarg) == 2, 'argument "%s" should be of the form key=value' % (arg,))
                param, arg = kvarg
                current_component_def.declare_connector(arg)
                parameters.append(param)
                arguments.append(arg)

            current_component_def.add_subcomponent(subcomponent_def, parameters, arguments)

            or_die(subcomponent_def.check_params(parameters),
                   'incorrect parameter list, expected %s' % (subcomponent_def.params(),))

    or_die(current_component_def is None, 'last component has no end')

    return component_defs

try:
    component_defs = read_component_defs_from_file('Component.defs')
    print component_defs['Not']
    print component_defs['Not']._internal_connectors
    print component_defs['Not']._subcomponents
except MifusException as e:
    print e


