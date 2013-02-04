#!/usr/bin/python

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

