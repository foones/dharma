#!/usr/bin/python

class ConnectorDefinition(object):

    def __init__(self, local_port, subcomponent_id, remote_port):
        self._local_port = local_port
        self._subcomponent_id = subcomponent_id
        self._remote_port = remote_port

    def __repr__(self):
        return '<local:%s %s:%s>' % (self._local_port, self._subcomponent_id, self._remote_port)

class ComponentDefinition(object):

    def __init__(self, name, input_ports, output_ports):
        self.name = name

        self._input_ports = set(input_ports)
        self._output_ports = set(output_ports)
        self._internal_ports = set()
        self._subcomponent_defs = []
        self._connector_defs = []

    def output_ports(self):
        return self._output_ports

    def external_ports(self):
        return self._output_ports | self._input_ports

    def all_ports(self):
        return self.external_ports() | self._internal_ports

    def declare_port(self, port_name):
        if not self.is_port(port_name):
            self._internal_ports.append(port_name)

    def is_port(self, port_name):
        return port_name in self.all_ports()

    def check_external_ports(self, ports):
        return self.external_ports() == set(ports)

    def check_input_ports(self, input_ports):
        return self._input_ports == set(input_ports)

    def _add_subcomponent_def(self, subcomponent_def):
        self._subcomponent_defs.append(subcomponent_def)
        return len(self._subcomponent_defs) - 1

    def add_subcomponent(self, subcomponent_def, remote_ports, local_ports):
        assert len(remote_ports) == len(local_ports)
        assert subcomponent_def.check_external_ports(remote_ports)
        for port in local_ports:
            assert self.is_port(port)
        subcomponent_id = self._add_subcomponent_def(subcomponent_def)
        for remote_port, local_port in zip(remote_ports, local_ports):
            self._connector_defs.append(ConnectorDefinition(local_port, subcomponent_id, remote_port))

    def subcomponent_definitions(self):
        return self._subcomponent_defs

    def connector_definitions(self):
        return self._connector_defs

    def show_external_ports(self):
        return ' '.join([
            ('!' if port in self._output_ports else '') + port
            for port in self.external_ports()
        ])

    def __repr__(self):
        return '<ComponentDefinition %s %s>' % (self.name, self.show_external_ports())

#class Interface(object):
#    def __init__

BIT0 = 0
BIT1 = 1

FALSE_COMPONENT = ComponentDefinition('False', [], ['a'])
NAND_COMPONENT = ComponentDefinition('Nand', ['a', 'b'], ['c'])

class Component(object):

    def __init__(self, component_def):
        self._definition = component_def
        #self._subcomponents
        #    Component(subcomponent.component_def)
        self._subinstances = [
            subcomponent
            for subcomponent in definition.subcomponents()
        ]
        self._state = {}
        for port in self._definition.all_ports():
            self._state[port] = BIT0

    def external_state(self):
        res = {}
        for port in self._definition.external_ports():
            res[port] = self._state[port]
        return res

    def tick(self, inputs):
        input_ports = []
        values = []
        for value in inputs:
            assert len(port_val) == 2
            port, value = port_val
            assert value in [0, 1]
            input_ports.append(port)
        assert self._definition.check_input_ports(input_ports)

        for port, value in inputs:
            self._state[port] = value

        #for comp_def, _ in definition:

class Connector(object):

    def __init__(self):
        self._interfaces = []

    def add_interface(self, iface):
        self._interfaces.append(iface)

