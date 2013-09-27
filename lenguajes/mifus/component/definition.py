#!/usr/bin/python

class ConnectorDefinition(object):

    def __init__(self, local_port, subcomponent_id, remote_port):
        self.local_port = local_port
        self.subcomponent_id = subcomponent_id
        self.remote_port = remote_port

    def __repr__(self):
        return '<local:%s %s:%s>' % (self.local_port, self.subcomponent_id, self.remote_port)

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
            self._internal_ports.add(port_name)

    def is_port(self, port_name):
        return port_name in self.all_ports()

    def is_input_port(self, port_name):
        return port_name in self._input_ports

    def is_output_port(self, port_name):
        return port_name in self._output_ports

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

    def component_class(self):
        raise Exception('subclass responsibility')

class BuiltinComponentDefinition(ComponentDefinition):

    def __init__(self, name, input_ports, output_ports, tick_state):
        ComponentDefinition.__init__(self, name, input_ports, output_ports)
        self.tick_state = tick_state

    def component_class(self):
        return BuiltinComponent

    def __repr__(self):
        return '<BuiltinComponentDefinition %s %s>' % (self.name, self.show_external_ports())

class UserComponentDefinition(ComponentDefinition):

    def __init__(self, name, input_ports, output_ports):
        ComponentDefinition.__init__(self, name, input_ports, output_ports)

    def component_class(self):
        return UserComponent

    def __repr__(self):
        return '<UserComponentDefinition %s %s>' % (self.name, self.show_external_ports())

BIT0 = 0
BIT1 = 1

def bit_nand(x, y):
    return 1 - x * y

def tick_false(state):
    state['a'] = BIT0

def tick_nand(state):
    state['c'] = bit_nand(state['a'], state['b'])

FALSE_COMPONENT_DEFINITION = BuiltinComponentDefinition('False', [], ['a'], tick_false)
NAND_COMPONENT_DEFINITION = BuiltinComponentDefinition('Nand', ['a', 'b'], ['c'], tick_nand)

class Connector(object):

    def __init__(self, connector_def, subcomponents):
        self.local_port = connector_def.local_port
        self.subcomponent_id = connector_def.subcomponent_id
        self.subcomponent = subcomponents[connector_def.subcomponent_id]
        self.remote_port = connector_def.remote_port

def make_component(component_def): 
    return component_def.component_class()(component_def)

class Component(object):

    def __init__(self, component_def):
        self._definition = component_def

        self._subcomponents = [
            make_component(subcomponent_def)
            for subcomponent_def in component_def.subcomponent_definitions()
        ]

        self._connectors = [
            Connector(connector_def, self._subcomponents)
            for connector_def in component_def.connector_definitions()
        ]

        self._state = {}
        for port in self._definition.all_ports():
            self._state[port] = BIT0

    def external_state(self):
        res = {}
        for port in self._definition.external_ports():
            res[port] = self._state[port]
        return res

    def is_input_port(self, port_name):
        return self._definition.is_input_port(port_name)

    def is_output_port(self, port_name):
        return self._definition.is_output_port(port_name)

    def state_of_port(self, port_name):
        print self, port_name
        return self._state[port_name]

    def _read_inputs(self, inputs):
        input_ports = []
        values = []
        for port, value in inputs:
            assert value in [BIT0, BIT1]
            input_ports.append(port)
        assert self._definition.check_input_ports(input_ports)
        for port, value in inputs:
            self._state[port] = value

    def tick(self):
        raise Exception('subclass responsibility') 

class BuiltinComponent(Component):

    def __init__(self, component_def):
        Component.__init__(self, component_def)

    def tick(self, inputs):
        self._read_inputs(inputs)
        self._definition.tick_state(self._state)

    def __repr__(self):
        return '<BuiltinComponent %s>' % (self._definition,)

class UserComponent(Component):

    def __init__(self, component_def):
        Component.__init__(self, component_def)

    def tick(self, inputs):
        self._read_inputs(inputs)

        remote_port_values = {}
        for subcomponent_id in range(len(self._subcomponents)):
            remote_port_values[subcomponent_id] = []

        for connector in self._connectors:
            if connector.subcomponent.is_input_port(connector.remote_port):
                remote_port_values[connector.subcomponent_id].append((connector.remote_port, self._state[connector.local_port]))

        for subcomponent_id in range(len(self._subcomponents)):
            subcomponent = self._subcomponents[subcomponent_id]
            subcomponent.tick(remote_port_values[subcomponent_id])

        for connector in self._connectors:
            if connector.subcomponent.is_output_port(connector.remote_port):
                self._state[connector.local_port] = connector.subcomponent.state_of_port(connector.remote_port)

    def __repr__(self):
        return '<UserComponent %s>' % (self._definition,)

