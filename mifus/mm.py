#!/usr/bin/python
from common.utils import MifusException
from component.parser import read_component_defs_from_file
from component.definition import make_component

try:
    component_defs = read_component_defs_from_file('Component.defs')
    print component_defs['Not']
    print component_defs['Not']._internal_ports
    print component_defs['Not'].subcomponent_definitions()
    print component_defs['Not'].connector_definitions()

    inst = make_component(component_defs['Test'])
    print inst.external_state()
    inst.tick([])
    print inst.external_state()
    inst.tick([])
    print inst.external_state()
    inst.tick([])
    print inst.external_state()
    inst.tick([])
    print inst.external_state()

except MifusException as e:
    print e


