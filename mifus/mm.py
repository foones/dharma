#!/usr/bin/python
from common.utils import MifusException
from component.parser import read_component_defs_from_file

try:
    component_defs = read_component_defs_from_file('Component.defs')
    print component_defs['Not']
    print component_defs['Not']._internal_ports
    print component_defs['Not'].subcomponent_definitions()
    print component_defs['Not'].connector_definitions()

    #inst = ComponentInstance(component_defs['Not'])
    #print inst.external_state()
    #inst.tick([('a', 0)])
    #print inst.external_state()

except MifusException as e:
    print e


