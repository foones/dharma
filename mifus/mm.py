#!/usr/bin/python
from common.utils import MifusException
from component.parser import read_component_defs_from_file

try:
    component_defs = read_component_defs_from_file('Component.defs')
    print component_defs['Not']
    print component_defs['Not']._internal_connectors
    print component_defs['Not']._subcomponents
except MifusException as e:
    print e


