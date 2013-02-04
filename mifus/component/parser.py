#!/usr/bin/python
from common.utils import file_lines, MifusException
from component.definition import ComponentDefinition, FALSE_COMPONENT, NAND_COMPONENT

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
            or_die(name not in component_defs, 'component "%s" already defined' % (name,))
            ports = l[2:] if len(l) > 2 else []
            input_ports = []
            output_ports = []
            for p in ports:
                if p.startswith('!'):
                    output_ports.append(p[1:])
                else:
                    input_ports.append(p)
            current_component_def = ComponentDefinition(name, input_ports, output_ports)
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

            remote_ports = []
            local_ports = []
            for arg in args:
                kvarg = arg.split('=')
                or_die(len(kvarg) == 2, 'argument "%s" should be of the form key=value' % (arg,))
                port, arg = kvarg
                current_component_def.declare_port(arg)
                remote_ports.append(port)
                local_ports.append(arg)

            current_component_def.add_subcomponent(subcomponent_def, remote_ports, local_ports)

            or_die(subcomponent_def.check_external_ports(remote_ports),
                   'incorrect port list, expected %s' % (subcomponent_def.show_external_ports(),))

    or_die(current_component_def is None, 'last component has no end')

    return component_defs

