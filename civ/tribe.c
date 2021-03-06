#include "civ.h"

void init_tribe(Tribe *tribe, Color color)
{
	tribe->color = color;
	tribe->units = UnitVector_new();
}

void tribe_add_unit(Tribe *tribe, Unit *unit)
{
	UnitVector_add(tribe->units, unit);
}

