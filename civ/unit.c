#include "unit.h"

DEFINE_VECTOR_TYPE(UnitVector, Unit *)

static UnitType _settlers = {
	1,		/* move */
	DOMAIN_GROUND,	/* domain */

	0,		/* att */
	1,		/* def */
	1,		/* hit */
};
UnitType *settlers = &_settlers;

Unit *unit_new(UnitType *unit_type)
{
	Unit *unit = (Unit *)malloc(sizeof(Unit));
	unit->type = unit_type;
	unit->pos_i = -1;
	unit->pos_j = -1;
	return unit;
}

int unit_can_step_on_terrain(Unit *unit, Terrain *terrain)
{
	switch (unit->type->domain) {
	case DOMAIN_AIR:
		return 1;
	case DOMAIN_GROUND:
		return terrain != ocean;
	case DOMAIN_SEA:
		return terrain == ocean;
	}
	return 0;
}
