#ifndef _CIVUNIT_H_
#define _CIVUNIT_H_

#include "utils.h"
#include "map.h"

typedef int UnitDomain;

typedef struct _unit_type {
	int moves;	/* Movement rate (spaces per turn) */
	int domain;	/* 0 = ground, 1 = air, 2 = sea */

	int att;	/* Chance to score hit attacking */
	int def;	/* Change to score hit defending */
	int hit;	/* Hit points */
} UnitType;

#define UNIT_DOMAIN_GROUND	0
#define UNIT_DOMAIN_AIR		1
#define UNIT_DOMAIN_SEA		2

typedef struct _unit {
	struct _tribe *tribe;	/* use struct _tribe to break inclusion cycle */
	UnitType *type;
	int pos_i;
	int pos_j;

	int hit_left;		/* hit points left */
	int moves_left;		/* at current turn */
} Unit;

DECLARE_VECTOR_TYPE(UnitVector, Unit *)

extern UnitType *settlers;

Unit *unit_new(UnitType *unit_type);
int unit_can_step_on_terrain(Unit *unit, Terrain *terrain);
int unit_has_moves_left(Unit *unit);

#endif
