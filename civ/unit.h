#ifndef _CIVUNIT_H_
#define _CIVUNIT_H_

#include "utils.h"
#include "map.h"

typedef struct _unit_type {
	int move;	/* Movement rate (spaces per turn) */
	int domain;	/* 0 = ground, 1 = air, 2 = sea */

	int att;	/* Chance to score hit attacking */
	int def;	/* Change to score hit defending */
	int hit;	/* Hit points */
} UnitType;

#define DOMAIN_GROUND	0
#define DOMAIN_AIR	1
#define DOMAIN_SEA	2

typedef struct _unit {
	struct _tribe *tribe;	/* use struct _tribe to break inclusion cycle */
	UnitType *type;
	int pos_i;
	int pos_j;
} Unit;

DECLARE_VECTOR_TYPE(UnitVector, Unit *)

extern UnitType *settlers;

Unit *unit_new(UnitType *unit_type);
int unit_can_step_on_terrain(Unit *unit, Terrain *terrain);

#endif
