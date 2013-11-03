#ifndef _CIVUTILS_H_
#define _CIVUTILS_H_

#include <stdlib.h>
#include <string.h>

#define DECLARE_VECTOR_TYPE(TVECTOR, T) \
	\
	typedef struct _vector { \
		unsigned int capacity; \
		unsigned int nelems; \
		T *elems; \
	} TVECTOR; \
	TVECTOR *TVECTOR##_new(void); \
	void TVECTOR##_add(TVECTOR *vec, T elem);

#define DEFINE_VECTOR_TYPE(TVECTOR, T) \
	\
	TVECTOR *TVECTOR##_new(void) \
	{ \
		TVECTOR *vec = (TVECTOR *)malloc(sizeof(TVECTOR)); \
		vec->capacity = 1; \
		vec->nelems = 0; \
		vec->elems = (T *)malloc(sizeof(T)); \
		return vec; \
	} \
	\
	void TVECTOR##_add(TVECTOR *vec, T elem) \
	{ \
		if (vec->nelems == vec->capacity) { \
			T *new_elems = (T *)malloc(sizeof(T) * 2 * vec->capacity); \
			memcpy(new_elems, vec->elems, sizeof(T) * vec->capacity); \
			vec->capacity = 2 * vec->capacity; \
			free(vec->elems); \
			vec->elems = new_elems; \
		} \
		vec->elems[vec->nelems++] = elem; \
	}

#endif
