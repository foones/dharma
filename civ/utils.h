#ifndef _CIVUTILS_H_
#define _CIVUTILS_H_

#include <stdlib.h>
#include <string.h>
#include <assert.h>

/* Extensible vector */

#define DECLARE_VECTOR_TYPE(TVECTOR, T) \
	\
	typedef struct TVECTOR##_vector { \
		unsigned int capacity; \
		unsigned int size; \
		T *elems; \
	} TVECTOR; \
	TVECTOR *TVECTOR##_new(void); \
	TVECTOR *TVECTOR##_new_capacity(unsigned int capacity); \
	void TVECTOR##_add(TVECTOR *vec, T elem);

#define DEFINE_VECTOR_TYPE(TVECTOR, T) \
	\
	TVECTOR *TVECTOR##_new_capacity(unsigned int capacity) \
	{ \
		TVECTOR *vec = (TVECTOR *)malloc(sizeof(TVECTOR)); \
		vec->capacity = capacity; \
		vec->size = 0; \
		vec->elems = (T *)malloc(sizeof(T) * capacity); \
		return vec; \
	} \
	\
	TVECTOR *TVECTOR##_new(void) \
	{ \
		return TVECTOR##_new_capacity(1); \
	} \
	\
	void TVECTOR##_add(TVECTOR *vec, T elem) \
	{ \
		if (vec->size == vec->capacity) { \
			T *new_elems = (T *)malloc(sizeof(T) * 2 * vec->capacity); \
			memcpy(new_elems, vec->elems, sizeof(T) * vec->capacity); \
			vec->capacity = 2 * vec->capacity; \
			free(vec->elems); \
			vec->elems = new_elems; \
		} \
		vec->elems[vec->size++] = elem; \
	}

#define AT(VECTOR, I)	((VECTOR)->elems[(I)])

/* Bounded queue */

#define DECLARE_QUEUE_TYPE(TQUEUE, T) \
	typedef struct TQUEUE##_queue { \
		T *elems; \
		int capacity; \
		int start; \
		int end; \
	} TQUEUE; \
 	\
	void TQUEUE##_init(TQUEUE *queue, unsigned int capacity); \
	int TQUEUE##_empty(TQUEUE *queue); \
	int TQUEUE##_full(TQUEUE *queue); \
	void TQUEUE##_enqueue(TQUEUE *queue, T elem); \
	T TQUEUE##_dequeue(TQUEUE *queue);

#define DEFINE_QUEUE_TYPE(TQUEUE, T) \
	void TQUEUE##_init(TQUEUE *queue, unsigned int capacity) \
	{ \
		queue->capacity = capacity; \
		queue->elems = (T *)malloc(sizeof(T) * capacity); \
		queue->start = 0; \
		queue->end = 0; \
	} \
	\
	int TQUEUE##_empty(TQUEUE *queue) \
	{ \
		return queue->start == queue->end; \
	} \
 	\
	int TQUEUE##_full(TQUEUE *queue) \
	{ \
		return (queue->end + 1) % queue->capacity == queue->end; \
	} \
 	\
	void TQUEUE##_enqueue(TQUEUE *queue, T elem) \
	{ \
		assert(!TQUEUE##_full(queue)); \
		queue->elems[queue->end] = elem; \
		queue->end = (queue->end + 1) % queue->capacity; \
	} \
 	\
	T TQUEUE##_dequeue(TQUEUE *queue) \
	{ \
		T elem; \
		assert(!TQUEUE##_empty(queue)); \
		elem = queue->elems[queue->start]; \
		queue->start = (queue->start + 1) % queue->capacity; \
		return elem; \
	}

/* Initialize a bidimensional matrix */

#define INIT_MATRIX(MATRIX, NROWS, NCOLS, VALUE) { \
	int __i, __j; \
	MATRIX = (__typeof__(MATRIX))malloc(sizeof(__typeof__(*MATRIX)) * (NROWS)); \
	for (__i = 0; __i < (NROWS); __i++) { \
		MATRIX[__i] = (__typeof__(*MATRIX))malloc(sizeof(__typeof__(**MATRIX)) * (NCOLS)); \
		for (__j = 0; __j < (NCOLS); __j++) { \
			MATRIX[__i][__j] = VALUE; \
		} \
	} \
}

#endif
