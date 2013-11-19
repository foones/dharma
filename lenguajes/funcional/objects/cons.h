#ifndef _FU_OBJ_CONS_H_
#define _FU_OBJ_CONS_H_

extern Fu_MMTag fu_cons_tag;

typedef struct _Fu_Cons {
	Fu_Object *head;
	Fu_Object *tail;
} Fu_Cons;

Fu_Object *fu_cons(Fu_MM *mm, Fu_Object *head, Fu_Object *tail);

#define Fu_IS_CONS(X)		Fu_MM_IS_OF_TYPE(X, fu_cons_tag)
#define Fu_OBJ_AS_CONS(X)	Fu_MM_OBJ_AS_OF_TYPE(X, Fu_Cons)
#define Fu_CONS_HEAD(X)		(Fu_OBJ_AS_CONS(X)->head)
#define Fu_CONS_TAIL(X)		(Fu_OBJ_AS_CONS(X)->tail)

#endif
