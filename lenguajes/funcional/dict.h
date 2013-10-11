#ifndef _FU_DICT_H_
#define _FU_DICT_H_

typedef unsigned long int Key;
#define FU_DICT_CHILD_BITS	1
#define FU_DICT_NCHILDREN	(1 << FU_DICT_CHILD_BITS)
#define FU_DICT_CHILD(KEY)	(KEY & (FU_DICT_NCHILDREN - 1))
#define FU_DICT_NEXT(KEY)	(KEY >> FU_DICT_CHILD_BITS)

typedef struct _Fu_Dict_Node Node;
struct _Fu_Dict_Node {
	void *value;
	Node *child[FU_DICT_NCHILDREN];
};

typedef struct _Fu_Dict {
	Node *root;
} Fu_Dict;
 
void fu_dict_init(Fu_Dict *dict);
void fu_dict_define(Fu_Dict *dict, Key key, void *value);
void *fu_dict_get(Fu_Dict *dict, Key key);

/* Does not free the pointer itself */
void fu_free_dict(Fu_Dict *dict);

#endif
