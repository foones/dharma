#include <stdlib.h>
#include "dict.h"

#define KEY_LEN		((8 * sizeof(Key)) / FU_DICT_CHILD_BITS)

void fu_dict_init(Fu_Dict *dict)
{
	dict->root = NULL;
}

Node *mk_node()
{
	int i;
	Node *node = (Node *)malloc(sizeof(Node));
	node->value = NULL;
	for (i = 0; i < FU_DICT_NCHILDREN; i++) {
		node->child[i] = NULL;
	}
	return node;
}

void fu_dict_define(Fu_Dict *dict, Key key, void *value)
{
	int i;
	Node **node = &dict->root;
	for (i = 0; i < KEY_LEN;) {
		if (*node == NULL) {
			*node = mk_node();
		}
		node = &(*node)->child[FU_DICT_CHILD(key)];
		key = FU_DICT_NEXT(key);
		i += FU_DICT_CHILD_BITS;
	}
	if (*node == NULL) {
		*node = mk_node();
	}
	(*node)->value = value;
}

void *fu_dict_get(Fu_Dict *dict, Key key)
{
	int i;
	Node *node = dict->root;
	for (i = 0; i < KEY_LEN;) {
		if (node == NULL) {
			return NULL;
		}
		node = node->child[FU_DICT_CHILD(key)];
		key = FU_DICT_NEXT(key);
		i += FU_DICT_CHILD_BITS;
	}
	if (node == NULL) {
		return NULL;
	}
	return node->value;
}

void free_node(Node *node)
{
	if (node == NULL) {
		return;
	}
	int i;
	for (i = 0; i < FU_DICT_NCHILDREN; i++) {
		free_node(node->child[i]);
	}
	free(node);
}

void fu_free_dict(Fu_Dict *dict)
{
	free_node(dict->root);
}

