#ifndef _FU_AST_H_
#define _FU_AST_H_

#include "common.h"

typedef uint64 Fu_ASTTag;

typedef struct _Fu_ASTNode {
	Fu_ASTTag tag;
	struct _Fu_ASTNode *children[];
} Fu_ASTNode;

Fu_ASTNode *fu_ast_node(Fu_ASTTag tag, uint nchildren, ...);

#endif
