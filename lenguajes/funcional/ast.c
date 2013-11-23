#include <stdarg.h>

#include "ast.h"

Fu_ASTNode *fu_ast_node(Fu_ASTTag tag, uint nchildren, ...)
{
	Fu_ASTNode *node = malloc(sizeof(Fu_ASTNode) + nchildren * sizeof(Fu_ASTNode *));
	node->tag = tag;

	va_list arglist;
	va_start(arglist, nchildren);
	uint i;
	forn (i, nchildren) {
		node->children[i] = va_arg(arglist, Fu_ASTNode *);
	}
	va_end(arglist);

	return node;
}

