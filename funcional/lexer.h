#ifndef _FU_LEXER_H_
#define _FU_LEXER_H_

#include "common.h"

typedef unsigned int Fu_Token; 

#define Fu_STREAM_MAX_BUF	(64 * Fu_KB)

typedef struct _Fu_Stream {
	char buffer[Fu_STREAM_MAX_BUF];
	int bufi;
	void *rep;
	void (*sync)(struct _Fu_Stream *);
} Fu_Stream;

Fu_Stream *fu_stream_from_file(FILE *f);
Fu_Token fu_next_token(Fu_Stream *stream);

#endif
