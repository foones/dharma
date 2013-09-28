#ifndef _FU_LEXER_H_
#define _FU_LEXER_H_

#include <stdio.h>
#include "common.h"

/* Streams */

#if 0
#define Fu_STREAM_MAX_BUF	(16 * Fu_KB)
#endif
#define Fu_STREAM_MAX_BUF	5
#define Fu_STREAM_EOF		0x100

typedef struct _Fu_Position {
	char *source;	/* Name of the source */
	uint col;	/* Column */
	uint row;	/* Row */
} Fu_Position;

typedef struct _Fu_Stream {
	int bufsiz;		/* Size of each half of the buffer */
	uint bufp;		/* Which half we are in:
				 * 0x0 = first half
				 * 0xff = second half
				 */
	uint bufi;		/* Index inside the half we are in. */
	uint buflen;		/* Length of the current half of the buffer.
				 * If buflen < bufsiz, we are on the last
				 * chunk of the input.
				 */
	Fu_Position pos;	/* Position of the stream */
	void *rep;
	void (*sync)(struct _Fu_Stream *);
	uchar data[];
} Fu_Stream;

Fu_Stream *fu_stream_from_file(char *filename, FILE *f);

/* Lexer */

typedef struct _Fu_Lexer {
	Fu_Stream *stream;
} Fu_Lexer;

typedef uint Fu_Token; 
Fu_Lexer *fu_lexer_from_stream(Fu_Stream *stream);
Fu_Token fu_lexer_next_token(Fu_Lexer *lexer);

#define Fu_TOK_EOF	0x100

#endif
