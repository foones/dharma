#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "lexer.h"

#define current_buffer(S)	(&((S)->data[(S)->bufp & (S)->bufsiz]))
#define alternate_buffer(S)	(&((S)->data[(~(S)->bufp) & (S)->bufsiz]))

static void sync_file_stream(Fu_Stream *stream)
{
	assert(stream->bufi == stream->bufsiz && stream->buflen == stream->bufsiz);
	FILE *f = (FILE *)stream->rep;
	stream->bufp = ~stream->bufp;
	stream->bufi = 0;
	stream->buflen = fread(current_buffer(stream), sizeof(char), stream->bufsiz, f);
}

Fu_Stream *fu_stream_from_file(char *filename, FILE *f)
{
	int size = Fu_STREAM_MAX_BUF;
	Fu_Stream *stream = (Fu_Stream *)malloc(sizeof(Fu_Stream) + 2 * size);
	stream->bufsiz = size;
	stream->buflen = size;
	stream->bufp = 0;
	stream->bufi = stream->bufsiz;
	stream->rep = (void *)f;
	stream->sync = &sync_file_stream;
	stream->pos.source = filename;
	stream->pos.col = 1;
	stream->pos.row = 1;
	return stream;
}

#define stream_sync(S)	((S)->sync(S))

uint fu_stream_peek(Fu_Stream *stream)
{
	uint ch;
	if (stream->bufi < stream->buflen) {
		ch = current_buffer(stream)[stream->bufi];
	} else if (stream->buflen < stream->bufsiz) {
		ch = Fu_STREAM_EOF;
	} else {
		stream_sync(stream);
		if (stream->bufi >= stream->buflen) {
			ch = Fu_STREAM_EOF;
		} else {
			ch = current_buffer(stream)[stream->bufi];
		}
	}
	return ch;
}

#define fu_stream_next(S) { \
	assert((S)->bufi < (S)->buflen); \
	(S)->bufi++; \
}

#define stream_max_tok_len(S)	((S)->bufsiz)

/*
 * Copy the last n characters read from the stream to the given buffer.
 * - At least n characters should have been read from the stream.
 * - n should be at most stream_max_tok_len(stream).
 * - The buffer should be of length at least (n + 1).
 */
void fu_stream_copy_last(Fu_Stream *stream, int n, uchar *buf)
{
	int l = 0;
	if (n > stream_max_tok_len(stream)) {
		fu_fail("maximum token length (%u) exceeded\n", stream_max_tok_len(stream));
	}
	if (n > stream->bufi) {
		l = n - stream->bufi;
		n = stream->bufi;
		strncpy((char *)buf, (char *)&(alternate_buffer(stream)[stream->bufsiz - l]), l);
	}
	assert(n <= stream->bufi);
	strncpy((char *)&buf[l], (char *)&(current_buffer(stream)[stream->bufi - n]), n);
	buf[l + n] = '\0';
}

/* Lexer */

#define is_whitespace(X)	((X) == ' ' || (X) == '\t' || (X) == '\r' || (X) == '\n')
#define is_digit(X)		('0' <= (X) && (X) <= '9')
#define is_alpha(X)		(('a' <= (X) && (X) <= 'z') || ('A' <= (X) && (X) <= 'Z'))
#define is_alnum(X)		(is_digit(X) || is_alpha(X))
#define is_ident(X)		(is_alnum(X) || (X) == '_')

Fu_Lexer *fu_lexer_from_stream(Fu_Stream *stream)
{
	Fu_Lexer *lexer = malloc(sizeof(Fu_Lexer));
	lexer->stream = stream;
	return lexer;
}

Fu_Token fu_lexer_next_token(Fu_Lexer *lexer)
{
	uint ch = fu_stream_peek(lexer->stream);
	/* Eat up whitespace */
	while (ch != Fu_STREAM_EOF && is_whitespace(ch)) {
		fu_stream_next(lexer->stream);
		ch = fu_stream_peek(lexer->stream);
	}

	if (ch == Fu_STREAM_EOF) {
		return Fu_TOK_EOF;
	}

	if (is_ident(ch)) {
		int len = 0;
		while (is_ident(ch)) {
			len++;
			fu_stream_next(lexer->stream);
			ch = fu_stream_peek(lexer->stream);
		}

		/* Test */
		{
			int j;
			uchar mybuf[1000];
			for (j = 0; j < 1000; j++) mybuf[j] = '^';
			fu_stream_copy_last(lexer->stream, len, mybuf);
			printf("[%s] len=%u\n", mybuf, len);
		}

	} else {
		printf("pass\n");
		fu_stream_next(lexer->stream);
	}

	return 0;
}

