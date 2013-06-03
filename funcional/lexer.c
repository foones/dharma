#include <stdio.h>
#include <stdlib.h>
#include "lexer.h"

void sync_file_stream(Fu_Stream *stream)
{
	printf("stream: syncing\n");
}

Fu_Stream *fu_stream_from_file(FILE *f)
{
	Fu_Stream *stream = (Fu_Stream *)malloc(sizeof(Fu_Stream));
	stream->bufi = Fu_STREAM_MAX_BUF;
	stream->rep = (void *)f;
	stream->sync = &sync_file_stream;
	return stream;
}

Fu_Token fu_next_token(Fu_Stream *stream)
{
	stream->sync(stream);
	return 0;
}

