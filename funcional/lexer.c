#include "common.h"

typedef unsigned int Fu_Token; 

#define Fu_STREAM_MAX_BUF	Fu_MB
typedef struct _Fu_Stream {
	char buffer[Fu_STREAM_MAX_BUF];
	void *sync(struct _Fu_Stream *);
};

Fu_Token tokenize(Fu_Stream *stream)
{
	fu_stream_sync(stream);
}

