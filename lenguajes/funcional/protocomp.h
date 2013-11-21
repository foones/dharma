#ifndef _FU_PROTO_H_
#define _FU_PROTO_H_

#include "mm.h"

#define Fu_PROTO_TAG_VARIABLE		0x3
#define Fu_PROTO_MK_VARIABLE(ID)	Fu_MM_MK_IMMEDIATE((ID), Fu_PROTO_TAG_VARIABLE)
#define Fu_PROTO_TAG_LAMBDA_VAR		0x4
#define Fu_PROTO_MK_LAMBDA_VAR(ID)	Fu_MM_MK_IMMEDIATE((ID), Fu_PROTO_TAG_LAMBDA_VAR)

#define Fu_PROTO_MK_ABSTRACTION(MM, ID, BODY)	(fu_cons((MM), Fu_PROTO_MK_LAMBDA_VAR(ID), (BODY)))

Fu_VM *fu_proto_compile_definition(Fu_MM *mm, Fu_VM *vm, Fu_Object *body);

#endif
