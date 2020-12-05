#ifndef NODEHDEF
#define NODEHDEF

#include "node.h"

typedef struct {
  char *name;
  // More to come. e.g. print proc, safe & release procs
} tlv_type, tlv_type_ptr;

typedef struct {
  tlv_type_ptr type;
  value val;
} tlv_value, *tlv_value_ptr;

#endif
