#ifndef _DMI_H
#define _DMI_H
#include <stdint.h>

struct req {
  uint32_t addr;
  uint32_t op;
  uint32_t data;
};

struct resp {
  uint32_t resp;
  uint32_t data;
};

#endif