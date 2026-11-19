#ifndef QUIRE_SEAL_H
#define QUIRE_SEAL_H
/* The page seal in `quire_seal.c`: FNV-1a-64 with the checksum field at `off` zeroed,
   then the hash written at `off`. The arguments are Wiz `Bytes` values (word-sized). */
unsigned long wiz_store_seal(unsigned long v, unsigned long off);
#endif
