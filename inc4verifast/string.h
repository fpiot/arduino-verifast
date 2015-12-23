/* Copyright (c) 2002,2007 Marek Michalkiewicz
   All rights reserved.

   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions are met:

   * Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.

   * Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in
     the documentation and/or other materials provided with the
     distribution.

   * Neither the name of the copyright holders nor the names of
     contributors may be used to endorse or promote products derived
     from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE. */

/* $Id$ */

/*
   string.h

   Contributors:
     Created by Marek Michalkiewicz <marekm@linux.org.pl>
 */

#ifndef	_STRING_H_
#define	_STRING_H_ 1

#define	__need_NULL
#define	__need_size_t
#include <stddef.h>

#ifndef __ATTR_PURE__
#define __ATTR_PURE__ __attribute__((__pure__))
#endif

#ifndef __ATTR_CONST__
# define __ATTR_CONST__	__attribute__((__const__))
#endif

#ifdef __cplusplus
extern "C" {
#endif

/** \file */
/** \defgroup avr_string <string.h>: Strings
    \code #include <string.h> \endcode

    The string functions perform string operations on NULL terminated
    strings. 

    \note If the strings you are working on resident in program space (flash),
    you will need to use the string functions described in \ref avr_pgmspace. */


/** \ingroup avr_string

    This macro finds the first (least significant) bit set in the
    input value.

    This macro is very similar to the function ffs() except that
    it evaluates its argument at compile-time, so it should only
    be applied to compile-time constant expressions where it will
    reduce to a constant itself.
    Application of this macro to expressions that are not constant
    at compile-time is not recommended, and might result in a huge
    amount of code generated.

    \returns The _FFS() macro returns the position of the first
    (least significant) bit set in the word val, or 0 if no bits are set.
    The least significant bit is position 1.  Only 16 bits of argument
    are evaluted.
*/
#if defined(__DOXYGEN__)
#define _FFS(x)
#else  /* !DOXYGEN */
#define	_FFS(x) \
	(1				\
	 + (((x) & 1) == 0)		\
	 + (((x) & 3) == 0)		\
	 + (((x) & 7) == 0)		\
	 + (((x) & 017) == 0)		\
	 + (((x) & 037) == 0)		\
	 + (((x) & 077) == 0)		\
	 + (((x) & 0177) == 0)		\
	 + (((x) & 0377) == 0)		\
	 + (((x) & 0777) == 0)		\
	 + (((x) & 01777) == 0)		\
	 + (((x) & 03777) == 0)		\
	 + (((x) & 07777) == 0) 	\
	 + (((x) & 017777) == 0)	\
	 + (((x) & 037777) == 0)	\
	 + (((x) & 077777) == 0)	\
	 - (((x) & 0177777) == 0) * 16)
#endif /* DOXYGEN */

int ffs (int __val);
int ffsl (long __val);
//int ffsll (long long __val);
void *memccpy(void *a, const void *b, int c, size_t d);
void *memchr(const void *a, int b, size_t c);
int memcmp(const void *a, const void *b, size_t c);
void *memcpy(void *a, const void *b, size_t c);
void *memmem(const void *a, size_t b, const void *c , size_t d);
void *memmove(void *a, const void *b, size_t c);
void *memrchr(const void *a, int b, size_t c);
void *memset(void *a, int b, size_t c);
char *strcat(char *a, const char *b);
char *strchr(const char *a, int b);
char *strchrnul(const char *a, int b);
int strcmp(const char *a, const char *b);
char *strcpy(char *a, const char *b);
int strcasecmp(const char *a, const char *b);
char *strcasestr(const char *a, const char *b);
size_t strcspn(const char *__s, const char *__reject);
char *strdup(const char *s1);
size_t strlcat(char *a, const char *b, size_t c);
size_t strlcpy(char *a, const char *b, size_t c);
size_t strlen(const char *a);
char *strlwr(char *a);
char *strncat(char *a, const char *b, size_t c);
int strncmp(const char *a, const char *b, size_t c);
char *strncpy(char *a, const char *b, size_t c);
int strncasecmp(const char *a, const char *b, size_t c);
size_t strnlen(const char *a, size_t b);
char *strpbrk(const char *__s, const char *__accept);
char *strrchr(const char *a, int b);
char *strrev(char *a);
char *strsep(char **a, const char *b);
size_t strspn(const char *__s, const char *__accept);
char *strstr(const char *a, const char *b);
char *strtok(char *a, const char *b);
char *strtok_r(char *a, const char *b, char **c);
char *strupr(char *a);

#ifdef __cplusplus
}
#endif

#endif /* _STRING_H_ */

