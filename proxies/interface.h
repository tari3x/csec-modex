
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

/**
 * This file defines the interface that the proxy functions are supposed to use.
 * This interface will be implemented differently depending on the kind of analysis
 * that we are performing. For instance, in the binary tracing case, the interface functions
 * will simply print the concrete values of memory buffers, and in the symbolic case
 * they will also add information about the memory location of the buffers.
 */

#ifndef PROXY_INTERFACE
#define PROXY_INTERFACE

#include "common.h"

#include <stdlib.h>

/**
 * Disable tracing. Any code between a matching pair of mute() and unmute()
 * executes as if it were not instrumented. Calls to other interface functions have no effect.
 *
 * This can be used to temporarily suspend tracing, if the real function
 * called from the proxy, calls other proxy functions in turn (which would normally lead to chaos).
*/
EXTERN void mute();
EXTERN void unmute();

/**
 * Add a right hand side from a memory buffer/context attribute/integer value.
 *
 * The order of adding parts of an equation is {rhs}*, sym, lhs.
 */
EXTERN void load_buf(const unsigned char * buf, size_t len, const char * hint);
// can be used for zero-terminated strings, loads everything in the allocated buffer.
EXTERN void load_all(const char * buf, const char * hint);
EXTERN void load_ctx(const void * ctx, const char * attr, const char * hint);
EXTERN void load_int(int n, const char * hint);
EXTERN void load_str(const char * str);

/**
 * Apply an operation to the top of the stack.
 * Deterministic or non-deterministic.
 *
 * The first version sets a known length, the second sets a fresh length and writes it into len.
 */
EXTERN void symL(const char * sym, const char * hint, size_t len, int deterministic);
EXTERN void symN(const char * sym, const char * hint, size_t * len, int deterministic);
EXTERN void symNE(const char * sym, const char * hint, unsigned char * len, size_t lenlen, int deterministic, int nargs);

/**
 * Create a nonce, of a given type and unknown length
 */
EXTERN void newTN(const char * type, const char * hint, size_t * len);
/**
 * Create a nonce, of a given type and known length
 */
EXTERN void newTL(const char * type, const char * hint, size_t len);
/**
 * Create a nonce, of known length l and type fixed_l
 */
EXTERN void newL(const char * hint, size_t len);


EXTERN void varsym(const char * name);
EXTERN void var(const char * name, const unsigned char * buf, const unsigned char * len, size_t lenlen);
EXTERN void varL(const char * name, const unsigned char * buf, size_t len);

/**
 * Add a left hand side. Same versions as for the right hand side.
 *
 * buf must not be NULL.
 */
EXTERN void store_buf(const unsigned char * buf);
// Replace completely the contents of buf with what is on top of stack
EXTERN void store_all(const char * buf);
EXTERN void store_ctx(const void * ctx, const char * attr);
// EXTERN long int lhs_int(long int n, const char * hint);

/**
 * Call instead of store_buf for an equation with an empty left hand side.
 */
EXTERN void event();

/**
 * Append contents of a memory buffer to a bitstring attribute.
 */
EXTERN void add_to_attr(const void * ctx, const char * attr, const unsigned char * buf, size_t len);

/**
 * Set an attribute, same versions as for rhs().
 */
EXTERN void set_attr_str(const void * ctx, const char * attr, const char * str);
EXTERN void set_attr_buf(const void * ctx, const char * attr, const unsigned char * buf, size_t len);
EXTERN void set_attr_int(const void * ctx, const char * attr, int n);

EXTERN int get_attr_int(const void * ctx, const char * attr);

/**
 * Copy an attribute from one context to the other, either a specific attribute
 * or all of them.
 */
EXTERN void copy_ctx(const void * to, const void * from);
EXTERN void copy_attr_ex(const void * to, const char * attr_to, const void * from, const char * attr_from);
EXTERN void copy_attr(const void * to, const void * from, const char * attr);

/**
 * Clear an attribute.
 *
 * FIXME: what is the exact semantics of this, set to empty (0) or
 * set to "doesn't exist"?
 */
EXTERN void clear_attr(const void * ctx, const char * attr);

/**
 * Throw away the symbolic value of an integer and replace it with concrete.
 * This is an identity function for binary case.
 *
 * n should be symbolically initialised before calling this.
 */
EXTERN long int concrete_val(long int n);

/**
 * Return p on the concrete level and a fresh pointer value on the symbolic level.
 * This can be used to model functions that return an internally allocated buffer.
 * This is an identity function for binary case.
 */
// EXTERN void * fresh_ptr(void * p, int size);

/**
 * Put a fresh heap pointer value on the stack.
 */
void fresh_ptr(int size);

/**
 * Specify that the function return value is what's on top of the symbolic stack.
 *
 * Should do nothing in binary case. This function is similar to what lhs_int would be,
 * but it is more safe and versatile, at the cost of not being compatible with binary method.
 * At the same time lhs_int in binary case doesn't make much sense anyway, because it
 * is too short to be reliably unified.
 *
 * Still, when redesigning according to the TODO, it might be better to remove this one.
 */
// EXTERN void sym_return();

#endif /* PROXY_INTERFACE */
