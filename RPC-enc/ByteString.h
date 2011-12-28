// Copyright (c) Microsoft (Michal Moskal (michal.moskal@microsoft.com) and Nadia Polikarpova).
// This file is re-distributed with permission as part of the csec-tools examples under the MSR-LA license.
// Licence agreement available online: http://research.microsoft.com/en-us/projects/pex/msr-la.txt

#ifndef _BYTESTRING_H
#define _BYTESTRING_H

#include <vcc.h>
#include <stdint.h>

typedef uint8_t  BYTE;
typedef uint16_t UINT16;
typedef uint32_t UINT32;
typedef uint64_t UINT64;

_(typedef BYTE ByteSequence[\natural];)

_(record ByteString {
    ByteSequence bytes;
    \natural length; })

_(def bool valid(ByteString s)
{	return \forall \natural i; s.length <= i ==> s.bytes[i] == (BYTE) 0; })

_(logic bool nonempty(ByteString s) = valid(s) && s.length > 0)

_(def ByteString empty()
{
  return (ByteString) {
    .length = 0,
    .bytes = \lambda \natural i; (BYTE) 0 };
})

_(def ByteString cons(BYTE b,ByteString s)
  _(requires valid(s))
  _(ensures \result.bytes[0] == b)
{
  return (ByteString) { 
    .length = s.length + 1,
    .bytes = \lambda \natural i; 
      i == 0            ? b : 
      i < s.length + 1  ? s.bytes[i - 1] :
                          (BYTE) 0 };
})

_(def ByteString substring(ByteString s, \natural first, \natural len)
  _(requires valid(s))
  _(requires len < s.length - first + 1)
{
  return (ByteString) { 
    .length = len,
    .bytes = \lambda \natural i; 
      i < len ? s.bytes[first + i] :
                (BYTE) 0 };
})

_(def ByteString concat(ByteString s1, ByteString s2)
  _(requires valid(s1) && valid(s2))
{
  return (ByteString) { 
    .length = s1.length + s2.length,
    .bytes = \lambda \natural i; 
      i < s1.length                               ? s1.bytes[i] :
      s1.length <= i && i < s1.length + s2.length ? s2.bytes [i - s1.length] :
                                                    (BYTE) 0 };
})

_(def ByteString reversed(ByteString s)
  _(requires valid(s))
{
  return (ByteString) { 
    .length = s.length,
    .bytes = \lambda \natural i; 
      i < s.length ? s.bytes [s.length - i - 1]:
                     (BYTE) 0 };
})

_(def ByteString from_array(BYTE a[], \natural size)
  _(reads \universe())
  _(ensures \forall \natural i; i < size ==> a[i] == \result.bytes[i])
  _(ensures \result.length == size)
  _(ensures valid(\result))
{
  return (ByteString) { 
    .length = size,
    .bytes = \lambda \natural i; 
      i < size ? a [i] :
                 (BYTE) 0 };
})

_(def bool contains_byte_string(BYTE a[], ByteString s)
  _(reads \universe())
  _(requires valid(s))
{ return s == from_array(a, s.length); })

_(def ByteString int_bytes(\natural x, size_t size)
  _(ensures valid(\result))
  _(ensures \result.length == size)
  _(decreases size)
{ return size == 0 ? empty() : cons((BYTE)(x % 256),int_bytes(x / 256, size - 1)); })

_(axiom \forall UINT16 x, y; int_bytes((\natural)x, 2) == int_bytes((\natural)y, 2) ==> x == y)
_(axiom \forall UINT32 x, y; int_bytes((\natural)x, 4) == int_bytes((\natural)y, 4) ==> x == y)
_(axiom \forall UINT64 x, y; int_bytes((\natural)x, 8) == int_bytes((\natural)y, 8) ==> x == y)

// /* Lemmas */

_(abstract void lemma_cons_injective(ByteString s1, BYTE b1, ByteString s2, BYTE b2)
  _(requires valid(s1) && valid(s2))
  _(ensures cons(b1,s1) == cons(b2,s2) <==> s1 == s2 && b1 == b2)
{
  _(assert b1 == cons(b1,s1).bytes[0])
  _(assert \forall \natural i; i < s1.length ==> s1.bytes[i] == cons(b1,s1).bytes[i + 1])
})

_(abstract void lemma_concat_associative(ByteString s1, ByteString s2, ByteString s3)
  _(requires valid(s1) && valid(s2) && valid(s3))
  _(ensures concat(s1, concat(s2, s3)) == concat(concat(s1, s2), s3))
{  })

_(abstract void lemma_concat_substring(ByteString s, \natural i)
  _(requires valid(s))
  _(requires i < s.length)
  _(ensures concat(substring(s, 0, i), substring(s, i, s.length - i)) == s)
{  })

_(abstract void lemma_substring_concat(ByteString s1, ByteString s2)
  _(requires valid(s1) && valid(s2))
  _(ensures s1 == substring(concat(s1, s2), 0, s1.length))
  _(ensures s2 == substring(concat(s1, s2), s1.length, s2.length))
{  })

_(abstract void lemma_substring_concat_generic()
  _(ensures \forall ByteString s1, s2; valid(s1) && valid(s2) ==> s1 == substring(concat(s1, s2), 0, s1.length) && s2 == substring(concat(s1, s2), s1.length, s2.length))
{  })

_(abstract void lemma_concat_injective(ByteString s1, ByteString s2, ByteString t1, ByteString t2)
  _(requires valid(s1) && valid(s2) && valid(t1) && valid(t2))
  _(requires s1.length == t1.length)
  _(ensures concat(s1, s2) == concat(t1, t2) <==> s1 == t1 && s2 == t2)
{
  _(assert s1 == substring(concat(s1, s2), 0, s1.length))
  _(assert s2 == substring(concat(s1, s2), s1.length, s2.length))
})

_(abstract void lemma_reverse_twice(ByteString s)
  _(requires valid(s))
  _(ensures reversed(reversed(s)) == s)
{  })

_(abstract void lemma_reverse_injective(ByteString s1, ByteString s2)
  _(requires valid(s1) && valid(s2)) 
  _(ensures reversed(s1) == reversed(s2) <==> s1 == s2)
{
  lemma_reverse_twice(s1);
  lemma_reverse_twice(s2);
})

_(abstract void lemma_from_array_concat(BYTE a[], \natural m, \natural n)
  _(reads \universe())
  _(ensures from_array(a, n + m) == concat(from_array(a, m), from_array(a + m, n)))
{  })

_(abstract void lemma_contains_concat(BYTE a[], ByteString s1, ByteString s2)
  _(reads \universe())
  _(requires valid(s1) && valid(s2))
  _(ensures contains_byte_string(a, concat(s1, s2)) <==> contains_byte_string(a, s1) && contains_byte_string(a + s1.length, s2))
{
  lemma_substring_concat(s1, s2);
})

#endif