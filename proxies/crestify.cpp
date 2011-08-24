
// Copyright (c) Mihhail Aizatulin (avatar@hot.ee).
// This file is distributed as part of csec-tools under a BSD license.
// See LICENSE file for copyright notice.

#include "common_internal.h"

#include "crest.h"
#include "interface.h"

#include <iostream>
#include <map>

// for exit()
#include <stdlib.h>

// for strlen()
#include <string.h>

////////////////////////////////////////////////////////
// Shared State
////////////////////////////////////////////////////////

int muted = 0;

/**
 * Set by CustomReturn()
 */
bool customReturn = false;

/**
 * The last heap ptr id used by memory allocation functions.
 */
int lastHeapPtr = 0;

////////////////////////////////////////////////////////
// Helpers, to be called only from uninstrumented code
////////////////////////////////////////////////////////

void Clear(int numargs)
{
  if(muted) return;

  for(int i = 0; i < numargs; i++)
    cout << "Clear" << endl;
}

void LoadHeapPtr(int id)
{
  cout << "LoadHeapPtr " << id << endl;
  cout << "LoadInt 1" << endl;
  cout << "SetPtrStep" << endl;
}

///////////////////////////////////////////
// CREST Functions
///////////////////////////////////////////


/**
 * The pointer to the function that is being called right now.
 * Used by Call() to detect when the function is invoked from non-instrumented code.
 */
EXTERN int main(int, char**);
funPtr calledFun = (funPtr)&main;

void __CrestInit()
{
  // load the argc, assume it is 2
  __CrestLoadInt(2);

  // construct argv with two parameters

  __CrestLoadCString("argv[0]_contents");
  __CrestLoadCString("argv[1]_contents");
  Append();
  __CrestLoadCString("argv[2]_contents");
  Append();
  __CrestLoadCString("argv[3]_contents");
  Append();
  __CrestLoadCString("argv[4]_contents");
  Append();
  __CrestLoadStackPtr("argv");
  __CrestLoadInt(sizeof(char*));
  __CrestSetPtrStep();
  __CrestStoreBuf();
  __CrestLoadStackPtr("argv");
  __CrestLoadInt(sizeof(char*));
  __CrestSetPtrStep();
  cout << "Hint argv" << endl;
}

void __CrestClear(__CREST_VALUE n)
{
  if(muted) return;

  Clear(n);
}

void __CrestInvoke(__CREST_FUN_PTR f)
{
  if(muted) return;

  f();
}

//void __CrestApply1(__CREST_OP op, __CREST_VALUE val)
//{
//  if(muted) return;
//
//  cout << "ApplyOp " << op << " " << 1 << endl;
//  cout << "ConcreteResult  " << val << endl;
//}
//
//void __CrestApply2(__CREST_OP op, __CREST_VALUE val)
//{
//  if(muted) return;
//
//  cout << "ApplyOp " << op << " " << 2 << endl;
//  cout << "ConcreteResult  " << val << endl;
//}

void __CrestApplyN(__CREST_OP op, __CREST_VALUE n)
{
  if(muted) return;

  cout << "ApplyN " << op << " " << n << endl;
}

void __CrestSimplify(__CREST_VALUE val)
{
  if(muted) return;

  cout << "ConcreteResult " << val << endl;
}

void __CrestNondet()
{
  if(muted) return;

  cout << "Nondet" << endl;
}

void __CrestMute()
{
  mute();
}

void __CrestUnmute()
{
  unmute();
}

void __CrestBranch(__CREST_BOOL cond)
{
  if(muted) return;

  cout << "Branch " << (bool) cond << endl;
}

void __CrestCall(__CREST_STR name, __CREST_FUN_PTR f)
{
  if(muted) return;

  cout << "Call " << name << endl;
}

void __CrestReturn(__CREST_BOOL is_void)
{
  if(muted) return;

  // if CustomReturn() has been called already, remove the automatically
  // generated value from the stack to let the custom value be returned
  if(customReturn)
  {
    if(!is_void) __CrestClear(1);
    customReturn = false;
  }

  cout << "Return" << endl;
}

void __CrestStore()
{
  if(muted) return;

  cout << "StoreMem " << endl;
}

void __CrestStoreBuf()
{
  if(muted) return;

  cout << "StoreBuf " << endl;
}


void __CrestLoadInt(__CREST_VALUE val)
{
  if(muted) return;

  cout << "LoadInt " << val << endl;
}

void __CrestLoadMem()
{
  if(muted) return;

  // Always uses the size of the pointer
  cout << "LoadMem" << endl;
}

void __CrestLoadCString(__CREST_STR val)
{
  if(muted) return;

  int len = strlen(val);

  // String constants are stored in the DATA memory segment, so we can just use
  // heap pointer semantics for them.
  cout << "LoadStr " << endl << buffer2string((const unsigned char *) val, len) << "00" << endl;
  cout << "LoadInt " << len << endl;
  LoadHeapPtr(++lastHeapPtr);
  cout << "StoreMem" << endl;
  cout << "LoadInt " << len << endl;
  LoadHeapPtr(lastHeapPtr);
}

void __CrestLoadString(__CREST_STR val)
{
  if(muted) return;

  // int len = strlen(val);
  cout << "LoadStr " << endl << val << endl;
}

void __CrestLoadTypeSize(__CREST_STR val)
{
  if(muted) return;

  cout << "LoadStr " << endl << val << endl;
  cout << "ApplyN SizeOf 1" << endl;
}

void __CrestLoadChar(__CREST_CHAR val)
{
  if(muted) return;

  cout << "LoadStr " << endl << buffer2string((const unsigned char *)(&val), 1) << endl;
}

void __CrestSetLen()
{
  if(muted) return;

  cout << "SetLen" << endl;
}

void __CrestSetPtrStep()
{
  if(muted) return;

  cout << "SetPtrStep" << endl;
}

void __CrestLoadStackPtr(__CREST_STR var)
{
  if(muted) return;

  cout << "LoadStackPtr " << var << endl;
}

void __CrestFieldOffset(__CREST_STR field)
{
  if(muted) return;

  cout << "FieldOffset " << field << endl;
}

void __CrestIndexOffset()
{
  if(muted) return;

  cout << "IndexOffset" << endl;
}

void __CrestLocation(__CREST_STR loc)
{
  if(muted) return;

  cout << "// " << loc;
  // if(muted) cout << " (muted)";
  cout << endl;
}

void __CrestDone()
{
  if(muted) return;

  cout << "Done" << endl;
}

///////////////////////////////////////////////////////
// Helpers, to be called only from instrumented code
///////////////////////////////////////////////////////

map<const void *, map<string, int> > int_attributes;


/**
 * It is important that mute() and unmute() have no parameters and return values.
 * Otherwise they would need to take special care of them when turning off the instrumentation.
 */
void mute()
{
  muted++;
}

void unmute()
{
  // don't go into negative
  // FIXME: in fact, it would be an error if unmute() is called on 0?
  if(muted) muted--;
}


void CustomReturn()
{
  if(muted) return;

  customReturn = true;
}

void LoadBuf(const unsigned char * buf, size_t len)
{
  if(muted) return;
  cout << "LoadBuf" << endl;
}

void LoadAll(const unsigned char * buf)
{
  if(muted) return;
  cout << "LoadAll" << endl;
}

void LoadAttr(const void * ctx, const char * attr)
{
  if(muted) return;

  // remove attr from stack, it's not symbolic
  Clear(1);
  cout << "CtxOffset " << attr << endl;
  cout << "LoadAll " << endl;
}

void LoadInt(int n)
{
  if(muted) return;

  // n is already on the stack, do nothing
}

void LoadStr(const char * str)
{
  if(muted) return;

  Clear(1);
  cout << "LoadStr " << endl << str << endl;
}

void Sym(const char * sym)
{
  if(muted) return;

  // Discard the sym parameter from symbolic stack
  Clear(1);
  cout << "ApplyAll " << sym << endl;
}

void SymN(const char * sym, int n)
{
  if(muted) return;

  // Discard the parameters from symbolic stack
  Clear(2);
  cout << "ApplyN " << sym << " " << n << endl;
}


void Dup()
{
  if(muted) return;

  cout << "Dup " << endl;
}

void Nondet()
{
  __CrestNondet();
}

void Done()
{
  __CrestDone();
}


void Event()
{
  if(muted) return;

  cout << "Event" << endl;
}

void Append()
{
  if(muted) return;

  cout << "Append" << endl;
}

void Hint(const char * hint)
{
  if(muted) return;

  Clear(1);

  if(string(hint) != "")
    cout << "Hint " << hint << endl;
}

void SetLen(size_t len)
{
  if(muted) return;

  cout << "SetLen" << endl;
}

void StoreBuf(const unsigned char * buf)
{
  if(muted) return;

  __CrestStoreBuf();
}

void StoreAll(const unsigned char * buf)
{
  if(muted) return;

  cout << "StoreAll" << endl;
}

void StoreAttr(const void * ctx, const char * attr)
{
  if(muted) return;

  // remove attr from stack
  Clear(1);
  cout << "CtxOffset " << attr << endl;
  cout << "StoreAll " << endl;
}

void CopyCtx(const void * to, const void * from)
{
  if(muted) return;

  cout << "CopyCtx" << endl;
}

void StoreRuntimeInt(const void * ctx, const char * attr, int n)
{
  // if(muted) return; (this is runtime, so no muting)

  Clear(3);
  int_attributes[ctx][string(attr)] = n;
}

int LoadRuntimeInt(const void * ctx, const char * attr)
{
  // if(muted) return; (this is runtime, so no muting)

  Clear(2);
  int n = int_attributes[ctx][string(attr)];
  __CrestLoadInt(n);
  return n;
}

void NewHeapPtr(size_t buflen)
{
  if(muted) return;

  LoadHeapPtr(++lastHeapPtr);
}
