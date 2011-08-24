/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

extern void * stackguard_get_ra();
extern void stackguard_set_ra(void *new_ra);
/* You must provide an implementation for functions that get and set the
 * return address. Such code is unfortunately architecture specific.
 */
struct stackguard_stack {
  void * data;
  struct stackguard_stack * next;
} * stackguard_stack;

void stackguard_push(void *ra) {
  void * old = stackguard_stack;
  stackguard_stack = (struct stackguard_stack *)
    malloc(sizeof(stackguard_stack));
  stackguard_stack->data = ra;
  stackguard_stack->next = old;
}

void * stackguard_pop() {
  void * ret = stackguard_stack->data;
  void * next = stackguard_stack->next;
  free(stackguard_stack);
  stackguard_stack->next = next;
  return ret;
}
#line 3 "cilcode.tmp/ex24.c"
extern int ( /* missing proto */  scanf)() ;
#line 1 "cilcode.tmp/ex24.c"
int dangerous(void) 
{ char array[10] ;
  void *return_address ;

  {
  return_address = (void *)stackguard_get_ra();
  stackguard_push(return_address);
#line 3
  scanf("%s", array);
  {
  return_address = (void *)stackguard_pop();
  stackguard_set_ra(return_address);
#line 4
  return (0);
  }
}
}
#line 6 "cilcode.tmp/ex24.c"
int main(void) 
{ int tmp ;

  {
#line 7
  tmp = dangerous();
#line 7
  return (tmp);
}
}