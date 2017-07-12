 #include <stdlib.h>

struct stack_body {
  int value;
  struct stack_body* next;  
};

struct stack {
  struct stack_body* top;
};

//@inductive ints = ints_nil | ints_cons(int, ints);

/*@predicate nodes(struct stack_body *node, ints values) =
    switch (values) {
        case ints_nil: return node == 0;
        case ints_cons(value, values0):
         return node->next |-> ?next &*& node->value |-> value
        &*& malloc_block_stack_body(node) &*& nodes(next, values0);
        };

predicate stack(struct stack *stack, ints values) =
    stack->top |-> ?top &*& malloc_block_stack(stack) &*&
nodes(top, values);
@*/

struct stack* create_stack()
//@ requires true;
//@ ensures stack(result, 0);
{
  struct stack* s = malloc(sizeof(struct stack));  
  if(s == 0) { abort(); }
  s->top = 0;
 
  //@ close nodes(s->top, 0);
  //@ close stack(s, 0);
  return s;
}

void stack_push(struct stack* s, int v)
//@ requires stack(s, ?count);
//@ ensures stack(s, count + 1);
{
  //@ open stack(s, count);
  struct stack_body* b = malloc(sizeof(struct stack_body));
  if(b == 0) exit(-1);
  b->value = v;
  b->next = s->top;
  s->top = b;
  //@ close nodes(s->top, count + 1);
  //@ close stack(s, count + 1);
}

void stack_pop(struct stack* s)
//@ requires stack(s, ?count) &*& count > 0;
//@ ensures stack(s, count - 1);
{
  //@ open stack(s, count);
  //@ open nodes(s->top, count);
  struct stack_body* b = s->top;
  s->top = b->next;
  free(b);
  //@ close stack(s, count - 1);
}

/*
void stack_dispose_helper(struct stack_body* s)
  //@ requires nodes(s, ?count) &*& count > 0 ? count > 0 : count == 0;
  //@ ensures nodes(s, 0);
{

  //@ open nodes(s, count);
   if(s > 0) {
     struct stack_body* next = s->next;
     free(s);
     stack_dispose_helper(next);
     //@ close nodes(s, 0);
   }
   else{
   return;
   }
   //@ close nodes(s, count);
}
*/
void stack_dispose_helper(struct stack_body* s)
  //@ requires nodes(s, ?count);
  //@ ensures true;
{

  //@ open nodes(s, count);
   if(s != 0) {
     stack_dispose_helper(s->next);
     free(s);
   } else {
     return;
   }
}


void stack_dispose(struct stack* s)
//@ requires stack(s, _);
//@ ensures true;
{
  //@ open stack(s, _);
  struct stack_body* b = s->top;
  while(b != 0) 
  //@ invariant nodes(b, _);
  {
    //@ open nodes(b, _);
    struct stack_body* next = b->next;
    free(b);
    b = next;
  }
 //@ open nodes(0, _);
//  stack_dispose_helper(s->top);
  free(s);
}

int stack_get_sum_helper(struct stack_body *s)
//@ requires nodes(s, ?count);
//@ ensures true;
{
 //@ open nodes(s, count);
 int sum = 0;
  if(s != 0) {
     sum += s->value;
     stack_get_sum_helper(s->next);
     free(s);
   }
   return sum;
 // close nodes(s, count);  
}

int stack_get_sum(struct stack *s)
//@ requires stack(s, ?count);
//@ ensures true;
{
  //@ open stack(s, count);
  int sum = stack_get_sum_helper(s->top);
  free(s);
  return sum;
}

bool stack_is_empty(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == (count == 0);
{
    //@ open stack(stack, count);
    struct stack_body *top = stack->top;
    //@ open nodes(top, count);
    bool result = stack->top == 0;
    //@ close nodes(top, count);
    //@ close stack(stack, count);
    return result;
}

void stack_popn(struct stack *s, int n)
//@ requires stack(s, ?count) &*& n > 0 &*& count > n;
//@ ensures stack(s, count - n);
{
  // open stack(s, count);
  //open nodes(s->top, count);
  //int k = 0;
  int c = 0;
  while(c < n)
  //@ invariant stack(s, count - c) &*& c <= n; // count - c > 0;
  {
    stack_pop(s);
    c++;
    //k++;
  }
  // close stack(s, count - n);
} 

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_pop(s);
    stack_pop(s);
    stack_dispose(s);
    return 0;
}


