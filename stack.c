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
    node == 0 ?
    	values == ints_nil
     :
    	values == ints_cons(?value, ?values0)
    	&*& node->next |-> ?next &*& node->value |-> value
    	&*& malloc_block_stack_body(node) &*& nodes(next, values0);
    
predicate stack(struct stack *stack, ints values) =
    stack->top |-> ?top &*& malloc_block_stack(stack) &*&
    nodes(top, values);
@*/

/*@fixpoint int ints_head(ints values) {
    switch (values) {
        case ints_nil: return 0;
        case ints_cons(value, values0): return value;
    }
}

fixpoint ints ints_tail(ints values) {
    switch (values) {
        case ints_nil: return ints_nil;
        case ints_cons(value, values0): return values0;
    }
}@*/

/*@
fixpoint int ints_sum(ints values){
    switch (values){
    case ints_nil: return 0;
    case ints_cons(value, values0): return value + ints_sum(values0);
    }
}@*/ 

/*@predicate lseg(struct stack_body *first, struct stack_body *last, int count) =
    first == last ?
        count == 0
    :
        0 < count &*& first != 0 &*&
        first->value |-> _ &*& first->next |-> ?next &*& 
        malloc_block_stack_body(first) &*&
        lseg(next, last, count - 1);      
@*/

/*@
fixpoint ints ints_append(ints values, ints values1){
   switch (values){
       case ints_nil: return values1;
       case ints_cons(value, values0): return ints_cons(value, ints_append(values0, values1));
   }
}
@*/

//reverse未完成
/*@
fixpoint ints ints_reverse_aux(ints values, ints rev){
   switch (values){
       case ints_nil: return rev;
       case ints_cons(value, values0): return ints_reverse_aux(values0, ints_cons(value, rev));
   }
}

/*fixpoint ints ints_reverse(ints values){
   return ints_reverse_aux(values, ints_nil);
} */   

fixpoint ints ints_reverse(ints values){
    switch (values){
        case ints_nil: return ints_nil;
        case ints_cons(value, values0): return ints_append(ints_reverse(values0), ints_cons(value, ints_nil));
    }         
}
@*/ 



/*@
lemma void ints_append_nil(ints values)
    requires true;
    ensures ints_append(values, ints_nil) == values;
{
    switch (values){
        case ints_nil:
        case ints_cons(value, values0):
            ints_append_nil(values0);
    }
}

//lemma void ints_append_assoc(int value, ints values1tail, ints rev)
//    requires true;
//    ensures ints_append(ints_reverse(ints_cons(value, values1tail)), rev) == ints_append(ints_revese(values1tail), ints_cons(value, rev));
//{
//}

lemma void ints_append_assoc(ints values1, ints values2, ints values3)
    requires true;
    ensures ints_append(ints_append(values1, values2), values3) == ints_append(values1, ints_append(values2, values3));
{
   switch (values1){
       case ints_nil:
       case ints_cons(value, values0): ints_append_assoc(values0, values2, values3);
   }
}           
                     
@*/              

struct stack* create_stack()
//@ requires true;
//@ ensures stack(result, ints_nil);
{
  struct stack* s = malloc(sizeof(struct stack));  
  if(s == 0) { abort(); }
  s->top = 0;
 
  //@ close nodes(s->top, ints_nil);
  //@ close stack(s, ints_nil);
  return s;
}

void stack_push(struct stack* s, int v)
//@ requires stack(s, ?values);
//@ ensures stack(s, ints_cons(v, values));
{
  //@ open stack(s, values);
  struct stack_body* b = malloc(sizeof(struct stack_body));
  if(b == 0) exit(-1);
  b->value = v;
  b->next = s->top;
  s->top = b;
  //@ close nodes(s->top, ints_cons(v, values));
  //@ close stack(s, ints_cons(v, values));
}

int stack_pop(struct stack* s)
//@ requires stack(s, ints_cons(?value, ?values0));
//@ ensures result == value &*& stack(s, values0);
{
  //@ open stack(s, ints_cons(value, values0));
  //@ open nodes(s->top, ints_cons(value, values0));
  struct stack_body* b = s->top;
  s->top = b->next;
  int c = b->value;
  free(b);
  //@ close stack(s, values0);
  return c;
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
/*void stack_dispose_helper(struct stack_body* s)
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
}*/


void stack_dispose(struct stack* s)
//@ requires stack(s, ?values0);
//@ ensures true;
{
  //@ open stack(s, values0);
  struct stack_body* b = s->top;
  while(b != 0) 
  //@ invariant nodes(b, _);
  {
    //@ open nodes(b, _);
    struct stack_body* next = b->next;
    free(b);
    b = next;
  }
 //@ open nodes(b, _);
//  stack_dispose_helper(s->top);
  free(s);
}

int nodes_get_sum(struct stack_body *s)
//@ requires nodes(s, ?values);
//@ ensures result == ints_sum(values) &*& nodes(s, values);
{
 //@ open nodes(s, values);
 int sum = 0;
  if(s != 0) {
     sum += s->value;
     int b = nodes_get_sum(s->next);
     sum += b;
     //free(s);
   }
   //@ close nodes(s, values);
   return sum; 
}

int stack_get_sum(struct stack *s)
//@ requires stack(s, ?values);
//@ ensures result == ints_sum(values) &*& stack(s, values);
{
  //@ open stack(s, values);
  int sum = nodes_get_sum(s->top);
  //@ close stack(s, values);
  return sum;
}

/*bool stack_is_empty(struct stack *stack)
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
}*/

/*void stack_popn(struct stack *s, int n)
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
}*/ 

//練習問題１４工事中
void stack_reverse(struct stack *s)
     //@ requires stack(s, ?values);
     //@ ensures stack(s, ints_reverse(values));
{
     //@ open stack(s, values);
     struct stack_body *n = s->top; 
     struct stack_body *p = 0;
     //@ close nodes(p, ints_nil);
    //@ ints_append_nil(ints_reverse(values));
     while (n != 0)
     /*@
        invariant
            nodes(p, ?rev) &*& nodes(n, ?values1) &*&
            ints_reverse(values) == ints_append(ints_reverse(values1), rev);
        @*/ 
     {
        //@ open nodes(n, values1);
        struct stack_body *tmp = n->next;
        //@ assert nodes(tmp, ?values1tail) &*& n->value |-> ?value;
        n->next = p;
        p = n;
        n = tmp;
        //@ close nodes(p, ints_cons(value, rev));
        //@ ints_append_assoc(ints_reverse(values1tail), ints_cons(value, ints_nil), rev);
     }
     //@ open nodes(n, _);
     s->top = p;
     //@ close stack(s, ints_reverse(values));
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    int sum = stack_get_sum(s);
    assert(sum == 30);
    int result1 = stack_pop(s);
    assert(result1 == 20);
    int result2 = stack_pop(s);
    assert(result2 == 10);
    stack_dispose(s);
    return 0;
}


