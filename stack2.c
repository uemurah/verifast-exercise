#include <stdlib.h>

struct stack_body {
  int value;
  struct stack_body* next;  
};

struct stack {
  struct stack_body* top;
};

//@inductive ints = ints_nil | ints_cons(int, ints);

/*@predicate nodes(struct stack_body *node, int count) =
    node == 0 ?
        count == 0
    :
        0 < count
        &*& node->next |-> ?next &*& node->value |-> ?value
        &*& malloc_block_stack_body(node) &*& nodes(next, count - 1);
        
predicate stack(struct stack *stack, int count) =
    stack->top |-> ?top &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(top, count);
@*/

/*@predicate lseg(struct stack_body *first, struct stack_body *last, int count) =
    first == last ?
        count == 0
    :
        0 < count &*& first != 0 &*&
        first->value |-> _ &*& first->next |-> ?next &*& 
        malloc_block_stack_body(first) &*&
        lseg(next, last, count - 1);
@*/  

/*@lemma void nodes_to_lseg_lemma(struct stack_body *first)
    requires nodes(first, ?count);
    ensures lseg(first, 0, count);
{
    open nodes(first, count);
    if (first != 0) {
        nodes_to_lseg_lemma(first->next);
    }
    close lseg(first, 0, count);
}            
@*/ 

//練習問題１２
/*@lemma void lseg_to_nodes_lemma(struct stack_body *first)
    requires lseg(first, 0, ?count);
    ensures nodes(first, count);
{
    open lseg(first, 0, count);
    if(first != 0) {
       lseg_to_nodes_lemma(first->next);
    }
    close nodes(first, count);   
}    
@*/

/*@
lemma void lseg_add_lemma(struct stack_body *first)
    requires
        lseg(first, ?last, ?count) &*& last != 0 &*& last->value |-> _ &*& last->next |-> ?next &*&
        malloc_block_stack_body(last) &*& lseg(next, 0, ?count0);
    ensures lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
    open lseg(first, last, count);
    if (first == last) {
        close lseg(next, next, 0);
    } else {
        lseg_add_lemma(first->next);
    }
    open lseg(next, 0, count0);
    close lseg(next, 0, count0);
    close lseg(first, next, count + 1);
}
@*/

/*@ lemma void lseg_union_lemma(struct stack_body *first)
    requires lseg(first, ?last, ?count) &*& lseg(last, 0, ?count0) &*& count0 >= 0;
    ensures lseg(first, 0, count + count0);
    {
    open lseg(first, last, count);
    if (first == last) {
       //lseg_union_lemma(last);
       } else {
         lseg_union_lemma(first->next);
         close lseg(first, 0, count + count0);
       }
    //close lseg(first, 0, count + count0); 
    }
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

int stack_get_count(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    struct stack_body *top = stack->top;
    //@ nodes_to_lseg_lemma(top);
    struct stack_body *n = top;
    int i = 0;
    //@ close lseg(top, top, 0);
    while (n != 0)
        //@ invariant lseg(top, n, i) &*& lseg(n, 0, count - i);
    {
        //@ open lseg(n, 0, count - i);
        n = n->next;
        i++;
        //@ lseg_add_lemma(top);
    }
    //@ open lseg(0, 0, _);
    // close lseg(0, 0, 0);
    // open lseg(0, 0, _);
    //@ lseg_to_nodes_lemma(top);
    //@ close stack(stack, count);
    return i;
}


//練習問題１３
void stack_push_all(struct stack *stack, struct stack *other)
    //@ requires stack(stack, ?count) &*& stack(other, ?count0);
    //@ ensures stack(stack, count0 + count);
{
    //@ open stack(other, count0);
    //@ open stack(stack, count);
    struct stack_body *top0 = other->top;
    free(other);
    struct stack_body *n = top0;
    if (n != 0) {
    	//@ nodes_to_lseg_lemma(n);
    	//@ open lseg(n, 0, count0);
    	//@ close lseg(top0, top0, 0);
        while (n->next != 0)
        /*@ invariant lseg(top0, n, ?k) &*& 
                      malloc_block_stack_body(n) &*& 
                      n->value |-> ?dummy &*& n->next |-> ?xx &*& 
                      lseg(xx, 0, count0 - (k + 1)) &*& n != 0;
        @*/              
        {
            n = n->next;
  	    //@ lseg_add_lemma(top0);
  	    //@ open lseg(xx, 0, count0 - (k + 1));
        }
        //@ open lseg(xx, 0, _);
        n->next = stack->top;
        //@ nodes_to_lseg_lemma(stack->top);
        stack->top = top0;
        //@ lseg_add_lemma(top0);
        //@ lseg_union_lemma(top0);
        //@ lseg_to_nodes_lemma(top0);
    } else {
	//@ open nodes(top0, count0);
    }
    //@ close stack(stack, count + count0);
}

//練習問題１４工事中
/*void stack_reverse(struct stack *s)
     //@ requires
     //@ ensures
{
     struct stack_body *n = s->top; 
     struct stack_body *p = 0;
     struct stack_body *q;
     while (n->next != 0) 
     {
        q = n->next;
        n->next = p;
        p = n;
        n = q;
     }
     n->next = p;
     s->top = n;
}*/

//練習問題15
typedef bool int_predicate(int x);
    //@ requires true;
    //@ ensures true;
    
struct stack_body *nodes_filter(struct stack_body *n, int_predicate *p)
    //@ requires nodes(n, _) &*& is_int_predicate(p) == true;
    //@ ensures nodes(result, _);
{
    if (n == 0) {
        return 0;
    } else {
        //@ open nodes(n, _);
        bool keep = p(n->value);
        if (keep) {
            struct stack_body *next = nodes_filter(n->next, p);
            //@ open nodes(next, ?count);
            //@ close nodes(next, count);
            n->next = next;
            //@ close nodes(n, count + 1);
            return n;
        } else {
            struct stack_body *next = n->next;
            free(n);
            struct stack_body *result = nodes_filter(next, p);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
    //@ requires stack(stack, _) &*& is_int_predicate(p) == true;
    //@ ensures stack(stack, _);
{
    //@ open stack(stack, _);
    struct stack_body *head = nodes_filter(stack->head, p);
    //@ assert nodes(head, ?count);
    stack->head = head;
    //@ open nodes(head, count);
    //@ close nodes(head, count);
    //@ close stack(stack, count);
}

bool neq_20(int x) //@ : int_predicate
    //@ requires true;
    //@ ensures true;
{
    return x != 20;
}



int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    stack_push(s, 10);
    stack_push(s, 20);
    stack_push(s, 30);
    //stack_pop(s);
    //stack_pop(s);
    stack_filter(s, neq_20);
    stack_dispose(s);
    return 0;
}
