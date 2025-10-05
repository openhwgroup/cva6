// See LICENSE for license details.

//**************************************************************************
// Towers of Hanoi benchmark
//--------------------------------------------------------------------------
//
// Towers of Hanoi is a classic puzzle problem. The game consists of
// three pegs and a set of discs. Each disc is a different size, and
// initially all of the discs are on the left most peg with the smallest
// disc on top and the largest disc on the bottom. The goal is to move all
// of the discs onto the right most peg. The catch is that you are only
// allowed to move one disc at a time and you can never place a larger
// disc on top of a smaller disc.
//
// This implementation starts with NUM_DISC discs and uses a recursive
// algorithm to sovel the puzzle.

#include "util.h"


#define NUM_COUNTERS 2
static uintptr_t counters[NUM_COUNTERS];
static char* counter_names[NUM_COUNTERS];


void setStats(int enable)
{
  int i = 0;
#define READ_CTR(name) do { \
    while (i >= NUM_COUNTERS) ; \
    uintptr_t csr = read_csr(name); \
    if (!enable) { csr -= counters[i]; counter_names[i] = #name; } \
    counters[i++] = csr; \
  } while (0)

  READ_CTR(mcycle);
  READ_CTR(minstret);

#undef READ_CTR
}

// This is the number of discs in the puzzle.

#define NUM_DISCS  7

//--------------------------------------------------------------------------
// List data structure and functions

struct Node
{
  int val;
  struct Node* next;
};

struct List
{
  int size;
  struct Node* head;
};

struct List g_nodeFreeList;
struct Node g_nodePool[NUM_DISCS];

int list_getSize( struct List* list )
{
  return list->size;
}

void list_init( struct List* list )
{
  list->size = 0;
  list->head = 0;
}

void list_push( struct List* list, int val )
{
  struct Node* newNode;

  // Pop the next free node off the free list
  newNode = g_nodeFreeList.head;
  g_nodeFreeList.head = g_nodeFreeList.head->next;

  // Push the new node onto the given list
  newNode->next = list->head;
  list->head = newNode;

  // Assign the value
  list->head->val = val;

  // Increment size
  list->size++;

}

int list_pop( struct List* list )
{
  struct Node* freedNode;
  int val;

  // Get the value from the->head of given list
  val = list->head->val;

  // Pop the head node off the given list
  freedNode = list->head;
  list->head = list->head->next;

  // Push the freed node onto the free list
  freedNode->next = g_nodeFreeList.head;
  g_nodeFreeList.head = freedNode;

  // Decrement size
  list->size--;

  return val;
}

void list_clear( struct List* list )
{
  while ( list_getSize(list) > 0 )
    list_pop(list);
}

//--------------------------------------------------------------------------
// Tower data structure and functions

struct Towers
{
  int numDiscs;
  int numMoves;
  struct List pegA;
  struct List pegB;
  struct List pegC;
};

void towers_init( struct Towers* this, int n )
{
  int i;

  this->numDiscs = n;
  this->numMoves = 0;

  list_init( &(this->pegA) );
  list_init( &(this->pegB) );
  list_init( &(this->pegC) );

  for ( i = 0; i < n; i++ )
    list_push( &(this->pegA), n-i );

}

void towers_clear( struct Towers* this )
{

  list_clear( &(this->pegA) );
  list_clear( &(this->pegB) );
  list_clear( &(this->pegC) );

  towers_init( this, this->numDiscs );

}

void towers_solve_h( struct Towers* this, int n,
                     struct List* startPeg,
                     struct List* tempPeg,
                     struct List* destPeg )
{
  int val;

  if ( n == 1 ) {
    val = list_pop(startPeg);
    list_push(destPeg,val);
    this->numMoves++;
  }
  else {
    towers_solve_h( this, n-1, startPeg, destPeg,  tempPeg );
    towers_solve_h( this, 1,   startPeg, tempPeg,  destPeg );
    towers_solve_h( this, n-1, tempPeg,  startPeg, destPeg );
  }

}

void towers_solve( struct Towers* this )
{
  towers_solve_h( this, this->numDiscs, &(this->pegA), &(this->pegB), &(this->pegC) );
}

int towers_verify( struct Towers* this )
{
  struct Node* ptr;
  int numDiscs = 0;

  if ( list_getSize(&this->pegA) != 0 ) {
    return 2;
  }

  if ( list_getSize(&this->pegB) != 0 ) {
    return 3;
  }

  if ( list_getSize(&this->pegC) != this->numDiscs ) {
    return 4;
  }

  for ( ptr = this->pegC.head; ptr != 0; ptr = ptr->next ) {
    numDiscs++;
    if ( ptr->val != numDiscs ) {
      return 5;
    }
  }

  if ( this->numMoves != ((1 << this->numDiscs) - 1) ) {
    return 6;
  }

  return 0;
}

//--------------------------------------------------------------------------
// Main

int main( int argc, char* argv[] )
{
  struct Towers towers;
  int i;

  // Initialize free list

  list_init( &g_nodeFreeList );
  g_nodeFreeList.head = &(g_nodePool[0]);
  g_nodeFreeList.size = NUM_DISCS;
  g_nodePool[NUM_DISCS-1].next = 0;
  g_nodePool[NUM_DISCS-1].val = 99;
  for ( i = 0; i < (NUM_DISCS-1); i++ ) {
    g_nodePool[i].next = &(g_nodePool[i+1]);
    g_nodePool[i].val = i;
  }

  towers_init( &towers, NUM_DISCS );

  // If needed we preallocate everything in the caches

#if PREALLOCATE
  towers_solve( &towers );
#endif

  // Solve it

  towers_clear( &towers );
  setStats(1);
  towers_solve( &towers );
  setStats(0);

  // Check the results
  return towers_verify( &towers );
}

