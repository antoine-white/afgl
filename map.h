#include "limits.h"
#include "stdio.h"
#include "stdlib.h"

typedef int key_t;
typedef int val_t;
typedef unsigned long int index_t;

struct Cell{
    key_t key;
    val_t value;
};

typedef struct Cell Cell;

struct Map
{
    Cell* array;
    index_t capacity;
    index_t size;
};

typedef struct Map Map;

/*@
logic integer Capacity{L}(Map* s) = s->capacity;
logic integer Size{L}(Map* s) = s->size;
*/

/*@
    predicate
        Empty{L}(Map* s) = Size(s) == 0;
    predicate
        Full{L}(Map* s) = Size(s) >= Capacity(s);
    predicate
        KeyEquals{L}(Cell c,key_t key) = c.key == key;
    predicate
        KeyExists{L}(Map* s,key_t key) = \exists integer indice ; 0 <= indice < Size(s) && KeyEquals(s->array[indice],key);
    predicate
        KeyExistsIn{L}(Map* s,int i,key_t key) = \exists integer indice ; 0 <= indice <= i < Size(s) && KeyEquals(s->array[indice],key);
*/

/*@
requires \valid(m);
requires capacity > 0;
requires \valid(storage+ (0 .. capacity-1));
requires \separated(m, storage + (0..capacity-1));
assigns m->size,m->array,m->capacity;
ensures Empty(m);
ensures Capacity(m) == capacity;
ensures m->array == storage;
*/
void init(Map* m , index_t capacity,Cell* storage );


_Bool add(Map* m, Cell new_cell);

const Cell* get(Map* m, key_t key);

















