
#include "stdio.h"
#include "stdlib.h"
/*@
    logic integer Capacity{L}(Map* s) = s->capacity;
    logic integer Size{L}(Map* s) = s->size
    logic value_type* Storage{L}(Map* s) = s->array;
*/

/*@
    predicate
        Empty{L}(Map* s) = Size(s) == 0;
    predicate
        Full{L}(Map* s) = Size(s) == Capacity(s);
*/


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
requires capacity: 0 < capacity;
assigns s->obj, s->capacity, s->size;
ensures valid: \valid(\return);
ensures capacity: Capacity(\return) == capacity;
//ensures invariant: Invariant(\return);
ensures empty: Empty(\return);
*/
Map* init(index_t capacity);
_Bool add(Map* m, Cell new_cell);
_Bool get(Map* m, key_t key,val_t *val);
