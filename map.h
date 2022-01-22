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
///
/// initialise la map m
/// 
void init(Map* m , index_t capacity,Cell* storage );

/*@
requires m->capacity >= m->size;
requires m->capacity > 0;
requires m->capacity <= INT_MAX;
requires \valid(m);
requires \valid(m->array + (0 .. m->capacity-1));
behavior full:
    assumes Full(m);
    assigns \nothing;
    ensures m->size == \at(m->size,Pre);
    ensures \result == 0;
behavior exits:
    assumes !Full(m) && KeyExists(m,new_cell.key);
    assigns \nothing;
    ensures \result == 0;
behavior ok:
    assumes !Full(m) && !KeyExists(m,new_cell.key);
    assigns m->size , m->array[m->size];
    ensures \result == 1;
complete behaviors ;
disjoint behaviors ;
*/
///
/// Retourne 1 si la cellule a bien ete ajoutee dans la map m sinon retourne 0
/// 
_Bool add(Map* m, Cell new_cell);


/*@
requires \valid_read(m);
requires m->size < INT_MAX;
requires \valid_read(m->array + (0 .. m->size-1));
assigns \nothing;

behavior empty_array:
    assumes m->size <= 0;
    assigns \nothing;
    ensures \result == NULL;
behavior exist:
    assumes m->size > 0;
    assumes KeyExists(m, key);
    assigns \nothing;
    ensures KeyEquals(*\result,key);
behavior not_exist:
    assumes m->size > 0;
    assumes !KeyExists(m, key);
    assigns \nothing;
    ensures \result == NULL;

complete behaviors ;
disjoint behaviors ;
*/
///
/// Retourne la cellule correspondant à key dans la map m sinon retourne NULL
/// 
const Cell* get(Map* m, key_t key);

/*@
requires \valid_read(m);
requires m->size < INT_MAX;
requires \valid_read(m->array + (0 .. m->size-1));
assigns \nothing;

behavior empty_array:
    assumes m->size <= 0;
    assigns \nothing;
    ensures \result == 0;
behavior exist:
    assumes m->size > 0;
    assumes KeyExists(m, key);
    assigns \nothing;
    ensures \result == 1;
behavior not_exist:
    assumes m->size > 0;
    assumes !KeyExists(m, key);
    assigns \nothing;
    ensures \result == 0;

complete behaviors ;
disjoint behaviors ;
*/
///
/// Retourne 1 si la cle existe sinon 0
/// 
_Bool exists(Map* m, key_t key);
















