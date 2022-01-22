#include "map.h"


void init(Map* m , index_t capacity,Cell* storage )
{    
    m->capacity = capacity;
    m->size = 0;
    m->array = storage;
}

/*@

requires m->capacity >= m->size ;
requires m->capacity <= INT_MAX;
requires \valid(m);
requires \valid(m->array + (0 .. m->capacity-1));
behavior exists:
    assumes KeyExists(m,key);
    ensures \result == 1;
behavior no:
    assumes !KeyExists(m,key);
    ensures \result == 0;
complete behaviors ;
disjoint behaviors ;
*/
_Bool keyExists(Map* m, key_t key){
    /*@
      loop invariant 0 <= i < m->size;
      //loop invariant !KeyExistsIn(m, i, key);
      loop assigns i;
      loop variant m->size-i;
    */
    for (int i = 0; i < m->size; i++)
        if(m->array[i].key == key)
            return 1; 
    return 0;
}

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
_Bool exists(Map* m, key_t key)
{
    /*@
      loop invariant 0 <= i <= m->size;
      loop invariant \forall integer k; 0 <= k < i ==> ! KeyEquals(m->array[k],key);
      loop assigns i;
      loop variant m->size-i;
    */
    for( int i = 0; i < m->size; ++i){
        if(m->array[i].key == key){
            //@ assert KeyEquals(m->array[i], key);
            //@ assert KeyExists(m, key);
            return 1;
        }
    }
    //@ assert \forall integer k; 0 <= k < m->size ==> ! KeyEquals(m->array[k],key);

    return 0;
}


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
_Bool add(Map* m, Cell new_cell)
{
    if (m->size >= m->capacity)
        return 0;
    _Bool res = exists(m,new_cell.key);     
    if (res == 1) {
        //@ assert KeyExists(m, new_cell.key);
        return 0;
    }
    //@ assert \forall integer k; 0 <= k < m->size ==> ! KeyEquals(m->array[k],new_cell.key);
    m->array[m->size] = new_cell;
    // @ assert m->array[m->size] == new_cell;
    ++m->size;
    return 1;
        
}


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
const Cell* get(Map* m, key_t key)
{
    /*@
      loop invariant 0 <= i <= m->size;
      loop invariant \forall integer k; 0 <= k < i ==> ! KeyEquals(m->array[k],key);
      loop assigns i;
      loop variant m->size-i;
    */
    for( int i = 0; i < m->size; ++i){
        if(m->array[i].key == key){
            //@ assert KeyEquals(m->array[i], key);
            //@ assert KeyExists(m, key);
            return &(m->array[i]);
        }
    }
    //@ assert \forall integer k; 0 <= k < m->size ==> ! KeyEquals(m->array[k],key);
    return NULL;
}
