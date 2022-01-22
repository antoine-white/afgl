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

_Bool add(Map* m, Cell new_cell)
{
    if (m->size == m->capacity)
        return 0;
    _Bool res = 1;
    /*@
    loop invariant 0 <= i <=  m->size ;
    //loop invariant \forall integer j ; 0 <= j < i ==> res ==  (m->array[j].key != new_cell.key) && res == 0 ;
    loop assigns i,res;
    loop variant m->size-i ;
    */
    for (int i = 0; i < m->size && res != 0; i++)
        if(m->array[i].key == new_cell.key)
            res =  0;   
    if (res == 0) 
        return 0;
    m->array[m->size] = new_cell;
    ++m->size;
    return 1;
        
}


_Bool get(Map* m, key_t key,val_t *val)
{
    _Bool found = 0;
    int i = m->size;
    while( i--> 0 || !found){
        if(m->array[i].key == key){
            found = 1;
            *val = m->array[i].value;
        }
    }
    return found;
}
