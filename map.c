#include "map.h"


void init(Map* m , index_t capacity,Cell* storage )
{    
    m->capacity = capacity;
    m->size = 0;
    m->array = storage;
}

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
