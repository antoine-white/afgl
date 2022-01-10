#include "map.h"

Map* init(index_t capacity)
{
    Map *m = (Map *) malloc(sizeof(Map));
    m->capacity = capacity;
    m->size = 0;
    m->array = (Cell *) malloc(sizeof(Cell) * capacity);
    return m;
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
