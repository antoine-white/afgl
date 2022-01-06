#include "map.h"

Map* init(index_t capacity)
{
    Map *m = (Map *) malloc(sizeof(Map));
    m->capacity = capacity;
    m->size = 0;
    m->array = (Cell *) malloc(sizeof(Cell) * capacity);
    return m;
}

// TODO : may be latter check if it exists and change the value 
_Bool add(Map* m, Cell new_cell)
{
    if (m->size == m->capacity)
        return 0;
    for (int i = m->size; i-->0;)
        if(m->array[i].key == new_cell.key)
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