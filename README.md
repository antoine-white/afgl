# AFGL

Antoine Blanco, Adrien Mevelec, Mehdi Ziar 

Implémentation et preuve d'un "ensemble fini" (Java Map) avec frama-c

## Liste des methodes 

* ### init
  **initialise la map m**
```c
void init(Map* m , index_t capacity,Cell* storage);
```
* ### add
  **Retourne 1 si la cellule a bien ete ajoutee dans la map m sinon retourne 0**
```c
_Bool add(Map* m, Cell new_cell);
```
* ### exists
  **Retourne 1 si la cle existe sinon 0L**
```c
_Bool exists(Map* m, key_t key);
```

* ### get
  **Retourne la cellule correspondant à key dans la map m sinon retourne NULL**
```c
const Cell* get(Map* m, key_t key);
```


## compiler / lancer programme
```sh
$ gcc *.c -o a.exe
$ ./a.exe
```
