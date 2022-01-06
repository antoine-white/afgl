#include "map.h"

int main(int argc, char const *argv[])
{
    Map* m = init(10);
    Cell c = {.key = 1,.value = 121};
    _Bool b = add(m,c);
    printf("%d\n",b);
    b = add(m,c);
    printf("%d\n",b);
    int* rt = malloc(sizeof(int));
    b= get(m,1,rt);
    printf("%d => %d\n",b,*rt);

    return 0;
}
