#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

#define MAX_LEN 100

bool search(char* a, int a_len, char key){
    bool res = false;
    for(int i =0; i < a_len; i++){
        if(a[i] == key) res = true;
    }
    return res;
}

bool copy_and_search(char * a1, char* a2, char a2_len, char key){
    a1 = a2;
    return(search(a1, a2_len, key));

}

bool main(){
    const char * a1;
    const char * a2;
    const char * a3;
    int a1_len;
    int a2_len;
    //Some char
    char key = 'a';
    //CBMC will choose i non-deterministically
    int i;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len <= a1_len);
    __CPROVER_assume(i < a2_len);

    a2 = malloc(a2_len);

    //assignment of the full array. 
    //a2's spec has to be copied over for a1 as well.    
    bool res = copy_and_search(a1, a2, a2_len, key);
    return res;

   
}