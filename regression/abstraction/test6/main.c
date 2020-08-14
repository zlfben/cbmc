#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

#define MAX_LEN 100

// Copies entries from a1 to a2 array.
int foo(char* a1, int a1_len, char* a2, int a2_len){
    bool res = true;
    if(a1_len == a2_len){
        for(int i; i < a1_len; i++){
            //assign a1 to a2.
            a2[i] = a1[i] + 1;
        }
        return 1;
    }
    else {
       int len = (a1_len < a2_len)?a1_len:a2_len;
        for(int i =0; i<len; i++){
            a2[i] = a1[i];
        }
        return 0;
    }

}


void main(){
    const char * a1;
    const char * a2;
    int a1_len;
    int a2_len;
    //CBMC will choose i non-deterministically
    int i;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len <= a1_len);
    __CPROVER_assume(i < a2_len);

    a1 = malloc(a1_len);
    a2 = malloc(a2_len);

    if(foo(a1, a1_len, a2, a2_len)) assert(a1[i] == a2[i]-1);
    else assert(a1[i] == a2[i]);
    return;
}