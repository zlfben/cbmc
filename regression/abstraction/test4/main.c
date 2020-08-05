#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>

#define MAX_LEN 100

bool foo(char* a1, int a1_len, char* a2, int a2_len){
    bool res = true;
    if(a1_len == a2_len){
        for(int i; i < a1_len; i++){
            if(a2[i] != a1[i] + 1) res &= false;
        }
        return res;
    }
    else {
       return false;
    }

}

bool bar(char * a1, int a1_len, char * a2, int a2_len, int i) {
    int k = i-1;
    assert(a1_len == a2_len);
    if (k > 0) {
        if(a2[i] == a1[i] + 1) return true;
        else return false; 
    }
    else return true;
}


void main(){
    const char * a1;
    const char * a2;
    int a1_len;
    int a2_len;
    int i;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len < MAX_LEN);
    a1 = malloc(a1_len);
    a2 = malloc(a2_len);

    if(foo(a1, a1_len, a2, a2_len)) {
        assert(bar(a1, a1_len, a2, a2_len, i));
    }
    else assert(true);
    return;
}