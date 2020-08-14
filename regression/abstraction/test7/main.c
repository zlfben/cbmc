#include <stdlib.h>
#include <assert.h>

#define MAX_LEN 100

void main(){
    char * a1;
    char * a2;
    int a1_len;
    int a2_len;
    int i = 0;
    int sum;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len < MAX_LEN);
    a1 = malloc(a1_len);
    a2 = malloc(a2_len);

    //We are assigning a variable that is not being abstracted --sum.
    while(i < a1_len){
        if(a1[i] == a2[i]) sum += a1[i];
        i++;
    }
    
    //This should lead to CBMC finding a counter example
    assert(sum < 0);
    return;
}