#include <stdint.h>
#include <assert.h>
#include <stddef.h>

//Some helper functions. 

//nndt_bool, nndt_int, nndt_sizet are available in CBMC.

size_t nndt_int(){
    size_t i;
    return(i);
}

size_t nndt_bool(){
    size_t i;
    return(i % 2);
}


size_t nndt_under(size_t bound){
    size_t nd;
    // Mod is an expensive operation. We need to get rid of this.
    //return(nd%bound);
    __CPROVER_assume(nd < bound);
    return(nd);
}

size_t nndt_between(size_t l, size_t u){
    size_t diff = u - l;
    size_t nd = nndt_under(diff);
    if (nd == 0) return(l+1);
    else return(nd + l);
}

size_t nndt_above(size_t bound){
    size_t nd = nndt_int();
    __CPROVER_assume(nd < bound);
    return(nd);
}

//For one index: *c*
// covers c*, +c*
size_t one_abs(size_t index, size_t a1){
    if(index < a1) return(0);
    else if(index == a1) return(1);
    else return(2);
}


size_t is_precise_1(size_t abs_ind, size_t a1){
    return(abs_ind == 1);
}

size_t is_abstract_1(size_t abs_ind, size_t a1){
    return(abs_ind != 1);
}

size_t concretize_1(size_t abs_ind, size_t a1){
    assert(abs_ind >= 0);
    assert(a1 >= 0);
    if(abs_ind < 1) {
        if (a1 == 0) 
        {
            assert(0);
            return(0);
        }
        else return(nndt_under(a1));
    }
    else if (abs_ind == 1) return(a1);
    else return(nndt_above(a1));
}

// Add a number to an abs_ind
size_t add_abs_to_conc_1(size_t abs_ind, size_t num, size_t a1){
    if (num == 1){
        if(abs_ind == 0) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind + 1);
        }
        //abs_ind = 1 or 2
        else return(2);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        size_t conc = concretize_1(abs_ind, a1);
        return(one_abs(conc+num, a1));
    }

}

size_t sub_conc_from_abs_1(size_t abs_ind, size_t num, size_t a1){
    if (num == 1){
        if(abs_ind == 2) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind - 1);
        }
        //abs_ind = 1 0r 0
        else return(0);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        size_t conc = concretize_1(abs_ind, a1);
        assert(conc>=num);
        return(one_abs(conc-num, a1));
    }
}



// For two indices

//Get the abstraction of an index for shape *c*c*.
//Cases +c+c*, c+c*, +cc*, c+c*, cc+ can all be 
//handled by the same function as long as we are careful with concretization, increment and other funcs.
//If model checking time is affected then we can split into finer cases.
int two_abs(int index, int a1, int a2) {
    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else return 4;
}


//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*
int concretize_2(int abs_ind, int a1, int a2) {
    assert(abs_ind >= 0);
    assert(a1 >= 0);
    assert(a2 > a1);
    if (abs_ind < 1) {
        if (a1 == 0)
        {
            //throw an exception here?
            assert(0 != 0);
            return(-1);
        }
        else return(nndt_under(a1));
    }
    else if (abs_ind == 1) return(a1);
    else if (abs_ind == 2){
        if (a1+1 == a2 ) {
            //throw an exception here? 
            assert(0 != 0); 
            return(-1);
        }
        else return(nndt_between(a1, a2));
    }
    else if (abs_ind == 3) return(a2);
    else return(nndt_above(a2));
}

int is_precise_2(int abs_ind){
    if (abs_ind == 1 || abs_ind == 3) return(1);
    else return(0);
}

int is_abstract_2(int abs_ind){
    int pre = is_precise_2(abs_ind);
    return(1-pre);
}

// Add a number to an abs_ind
int add_abs_to_conc_2(int abs_ind, int num, int a1, int a2){
    if (num == 1){
        if(abs_ind == 0 || abs_ind == 2) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind + 1);
        }
        else if (abs_ind == 1) {
            // case *cc*
            if (a2 == a1+1) return(3);
            else return(2);
        }
        //abs_ind = 3 or 4
        else return(4);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        int conc = concretize_2(abs_ind, a1, a2);
        return(two_abs(conc+num, a1, a2));
    }

}

int sub_conc_from_abs_2(int abs_ind, int num, int a1, int a2){
    if (num == 1){
        if(abs_ind == 4 || abs_ind == 2) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind - 1);
        }
        else if (abs_ind == 3) {
            if (a1 == a2) return(1);
            else return(2);
        }
        //abs_ind = 1 0r 0
        else return(0);
    }
    else {
        assert(num >= 2);
        //This might be extremely inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        int conc = concretize_2(abs_ind, a1, a2);
        return(two_abs(conc-num, a1, a2));
    }
}

// Three indices: *c*c*c. Not used currently.
int three_abs(int index, int a1, int a2, int a3) {

    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else if (index > a2 && index < a3) return 4;
    else if (index == a3) return 5;
    else return 6;
}

//Get the abstraction of an index for shape *cc*cc*.
//Cases covered: +cc+cc*, cc+cc*, +cccc*, cc+cc*, cccc* 
//If model checking time is affected then we can split into finer cases.
int four_abs(int index, int a1, int a2, int a3, int a4) {
    if (a2 == a3) return three_abs(index, a1, a2, a4);
    else {
        if (index < a1) return 0;
        else if (index == a1) return 1;
        else if (index > a1 && index < a2) return 2;
        else if (index == a2) return 3;
        else if (index > a2 && index < a3) return 4;
        else if (index == a3) return 5;
        else if (index > a3 && index < a4) return 6;
        else if (index == a4) return 7;
        else return 8;
    }
}

//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*
int concretize_4(int abs_ind, int a1, int a2, int a3, int a4) {
    assert(abs_ind >= 0);
    assert(a1 >= 0);
    assert(a2 = a1+1);
    assert(a3 >= a2+1);
    assert(a4 >= a3+1);
    if (abs_ind < 1) {
        if (a1 == 0)
        {
            //throw an exception here?
            assert(0 != 0);
            return(-1);
        }
        else return(nndt_under(a1));
    }
    else if (abs_ind == 1) return(a1);
    else if (abs_ind == 2) return(a2);
    else if (abs_ind == 3){
        if (a2+1 == a3 ) {
            //throw an exception here? 
            assert(0 != 0); 
            return(-1);
        }
        else return(nndt_between(a2, a3));
    }
    else if (abs_ind == 4) return(a3);
    else if (abs_ind == 5) return(a4);
    else return(nndt_above(a4));
}

int is_precise_4(int abs_ind){
    if (abs_ind == 1 || abs_ind == 2 || abs_ind == 4 || abs_ind == 5) return(1);
    else return(0);
}

int is_abstract_4(int abs_ind){
    if(!is_precise_4(abs_ind)) return(1);
    else return(0);
}

// Add a number to an abs_ind
int add_abs_to_conc_4(int abs_ind, int num, int a1, int a2, int a3, int a4){
    if (num == 1){
        if(abs_ind == 0 || abs_ind == 3) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind + 1);
        }
        else if (abs_ind == 1) return(2);
        else if (abs_ind == 2) {
            // case *cccc*
            if (a3 == a2+1) return(4);
            else return(3);
        }
        else if(abs_ind == 4) return(5);
        //abs_ind = 5 or 6
        else return(6);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        int conc = concretize_4(abs_ind, a1, a2,a3,a4);
        return(four_abs(conc+num,a1,a2,a3,a4));
    }

}
// Shape: *cc*cc* with abs indices 0 3 6 and precise indices 1,2 and 4,5
int sub_conc_from_abs_4(int abs_ind, int num, int a1, int a2, int a3, int a4){
    if (num == 1){
        if(abs_ind == 6 || abs_ind == 3) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind - 1);
        }
        else if (abs_ind == 5 || abs_ind == 2 || abs_ind == 1) return(abs_ind-1);
        else if (abs_ind == 4) {
            if (a3 == a2+1) return(2);
            else return(3);
        }
        //abs_ind = 0
        else return(0);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        int conc = concretize_4(abs_ind, a1, a2, a3, a4);
        return(four_abs(conc-num,a1,a2,a3,a4));
    }
}



