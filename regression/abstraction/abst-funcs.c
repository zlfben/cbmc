#include <stdint.h>

int two_abs(int index, int a1, int a2) {
    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else return 4;
}

int three_abs(int index, int a1, int a2, int a3) {

    if (index < a1) return 0;
    else if (index == a1) return 1;
    else if (index > a1 && index < a2) return 2;
    else if (index == a2) return 3;
    else if (index > a2 && index < a3) return 4;
    else if (index == a3) return 5;
    else return 6;
}

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

int is_precise(int index, int a1, int a2){
    return(0);
}

int add_abs_to_conc(int abs_ind, int concrete_ind){
    return(0);
}

int sub_conc_from_abs(int abs_ind, int concrete_ind){
    return(0);
}

int concretize(int abs_ind){
    return(0);
}
