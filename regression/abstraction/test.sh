#!/bin/bash

# whether verify the program or not
CHECK=true

# paths to the benchmark repos
AWS_C_COMMON_PATH="/home/ubuntu/aws-c-common"

# executables
MAKE="make"
GOTO_INSTRUMENT="/home/ubuntu/cbmc/build/bin/goto-instrument"
CBMC="/home/ubuntu/cbmc/build/bin/cbmc"
CBMC_FLAGS="--unwind 4 
            --trace"
            # --bounds-check
            # --nondet-static 
            # --div-by-zero-check 
            # --float-overflow-check 
            # --nan-check 
            # --pointer-overflow-check 
            # --undefined-shift-check 
            # --signed-overflow-check 
            # --unsigned-overflow-check 

AWS_C_COMMON_TESTS=(
    "aws_array_eq"
)

cwd=$(pwd)
for test in ${AWS_C_COMMON_TESTS[@]}; do
    echo "===== $test ====="
    cd $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/
    # compile program into goto-programs
    $MAKE veryclean 2&>1
    $MAKE goto 2&>1
    echo "Goto programs built"
    cd $cwd
    # run goto-instrument to make abstracted goto-programs
    $GOTO_INSTRUMENT --use-abstraction $cwd/specs/$test.json \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness.goto \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto
    # print the goto-programs into txts
    rm $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.txt
    $GOTO_INSTRUMENT --show-goto-functions \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto \
        >> $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.txt
    # check the program
    if [ $CHECK = true ]; then
        $CBMC $CBMC_FLAGS $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto
    fi
done
