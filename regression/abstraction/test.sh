#!/bin/bash

# paths to the benchmark repos
AWS_C_COMMON_PATH="/home/ubuntu/aws-c-common"
AWS_IOT_SDK_PATH="/home/ubuntu/aws-iot-device-sdk-embedded-C-tuttle"

# executables
MAKE="make"
GOTO_INSTRUMENT="goto-instrument"

AWS_C_COMMON_TESTS=(
    "aws_array_eq" 
    "aws_array_eq_c_str_ignore_case" 
    "aws_array_eq_ignore_case" 
    "aws_array_list_comparator_string" 
    "aws_array_list_front" 
    "aws_array_list_get_at" 
    "aws_array_list_pop_back" 
)

AWS_IOT_SDK_TEST="skip_string"

cwd=$(pwd)
for test in ${AWS_C_COMMON_TESTS[@]}; do
    echo "===== $test ====="
    cd $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/
    # compile program into goto-programs
    $MAKE goto 2&>1
    echo "Goto programs built"
    cd $cwd
    # run goto-instrument to make abstracted goto-programs
    $GOTO_INSTRUMENT --use-abstraction $cwd/$test.json \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness.goto \
        $AWS_C_COMMON_PATH/.cbmc-batch/jobs/$test/${test}_harness_abst.goto
done

echo "===== $AWS_IOT_SDK_TEST ====="
cd $AWS_IOT_SDK_PATH/cbmc/proofs/JsonParser/proofs
# compile program into goto-programs
$MAKE goto ENTRY=String 2&>1
cd $cwd
# run goto-instrument to make abstracted goto-programs
$GOTO_INSTRUMENT --use-abstraction $cwd/$AWS_IOT_SDK_TEST.json \
    $AWS_IOT_SDK_PATH/cbmc/proofs/JsonParser/proofs/String.goto \
    $AWS_IOT_SDK_PATH/cbmc/proofs/JsonParser/proofs/String_abst.goto
