#! /bin/bash

if [ -e gen ]; then
    rm gen
fi 

if [ -e /tmp/smt ]; then
    rm -rf /tmp/smt
fi    

if [ -e main.c ]; then
    rm main.c
fi

cd generate_test_cases
g++ main.cpp -o gen
cd ..

for i in {0..7}
do
    cd generate_test_cases
    ./gen $i correct
    cd ..
    cp generate_test_cases/main.c main.c
    forest 
    forest -learn_model
done

for i in {0..7}
do
    cd generate_test_cases
    ./gen $i bad
    cd ..
    cp generate_test_cases/main.c main.c
    forest 
    forest -export_model
done

#forest -check_learned_model
forest -export_allsat
forest -execute_allsat
#forest -run_evaluation



