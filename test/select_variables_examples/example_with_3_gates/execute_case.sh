#! /bin/bash


rm -rf /tmp/smt
rm gen

cd generate_test_cases
g++ main.cpp -o gen
cd ..
cp  generate_test_cases/gen gen

for i in {0..7}
do
    echo $(pwd)
    ./gen $i
    forest 
    forest -export_model
done

forest -export_allsat
forest -execute_allsat
forest -run_evaluation

