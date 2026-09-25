#!/bin/bash
cd /app/workspace/projects/lrx/aux
./wit_ecc 7 8 > wit_ecc_m7r8.log 2> wit_ecc_m7r8.err
./wit_ecc 7 9 > wit_ecc_m7r9.log 2> wit_ecc_m7r9.err
echo DONE > wit_ecc_78_79.done
