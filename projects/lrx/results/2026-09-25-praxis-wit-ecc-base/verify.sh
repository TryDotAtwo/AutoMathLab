#!/bin/bash
gcc -O2 -o wit_ecc wit_ecc.c || exit 1
./wit_ecc 7 8
