#!/bin/bash
# usage: run_cert.sh r ; builds CNF+DRAT for root case r, then drat-trim
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
r=$1
[ -f w14_cert_$r.cnf ] || taskset -c 0 nice -n 10 python3 w14_cert.py $r >> w14_cert_$r.log 2>&1
[ -f w14_cert_$r.cnf ] && [ ! -f w14_cert_$r.trim ] && taskset -c 0 nice -n 10 timeout 3000 ../../tools/drat-trim w14_cert_$r.cnf w14_cert_$r.drat -t 2900 > w14_cert_$r.trim.tmp 2>&1; mv w14_cert_$r.trim.tmp w14_cert_$r.trim
sha256sum w14_cert_$r.cnf w14_cert_$r.drat >> w14_cert_$r.log
