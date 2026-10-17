#!/bin/bash
cd "$(dirname "$0")"
export PYTHONPATH=../../pylib
until [ -f w14_conf.npz ]; do taskset -c 0 nice -n 10 python3 w14_conf.py >> w14_conf.log 2>&1 || sleep 5; done
