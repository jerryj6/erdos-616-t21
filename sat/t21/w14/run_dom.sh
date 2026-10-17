#!/bin/bash
cd "$(dirname "$0")"; export PYTHONPATH=../../pylib
until [ -f w14_red.npz ]; do taskset -c 0 nice -n 10 python3 w14_dom.py >> w14_dom.log 2>&1 || sleep 5; done
