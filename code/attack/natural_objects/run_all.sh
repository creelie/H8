#!/bin/sh
# Track T4, round 12: all exact / mod-p computations.  Logs in logs/.
set -e
cd "$(dirname "$0")"
mkdir -p logs
export PYTHONDONTWRITEBYTECODE=1
for d in 1 2 3; do python3 -B t4_basic.py $d > logs/basic_d$d.log; done
for d in 1 2 3; do python3 -B t4_lg.py $d > logs/lg_d$d.log; done
for nd in "2 1" "2 2" "3 1" "3 2" "4 1" "4 2"; do set -- $nd; python3 -B t4_lg_n.py $1 $2 > logs/lg_n$1_d$2.log; done
for d in 1 2; do python3 -B t4_contr.py $d > logs/contr_d$d.log; done
python3 -B t4_example.py 1 small > logs/example_d1_small.log
python3 -B t4_example.py 1 > logs/example_d1_ref.log
python3 -B t4_example.py 2 > logs/example_d2_ref.log
for d in 1 2; do python3 -B t4_minimal.py $d > logs/minimal_d$d.log; done
python3 -B t4_subtori_search.py 1 3 > logs/subtori_search_d1.log
for dH in "1 10" "2 8" "3 8"; do set -- $dH; python3 -B t4_sublattice.py $1 $2 > logs/sublattice_d$1.log; done
python3 -B t4_n2_cross.py > logs/n2_cross.log
echo done
