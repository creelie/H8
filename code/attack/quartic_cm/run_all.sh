#!/bin/sh
# Track T1: run every exact check; logs next to the scripts.
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
for s in t1_generic t1_T t1_loci t1_annihilator t1_lowerbound t1_fullflat t1_shapes_explore; do
  echo "=== $s ==="; python3 -B $s.py > $s.log 2>&1; tail -2 $s.log
done
