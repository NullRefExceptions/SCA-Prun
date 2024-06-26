#!/usr/bin/env bash

args="$*"
export option="$args"

make netstat
cp trimmer/work_dir/netstat_opt3.bc .

echo "Statistics for program before specialization" >&2
opt -load ../libProfilerPass.so -Pprofiler < netstat.bc > /dev/null

make base
bin_size_before=$(ls -l netstat_base_stripped | awk '{print $5}')

echo "Binary Size ${bin_size_before}" >&2

echo "Statistics for program after specialization" >&2
opt -load ../libProfilerPass.so -Pprofiler < netstat_opt3.bc > /dev/null

bin_size_after=$(ls -l trimmer/work_dir/netstat_fin_stripped | awk '{print $5}')

echo "Binary Size ${bin_size_after}" >&2

test_status=$(make test_netstat | grep "Passed")

echo "Test: ${test_status}" >&2

