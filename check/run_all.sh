#!/bin/bash
# Runs the checks of Section 6 of the paper and the consistency checks, from the root of the repository:
#     bash check/run_all.sh python3 > run_all.log 2>&1
# PY must have python-flint. The 48 files of the certificate for S_6 and the 576 files of the certificate for S_7 are in
# the archive record (s6_certificate.tar.gz, s7_certificate.tar.gz); unpack them in certificate/ to check them.
# check_cover.py recomputes the checksum of every file it reads, so the coverage checks need the unpacked files.
# By default the script checks the coverage of the shipped logs logs/s6_shards and logs/s7_shards, which record full
# runs, and rechecks two files of each certificate. With "full" as second argument it checks every file of the unpacked
# certificates (NPROC in parallel, third argument, default 8; about 48 core-minutes for S_6 and a few core-hours for S_7)
# and runs the coverage checks on the fresh output.
PY=${1:-python3}; MODE=${2:-quick}; NP=${3:-8}
R=$(cd "$(dirname "$0")/.." && pwd)
W=$(mktemp -d "${TMPDIR:-/tmp}/bohr_controls.XXXXXX")
P3="20674053/62500000 3901457/1562500000 101990031/1000000000"
S6="$R/certificate/s6_certificate"; S7="$R/certificate/s7_certificate"
echo "== certificate for S_5 <= 2.187"
$PY -I "$R/check/check_sidon.py" "$R/certificate/s5_certificate.json" 2.187; echo "exit $?"
sharded() {   # k bound dir nfiles recheck...
  local k=$1 b=$2 d=$3 n=$4; shift 4
  if [ ! -d "$d" ]; then
    echo "(the $n files of the certificate for S_$k are not unpacked in certificate/s${k}_certificate; skipping its checks)"
    return
  fi
  if [ "$MODE" = full ]; then
    mkdir -p "$W/c$k"
    ls "$d"/sh*.json | xargs -P "$NP" -I{} sh -c "$PY -I '$R/check/check_shard.py' {} $b > '$W/c$k/'\$(basename {} .json).log 2>&1"
    echo "== certificate for S_$k <= $b: coverage of the $n fresh shard logs"
    $PY -I "$R/check/check_cover.py" "$d" "$W/c$k"/sh*.log; echo "exit $?"
  else
    echo "== certificate for S_$k <= $b: coverage of the $n shard logs in logs/s${k}_shards (a record of a full run)"
    $PY -I "$R/check/check_cover.py" "$d" "$R/logs/s${k}_shards"/sh*.log; echo "exit $?"
    for s in "$@"; do
      echo "== certificate for S_$k <= $b: recheck of file sh$s.json"
      $PY -I "$R/check/check_shard.py" "$d/sh$s.json" "$b" | cut -c1-240; echo "exit ${PIPESTATUS[0]}"
    done
  fi
}
sharded 6 2.363 "$S6" 48 0 25
sharded 7 2.552 "$S7" 576 1 561
echo "== E(r*) at r* = 60333/200000 with s_5 = 2187/1000, s_6 = 2363/1000, s_7 = 2552/1000"
$PY -I "$R/check/check_majorant.py" 60333/200000 $P3 5=2187/1000 6=2363/1000 7=2552/1000; echo "exit $?"
echo "== Patel's displayed computation (MathDB problem 392062)"
$PY -I "$R/check/check_patel_values.py"; echo "exit $?"
echo "== consistency: the certificate for S_5 with the bound 2.186 < S_5 must be rejected"
$PY -I "$R/check/check_sidon.py" "$R/certificate/s5_certificate.json" 2.186 | cut -c1-160; echo "exit ${PIPESTATUS[0]}"
$PY -I "$R/check/make_controls.py" "$R/certificate/s5_certificate.json" "$W" > /dev/null
for c in drop_vertex drop_subtree drop_cell zero_y bad_halfwidth malformed; do
  echo "== consistency: altered certificate for S_5 ($c) must be rejected"
  $PY -I "$R/check/check_sidon.py" "$W/$c.json" 2.187 2>&1 | tail -1 | cut -c1-160; echo "exit ${PIPESTATUS[0]}"
done
if [ -d "$S6" ]; then
  echo "== consistency: file sh25.json of the certificate for S_6 with the bound 2.362 must be rejected"
  $PY -I "$R/check/check_shard.py" "$S6/sh25.json" 2.362 | cut -c1-160; echo "exit ${PIPESTATUS[0]}"
fi
if [ -d "$S7" ]; then
  echo "== consistency: file sh561.json of the certificate for S_7 with the bound 2.551 must be rejected"
  $PY -I "$R/check/check_shard.py" "$S7/sh561.json" 2.551 | cut -c1-160; echo "exit ${PIPESTATUS[0]}"
  echo "== consistency: coverage for S_7 with one shard log missing must fail"
  $PY -I "$R/check/check_cover.py" "$S7" $(ls "$R"/logs/s7_shards/sh*.log | grep -v '/sh3.log$'); echo "exit $?"
  echo "== consistency: coverage for S_7 with a log that names another shard file must fail"
  sed 's/file=sh5.json/file=sh6.json/' "$R/logs/s7_shards/sh5.log" > "$W/sh5_bad.log"
  $PY -I "$R/check/check_cover.py" "$S7" $(ls "$R"/logs/s7_shards/sh*.log | grep -v '/sh5.log$') "$W/sh5_bad.log"; echo "exit $?"
fi
rm -rf "$W"
echo "== consistency: E at r* + 10^-6 = 301666/10^6 must be >= 1"
$PY -I "$R/check/check_majorant.py" 301666/1000000 $P3 5=2187/1000 6=2363/1000 7=2552/1000; echo "exit $?"
echo "== consistency: E(r*) with s_7 = ceil(10^8 sqrt 7)/10^8 must be >= 1"
$PY -I "$R/check/check_majorant.py" 60333/200000 $P3 5=2187/1000 6=2363/1000; echo "exit $?"
echo "== python -O is refused"
for f in check_majorant.py check_sidon.py check_shard.py check_cover.py; do $PY -I -O "$R/check/$f" x 2>&1 | head -1; echo "exit ${PIPESTATUS[0]}"; done
