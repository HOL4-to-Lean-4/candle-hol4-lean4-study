B=~/candle_build/repo/_build
export PATH=$B/polyml/bin:$B/HOL/bin:/usr/bin:/bin LD_LIBRARY_PATH=$B/polyml/lib HOLDIR=$B/HOL
cd ~/ts_export; timeout 500 hol run "${WORK_ROOT:-/mnt/e}"/ts_ws/score/q.sml 2>&1 | grep -A6 -E "@@" | cut -c1-260
