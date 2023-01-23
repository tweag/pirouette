#! /usr/bin/env bash
set -uo pipefail

show_help() {
  cat <<EOF
usage: ./tests/run-tests.sh [--ci]
  Note the script is ran from the repo root.

  Options:
    --ci      Informs the script it is running in CI; this means
              we will save the test results as a file (named <project>-cabal-test.{res,out})
              The script WILL SUCCEED IFF THE BUILD SUCCEEDED; 
              This behavior ensures that the build gets cached. 
              Another job should check the artifact/cache to decide whether
              the workflow passes or fails as a whole
EOF
}

ci=false
while [[ $# -ne "0" ]]; do
  case $1 in
    --ci) ci=true; shift;;
    *) show_help; exit 1;;
  esac
done

if $ci; then
  pushd ..
  cabal update
  popd
fi

## Runs the cabal tests of a project; creates artifacts with potential failures.
run_cabal_test() {
  local proj=$1
  echo "Running 'cabal run tests' on $proj"

  local cabal_res=0
  if $ci; then
    cabal run tests | tee "./${proj}-cabal-test.out"
    cabal_res=$?
    echo "run_cabal_test:$cabal_res" >> "./${proj}-cabal-test.res"
  else
    cabal run tests
    cabal_res=$?
  fi

  return $cabal_res
}

cabal_build_ok=true
cabal_test_ok=true

## Generate cabal file and build pirouette
hpack
cabal build
cabal_build_ok=$?

if [[ "$cabal_build_ok" -ne "0" ]]; then
  echo "[FAILURE] 'cabal build' failed, will exit with 1"
  exit 1
fi

run_cabal_test "pirouette"
if [[ "$?" -ne "0" ]]; then
  echo "[FAILURE] 'cabal run tests' failed; check the respective artifact."
  cabal_test_ok=false
fi

## When running in CI, always return 0; we should use a subsequent job to check the
## produced files.
if $ci; then
  exit 0
elif $cabal_test_ok; then
  exit 0
else
  exit 1
fi
