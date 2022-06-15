#! /usr/bin/env bash
set -uo pipefail

show_help() {
  cat <<EOF
usage: ./tests/run-tests.sh [--ci]
  Note the script is ran from the repo root; Running without --ci
  will run "ormolu --mode inplace" and fix offending files.
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

## Runs ormolu on all .hs files in a given project; sets the ormolu_ok
## variable to `false` in case ormolu fails. It also creates an artifact
## explaining the failure inside the tests folder.
run_ormolu() {
  local proj=$1
  echo "Running ormolu on $proj"

  local ormolu_res=0
  ## We use UTF-8 characters in the pretty printing of Top and Bottom,
  ## which requires to set our locale for Ormolu to be happy.
  export LC_ALL=C.UTF-8
  if $ci; then
    ormolu --mode check $(find ./src -name '*.hs')
    ormolu_res=$?
  else
    ormolu --mode inplace $(find ./src -name '*.hs')
    ormolu_res=$?
  fi

  return $ormolu_res
}

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

ormolu_ok=true
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

## Disable ormolu for the time being; re-enable back before merging into main.
##
## run_ormolu "$p"
## if [[ "$?" -ne "0" ]]; then
##   echo "[FAILURE] 'ormolu --check' failed for $p; check the respective artifact."
##   ormolu_ok=false
## fi

run_cabal_test "pirouette"
if [[ "$?" -ne "0" ]]; then
  echo "[FAILURE] 'cabal run tests' failed; check the respective artifact."
  cabal_test_ok=false
fi

## When running in CI, always return 0; we should use a subsequent job to check the
## produced files.
if $ci; then
  exit 0
elif $cabal_test_ok && $ormolu_ok; then
  exit 0
else
  exit 1
fi
