#! /usr/bin/env bash
set -uo pipefail

show_help() {
  cat <<EOF
usage: ./ci/run-tests.sh [--ci]
  Note the script is ran from the repo root; Running without --ci
  will run "ormolu --mode inplace" and fix offending files.
  Options:
    --ci      Instructs the script to save artifacts and
              only checks syntax, instead of fixing it.
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
    ormolu --mode check $(find ./src -name '*.hs') 2> >(tee "./${proj}-ormolu.artifact")
    ormolu_res=$?
  else
    ormolu --mode inplace $(find ./src -name '*.hs')
    ormolu_res=$?
  fi

  if $ci && [[ "$ormolu_res" -eq "0" ]]; then
    rm "./${proj}-ormolu.artifact"
  fi

  return $ormolu_res
}

## Runs the cabal tests of a project; creates artifacts with potential failures.
run_cabal_test() {
  local proj=$1
  echo "Running 'cabal run tests' on $proj"

  local cabal_res=0
  if $ci; then
    cabal run tests | tee "./${proj}-cabal-test.artifact"
    cabal_res=$?
  else
    cabal run tests
    cabal_res=$?
  fi

  if $ci && [[ "$cabal_res" -eq "0" ]]; then
    rm "./$proj-cabal-test.artifact"
  fi

  return $cabal_res
}

## Runs hlint on a project; creates artifacts with potential failures
run_hlint() {
  local proj=$1
  echo "Running 'hlint' on $proj"

  ## Since SimpleSMT is an external library, we want to minimize the difference.
  ## Hence, we do not run `hlint` on it.
  local hlint_res=0
  if $ci; then
    hlint . --ignore-glob="src/Pirouette/SMT/SimpleSMT.hs" | tee "./${proj}-hlint.artifact"
    hlint_res=$?
  else
    hlint . --ignore-glob="src/Pirouette/SMT/SimpleSMT.hs"
    hlint_res=$?
  fi

  if $ci && [[ "$hlint_res" -eq "0" ]]; then
    rm "./$proj-hlint.artifact"
  fi

  return $hlint_res
}

projects=("pirouette")
ormolu_ok=true
cabal_ok=true
hlint_ok=true

for p in ${projects[*]}; do
  hpack
done

for p in ${projects[*]}; do
  run_ormolu "$p"
  if [[ "$?" -ne "0" ]]; then
    echo "[FAILURE] 'ormolu --check' failed for $p; check the respective artifact."
    ormolu_ok=false
  fi

  run_cabal_test "$p"
  if [[ "$?" -ne "0" ]]; then
    echo "[FAILURE] 'cabal run tests' failed for $p; check the respective artifact."
    cabal_ok=false
  fi

  run_hlint "$p"
  if [[ "$?" -ne "0" ]]; then
    echo "[FAILURE] 'hlint' failed for $p; check the respective artifact."
    hlint_ok=false
  fi
done

if $cabal_ok && $ormolu_ok && $hlint_ok; then
  exit 0
else
  exit 1
fi