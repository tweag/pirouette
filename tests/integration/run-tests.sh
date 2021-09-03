#! /bin/bash
set -euo pipefail

########################
# Command Line Options #
########################

# Tells use we're running on ci
onci=false

# Tells us to run fast tests only
fast=false

# Speficies part of a string that we want the tests to be ran to contain
matching=""

# copy the comand line to generate the TLA+ files to the clipboard
copy_cmd=false

# Only generates the TLA+ files, don't run TLA+
gen_only=false

while [[ $# -ge 1 ]]; do
  case $1 in
    --ci)   onci=true;;
    --fast) fast=true;;
    --containing) shift; matching=".*$1.*";;
    --copy-cmd|-c) copy_cmd=true;;
    --gen-only|-g) gen_only=true;;
    *)  echo "Unknown option: $1"; exit 1;;
  esac
  shift
done

######################
# Auxiliar Functions #
######################

mechoPref() {
  if [[ $# -ne 3 ]]; then
    echo "usage: mechoPref <prefix> <color> <text>"
    echo "you gave: $@"
    exit 1
  fi

  local code=""
  case $2 in
    green)  code="\e[32m" ;;
    GREEN)  code="\e[42m" ;;
    red)    code="\e[31m" ;;
    RED)    code="\e[41m" ;;
    yellow) code="\e[33m" ;;
    YELLOW) code="\e[43m" ;;
    blue)   code="\e[36m" ;;
    BLUE)   code="\e[46m" ;;
  esac

  echo -e "$1${code}${3}\e[0m"
}

mecho() {
  mechoPref "" "$1" "$2"
}

get-opt-json-key-into() {
  local -n ref=$1
  ref=$(echo "$3" | jq -r "$2")
}

get-json-key-into() {
  local -n ref=$1
  ref=$(echo "$3" | jq -r "$2")
  if [[ "$ref" == "null" ]]; then
    echo -e "Key '$2' not found on input:\n$3"
    exit 1
  fi
}

get-json-key-into-def() {
  local -n ref=$1
  ref=$(echo "$3" | jq -r "$2")
  if [[ "$ref" == "null" ]]; then
    ref="$4"
  fi
}

string-to-errcode() {
  case $1 in
     "Counter Example"|"Counter-example"|"Counter-Example")
      echo 12
    ;;
     "Parse error"|"Parse Error")
      echo 150
    ;;
    "Invalid function application")
       echo 75
    ;;
    "Temporal property violated")
       echo 13
    ;;
    "Deadlock")
       echo 11
    ;;
    *)
      echo $1
    ;;
  esac
}

check-result() {
  local expected=$1
  local got=$2

  if [[ "$expected" == "Success" || "$expected" == "0" ]]; then
    if [[ "$got" == 0 ]]; then
      return 0
    else
      return 1
    fi
  elif [[ "$expected" == "Failure" ]]; then
    if [[ $got -ge 1 ]]; then
      return 0
    else
      return 1
    fi
  else
    exp_code=$(string-to-errcode "$expected")
    if [[ $exp_code == $got ]]; then
      return 0
    else
      return 1
    fi
  fi
}

##################
# Running a Test #
##################

run-single-test() {
  if [[ $# -ne 2 ]]; then
    echo "run-single-test expects: <has_failures ref> <JSON test description>"
    exit 1
  fi
  local -n did_fail=$1
  local json=$2
  local res=0

  # Gets the necessary JSON keys
  get-json-key-into name     ".name"     "$json"
  get-json-key-into testdir  ".cd"       "$json"
  get-json-key-into pir      ".pir"      "$json"
  get-json-key-into options  ".options"  "$json"
  get-json-key-into tlacmd   ".tla"      "$json"

  # Options with a default value
  get-json-key-into-def expected ".expected" "$json" "Success"
  get-json-key-into-def slowtest ".slow"     "$json" "false"

  # Gets the optional JSON keys
  get-opt-json-key-into pp      ".postprocess" "$json"
  get-opt-json-key-into output  ".output"      "$json"
  get-opt-json-key-into pending ".pending"     "$json"

  if [[ "$pending" != "null" ]]; then
    mecho yellow "+ Skipping Pending Test: $name"
    mecho yellow "  - $pending"
    return 0
  fi

  if $fast && [[ "$slowtest" == "true" ]]; then
    mecho yellow "+ Skipping Slow Test: $name"
    return 0
  fi

  if [[ ! -z "$matching" ]] && [[ ! "$name" =~ ${matching} ]]; then
    mecho yellow "+ Skipping Unselected Test: $name"
    return 0
  fi

  mecho blue "+ Running:   $name"
  mecho blue "  Expecting: $expected"
  cd "$testdir"
  if [[ "$output" == "null" ]]; then
    mecho red "    ! No output specified; using Contract.tla"
    output="Contract.tla"
  fi

  if $copy_cmd; then
    echo "cabal exec pirouette -- $testdir/$pir $options" | xclip -sel clip
    exit 0
  else
    set +e
    mecho blue "    - Running pirouette"
    eval "cabal exec pirouette -- $pir $options > $output"
    res=$?
    set -e
  fi

  if [[ "$res" -ne "0" ]]; then
    mecho red "    ! pirouette failed"
    mecho red "    !    ran with: $pir $options"
    mecho red "    !    redirected to: $output"
    return 1
  fi

  if [[ "$pp" != "null" ]]; then
    mecho blue "    - Running post-process step"
    eval "$pp"
  fi

  if $gen_only; then
    mecho blue "    - Not Running TLA+"
  else
    if [[ "$tlacmd" != "null" ]]; then
      mecho blue "    - Running TLA+"
      set +e
      eval "$tlacmd > tla.out"
      res=$?
      set -e
    fi

    set +e
    check-result "$expected" "$res"
    fres=$?
    set -e

    if [[ "$fres" == "0" ]]; then
      mechoPref "  " GREEN "+ OK"
    else
      mechoPref "  " RED "+ Fail"
      mechoPref "    " red "- got: $res"
      did_fail=true
      cat tla.out
    fi

    rm tla.out "$output"
  fi

  cd - > /dev/null
}

############################
# main = Running All Tests #
############################

mecho blue "Building pirouette"
cabal build
if [[ "$(basename $(pwd))" == "pirouette" ]]; then
  cd tests/integration
fi

file=all.json
len=`jq 'length' ${file}`

has_failure=false
for i in $(seq 0 $(( $len - 1 ))); do
  test_desc=$(jq ".[${i}]" $file)

  set +e
  run-single-test has_failure "$test_desc"
  res=$?
  set -e

  if ! $onci && $has_failure; then
    mecho red "Found a failure while running locally, will stop now."
    exit 1
  fi
done

if $has_failure; then
  exit 1
else
  mecho green "No failures, great work!"
  exit 0
fi
