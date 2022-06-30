#!/usr/bin/env bash
set -e

# command adapted from https://github.com/JLLeitschuh/ktlint-gradle  task addKtlintFormatGitPreCommitHook
filesToFormat="$(git --no-pager diff --name-status --no-color --cached | \
  awk '($1 == "M" || $1 == "A") && $2 ~ /\.hs/ { print $2} $1 ~ /R/ && $3 ~ /\.hs/ { print $3 } ')"

echo "files to format $filesToFormat"
for sourceFilePath in $filesToFormat
do
  ormolu --mode inplace "$(pwd)/$sourceFilePath"
  git add $sourceFilePath
done;
