#!/bin/bash

failed_path=$(realpath .)/failed

function fail() {
  echo $1 >&2
  touch $failed_path
}

DOMINO=$(realpath $DOMINO)

echo "# Test sequential build (simple-KEM-example)"
(
  cd example-projects/simple-KEM-example
  rm -r _build
  $DOMINO prove --transcript
  CHECKSUM=$(tar --mtime='2000-01-01 00:00Z' -cf - _build/ | sha1sum | cut -f1 -d' ')

  for run in $(seq 5); do
    echo "## Run $run"
    $DOMINO prove
    [ $CHECKSUM = "$(tar --mtime='2000-01-01 00:00Z' -cf - _build/ | sha1sum | cut -f1 -d' ')" ] || fail "Run $run (sequential) produced different SMT from first run"
  done
)

echo "# Test parallel build (simple-KEM-example)"
(
  cd example-projects/simple-KEM-example
  rm -r _build
  $DOMINO prove --parallel 2 --transcript
  CHECKSUM=$(tar --mtime='2000-01-01 00:00Z' -cf - _build/ | sha1sum | cut -f1 -d' ')

  for run in $(seq 5); do
    echo "## Run $run"
    $DOMINO prove --parallel 2
    [ $CHECKSUM = "$(tar --mtime='2000-01-01 00:00Z' -cf - _build/ | sha1sum | cut -f1 -d' ')" ] || fail "Run $run (parallel) produced different SMT from first run"
  done
)

if [ -f $failed_path ]; then
  exit 1
fi
