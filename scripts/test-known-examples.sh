#!/bin/bash

failed_path=$(realpath .)/failed

function fail() {
    echo $1 >&2
    touch $failed_path
}

DOMINO=$(realpath $DOMINO)

echo "# Checking Reproducers still prove..."
for project_path in example-projects/repro-*; do
    project=$(basename $project_path)
    (
        echo "## Checking $project proves..."
        cd $project_path
        $DOMINO prove || fail "expected success, but failed: $project_path"
    )
done

echo "# Checking Error Reproducers still fail..."
for project_path in example-projects/err-repro-*; do
    project=$(basename $project_path)
    (
        echo "## Checking $project fails..."
        cd $project_path
        $DOMINO prove && fail "expected error, but succeeded: $project_path"
    )
done

# sed script from https://unix.stackexchange.com/a/244479
echo "# Checking known-good proofs still prove..."
sed -e 's/[[:space:]]*#.*// ; /^[[:space:]]*$/d' "example-projects/known-good.txt" | while read project; do
    project_path=example-projects/$project
    # skip comments
    if [ ! -d $project_path ]; then
        echo "WARN: skipping non-existing project in known-good proofs: $project"
        continue
    fi
    (
        echo "## Checking $project proves..."
        cd $project_path
        $DOMINO prove || fail "expected success, but failed: $project_path"
        echo "## Checking $project latex export..."
        $DOMINO latex || fail "expected success, but failed: $project_path"
        (
            cd _build/latex
            for file in Theorem_*.tex; do
                TEMPFILE=`mktemp`
                pdflatex "$file" >$TEMPFILE 2>&1 || fail "$(tail -n 20 $TEMPFILE)"
            done
        )
    )
done

echo "# Checking slow known-good proofs still parse..."
sed -e 's/[[:space:]]*#.*// ; /^[[:space:]]*$/d' "example-projects/known-good-slow.txt" | while read project; do
    project_path=example-projects/$project
    # skip comments
    if [ ! -d $project_path ]; then
        echo "WARN: skipping non-existing project in known-good proofs: $project"
        continue
    fi
    (
        echo "## Checking $project parses..."
        cd $project_path
        $DOMINO proofsteps || fail "expected success, but failed: $project_path"
    )
done


if [ -f $failed_path ]; then
    exit 1
fi
