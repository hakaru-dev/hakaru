#!/bin/bash
set -e

mkdocs build --clean

REPO="git@github.com:hakaru-dev/hakaru-dev.github.io.git"

git clone $REPO outbound
pushd outbound
git checkout master || git checkout --orphan master
git rm -rf .
cp -R ../site/* .
rm -rf *.pyc __pycache__
git add .
git commit -m "Deploy to GitHub Pages"
git push $REPO master

popd
rm -rf outbound site

