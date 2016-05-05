#!/bin/bash
set -e

mkdocs build --clean

REPO="git@github.com:hakaru-dev/hakaru.git"

git clone $REPO outbound                                                                                                                                                                                      
pushd outbound                                                                                                                                                                                                                                  
git checkout gh-pages || git checkout --orphan gh-pages                                                                                                                                                                                                             
git rm -rf .                                                                                                                                                                                                                             
cp -R ../site/* .                                                                                                                                                                                                                        
git add .                                                                                                                                                                                                                                
git commit -m "Deploy to GitHub Pages"                                                                                                                                                                                                   
git push $REPO gh-pages                                                                                                                                                                                                                 

popd
rm -rf outbound site

