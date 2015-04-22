#!/bin/bash -eu
# Installation script for Galois
set -e
set -o xtrace

SANDBOX=`readlink -m ${ENGROOT}/.cabal-sandbox`
LOCAL_MAPLE=${MAPLE_HOME}/bin/maple

OLD=${PWD}
cd maple/
${LOCAL_MAPLE} update-archive.mpl
cd ${OLD}

echo 'libname := "'"${PWD}"'/maple",libname:' >~/.mapleinit

cabal sandbox --sandbox=${SANDBOX} init
cabal install
