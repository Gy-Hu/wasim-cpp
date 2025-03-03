#!/bin/bash

# Script to rebuild glog without stack trace support for static linking

set -e

cd deps/glog

# Clean previous build
rm -rf build
rm -rf install

# Create build directory
mkdir -p build
cd build

# Configure with stack trace disabled
cmake .. -DCMAKE_INSTALL_PREFIX=../install -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DWITH_GFLAGS=ON -DBUILD_SHARED_LIBS=OFF -DWITH_UNWIND=OFF -DCMAKE_CXX_FLAGS="-DHAVE_NO_SYMBOLIZE -DHAVE_NO_STACKTRACE"

# Build and install
make -j$(nproc)
make install

echo "Glog rebuilt without stack trace support" 