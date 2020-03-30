#! /bin/bash 

if [ ! -d llvm-5.0.0.src ]; then
    home_dir=$(pwd)
    wget http://releases.llvm.org/5.0.0/llvm-5.0.0.src.tar.xz
    wget http://releases.llvm.org/5.0.0/cfe-5.0.0.src.tar.xz
   
    tar xf llvm-5.0.0.src.tar.xz
    tar xf cfe-5.0.0.src.tar.xz
   
    mv cfe-5.0.0.src llvm-5.0.0.src/tools/clang
   
    cd llvm-5.0.0.src
    mkdir build
    cd build
    export CXX=clang++
    cmake  -DCMAKE_INSTALL_PREFIX=../../../ ..
    make -j 2
    make 
    make install
    
    cd $home_dir
    rm *.tar.xz
fi
