#! /bin/bash 

 dir_name=googletest

if [ ! -d $dir_name ]; then
    home_dir=$(pwd)

    git clone https://github.com/google/googletest
    cd $dir_name
    mkdir build
    cd build
    cmake -DCMAKE_INSTALL_PREFIX=../../../ ..
    make 
    make install
fi
