#! /bin/bash

python extract_version.py

cd ..
BASE_PATH=$(pwd)
INSTALL_PATH=~/.yassi


if [ -d $INSTALL_PATH ]; then
    rm -rf $INSTALL_PATH
fi

mkdir $INSTALL_PATH
cd $INSTALL_PATH
touch config.txt
echo "base_path="$BASE_PATH >> config.txt

if [ -d $BASE_PATH/02_front_end/01_src/yassi_version.hpp ]; then
    rm $BASE_PATH/02_front_end/01_src/yassi_version.hpp
fi

mv $BASE_PATH/07_configuration/yassi_version.hpp $BASE_PATH/02_front_end/01_src/


