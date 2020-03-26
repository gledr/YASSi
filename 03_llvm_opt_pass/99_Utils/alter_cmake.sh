#! /bin/bash

# s3p 25.04.18
# When the optimization is built for the first time the CMakeLists.txt has to be altered
#
GLOBAL_CONFIG=~/.yassi/config.txt
CONFIG_DATA=$(cat $GLOBAL_CONFIG)
BASE_PATH=$(echo $CONFIG_DATA |  cut -d'=' -f2)
LLVM_SRC_HOME=$BASE_PATH/05_third_party/03_llvm/llvm-5.0.0.src/
CMAKEFILE=$LLVM_SRC_HOME/lib/Transforms/CMakeLists.txt

if [ $1 == "debug" ]; then
    echo "debug mode"
    if [ $(grep "YassiDebug" $CMAKEFILE ) ]; then
            echo "nothing to do"
        else
            sed -i -e "\$aadd_subdirectory(YassiDebug)" $CMAKEFILE
    fi 
    
    DEBUG=$BASE_PATH/03_llvm_opt_pass/03_YassiDebug
    cp $DEBUG/CMakeLists.txt $DEBUG/CMakeLists.txt.tmp
    sed -i -e "s|%%BASE_PATH_PATTERN%%|$BASE_PATH|g" $DEBUG/CMakeLists.txt.tmp
    
fi

if [ $1 == "instr" ]; then
    echo "instr mode"
    if [ $(grep "YassiInstr" $CMAKEFILE ) ]; then
            echo "nothing to do"
        else
            sed -i -e "\$aadd_subdirectory(YassiInstr)" $CMAKEFILE
    fi 
    

    INSTR=$BASE_PATH/03_llvm_opt_pass/01_YassiInstr
    cp $INSTR/CMakeLists.txt $INSTR/CMakeLists.txt.tmp
    sed -i -e "s|%%BASE_PATH_PATTERN%%|$BASE_PATH|g" $INSTR/CMakeLists.txt.tmp
    
fi

if [ $1 == "replay" ]; then
    echo "replay mode"
    if [ $(grep "YassiReplay" $CMAKEFILE ) ]; then
            echo "nothing to do"
        else
            sed -i -e "\$aadd_subdirectory(YassiReplay)" $CMAKEFILE
    fi 
    
    REPLAY=$BASE_PATH/03_llvm_opt_pass/02_YassiReplay
    cp $REPLAY/CMakeLists.txt $REPLAY/CMakeLists.txt.tmp
    sed -i -e "s|%%BASE_PATH_PATTERN%%|$BASE_PATH|g" $REPLAY/CMakeLists.txt.tmp
fi


