YASSI_HOME=$(abspath $(dir $(lastword $(MAKEFILE_LIST)))../)
LLVM_SRC_HOME=$(YASSI_HOME)/05_third_party/03_llvm/llvm-5.0.0.src/

all: instr replay debug
debug: ${LLVM_SRC_HOME}/build/lib/YassiDebug.so
instr: ${LLVM_SRC_HOME}/build/lib/YassiInstr.so
replay: ${LLVM_SRC_HOME}/build/lib/YassiReplay.so
instr_clean: clean_instr instr
replay_clean: clean_replay replay
debug_clean: clean_debug debug

${LLVM_SRC_HOME}/build/lib/YassiInstr.so: 01_YassiInstr/yassi_instrumentation_pass.cpp
	bash 99_Utils/alter_cmake.sh instr
	rm -rf $(LLVM_SRC_HOME)/lib/Transforms/YassiInstr
	rm -rf $(LLVM_SRC_HOME)/build/lib/Transforms/YassiInstr
	mkdir -p $(LLVM_SRC_HOME)/lib/Transforms/YassiInstr
	cp -R $(YASSI_HOME)/04_utils/02_types /$(LLVM_SRC_HOME)/lib/Transforms/YassiInstr/
	cp $(YASSI_HOME)/04_utils/03_datastructures/yassi_datastructuretree.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp $(YASSI_HOME)/04_utils/03_datastructures/yassi_genericdatastructures.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp $(YASSI_HOME)/04_utils/01_src/yassi_baseutils.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/ 
	cp $(YASSI_HOME)/04_utils/01_src/yassi_basedatabase.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/ 
	cp $(YASSI_HOME)/05_third_party/include/sqlite3.h ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/ 
	cp 00_GenericPasses/01_src/yassi_basepass.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 00_GenericPasses/01_src/yassi_fillnames.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 00_GenericPasses/01_src/yassi_database.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/ 
	cp 00_GenericPasses/01_src/yassi_demangle.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 00_GenericPasses/01_src/yassi_listexternalfunctions.* ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 01_YassiInstr/*.cpp ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 01_YassiInstr/*.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 01_YassiInstr/01_src/*.cpp ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 01_YassiInstr/01_src/*.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiInstr/
	cp 01_YassiInstr/YassiInstr.exports $(LLVM_SRC_HOME)/lib/Transforms/YassiInstr
	cp 01_YassiInstr/CMakeLists.txt.tmp $(LLVM_SRC_HOME)/lib/Transforms/YassiInstr/CMakeLists.txt
	rm 01_YassiInstr/CMakeLists.txt.tmp
	cmake -B$(LLVM_SRC_HOME)/build -H$(LLVM_SRC_HOME)
	make -j 2 -C $(LLVM_SRC_HOME)/build/lib/Transforms/YassiInstr
	cp $(LLVM_SRC_HOME)/build/lib/YassiInstr.so $(YASSI_HOME)/09_lib
	
${LLVM_SRC_HOME}/build/lib/YassiReplay.so: 02_YassiReplay/yassi_replay_pass.cpp
	bash 99_Utils/alter_cmake.sh replay
	rm -rf $(LLVM_SRC_HOME)/lib/Transforms/YassiReplay
	rm -rf $(LLVM_SRC_HOME)/build/lib/Transforms/YassiReplay
	mkdir -p $(LLVM_SRC_HOME)/lib/Transforms/YassiReplay
	cp -R $(YASSI_HOME)/04_utils/02_types /$(LLVM_SRC_HOME)/lib/Transforms/YassiReplay/
	cp 00_GenericPasses/01_src/yassi_database.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/ 
	cp 00_GenericPasses/01_src/yassi_fillnames.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 00_GenericPasses/01_src/yassi_removeprintf.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 00_GenericPasses/01_src/yassi_basepass.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 02_YassiReplay/CMakeLists.txt.tmp $(LLVM_SRC_HOME)/lib/Transforms/YassiReplay/CMakeLists.txt
	rm 02_YassiReplay/CMakeLists.txt.tmp
	cp $(YASSI_HOME)/05_third_party/include/sqlite3.h ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/ 
	cp 02_YassiReplay/YassiReplay.exports $(LLVM_SRC_HOME)/lib/Transforms/YassiReplay
	cp $(YASSI_HOME)/04_utils/03_datastructures/yassi_genericdatastructures.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp $(YASSI_HOME)/04_utils/01_src/yassi_baseutils.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/ 
	cp $(YASSI_HOME)/04_utils/01_src/yassi_basedatabase.* ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/ 
	cp 02_YassiReplay/*.cpp ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 02_YassiReplay/*.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 02_YassiReplay/01_src/*.cpp ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cp 02_YassiReplay/01_src/*.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiReplay/
	cmake -B$(LLVM_SRC_HOME)/build -H$(LLVM_SRC_HOME)
	make -C $(LLVM_SRC_HOME)/build/lib/Transforms/YassiReplay
	cp $(LLVM_SRC_HOME)/build/lib/YassiReplay.so $(YASSI_HOME)/09_lib

${LLVM_SRC_HOME}/build/lib/YassiDebug.so: 03_YassiDebug/yassi_debug_pass.cpp
	bash 99_Utils/alter_cmake.sh debug
	rm -rf $(LLVM_SRC_HOME)/lib/Transforms/YassiDebug
	rm -rf $(LLVM_SRC_HOME)/build/lib/Transforms/YassiDebug
	mkdir -p $(LLVM_SRC_HOME)/lib/Transforms/YassiDebug
	cp 03_YassiDebug/yassi_debug_pass.* $(LLVM_SRC_HOME)/lib/Transforms/YassiDebug
	cp 03_YassiDebug/YassiDebug.exports ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/
	cp $(YASSI_HOME)/05_third_party/include/sqlite3.h ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/ 
	cp -R $(YASSI_HOME)/04_utils/01_src/yassi_baseutils.* ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/ 
	cp $(YASSI_HOME)/04_utils/03_datastructures/yassi_genericdatastructures.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/
	cp $(YASSI_HOME)/04_utils/01_src/yassi_basedatabase.* ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/ 
	cp 00_GenericPasses/01_src/yassi_basepass.* ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/
	cp 00_GenericPasses/01_src/yassi_database.* ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/ 
	cp 03_YassiDebug/CMakeLists.txt.tmp $(LLVM_SRC_HOME)/lib/Transforms/YassiDebug/CMakeLists.txt
	rm 03_YassiDebug/CMakeLists.txt.tmp
	cp 03_YassiDebug/01_src/*.hpp ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/
	cp 03_YassiDebug/01_src/*.cpp ${LLVM_SRC_HOME}/lib/Transforms/YassiDebug/
	cp -R $(YASSI_HOME)/04_utils/02_types /$(LLVM_SRC_HOME)/lib/Transforms/YassiDebug/
	cmake -B$(LLVM_SRC_HOME)/build -H$(LLVM_SRC_HOME)
	make -C $(LLVM_SRC_HOME)/build/lib/Transforms/YassiDebug
	cp $(LLVM_SRC_HOME)/build/lib/YassiDebug.so $(YASSI_HOME)/09_lib

clean_instr:
	rm -rf $(LLVM_SRC_HOME)/build/lib/YassiInstr.so

clean_replay:
	rm -rf $(LLVM_SRC_HOME)/build/lib/YassiReplay.so

clean_debug: 
	rm -rf $(LLVM_SRC_HOME)/build/lib/YassiDebug.so

clean: clean_instr clean_replay clean_debug
	rm -rf $(YASSI_HOME)/09_lib/*.so
