#! /bin/bash

#
# Howto Z-Shell:
# $ autoload bashcompinit
# $ bashcompinit
# $ source *.sh
# $ complete -F _yassi_nextgen() -o filename yassi_nextgen
#

_yassi_nextgen ()
{
local cur

	COMPREPLY=()
	cur=${COMP_WORDS[COMP_CWORD]}

	case "$cur" in
		-*)
		COMPREPLY=( $( compgen -W ' \
			--help \
			--bash_completion \
			--clean_tables \
			--final \
			--compare_bc \
			--compare_replay_bc \
			--view_bc \
			--view_instr_bc \
			--cfg \
			--cfg2 \
			--run \
			--test \
			--show_results \
			--show_golden_results \
			--show_test_vectors \
			--replay \
			--show_coverage \
			--show_bb \
			--show_replay_bb \
			--clean \
			--get_result \
			--list_external_functions \
			--show_exceptions \
			--show_golden_exceptions \
			--show_bdd \
			--show_db \
			--make_bc \
			--debug \
			--quiet \
			--verbose \
			--log_file_enabled \
			--dump_memory \
			--dump_smt \
			--memory_check \
			--timeout \
			--max_depth \
			--file \
			--editor \
			--image_viewer \
			--logfile_name \
			--compare_tool \
			--tmp_folder \
			--llvm_path \
			--modelcheck_binary \
			--bughunter_binary \
			--frontend_binary \
			--replay_binary \
			--isolate_function \
			' -- $cur ) );;
	esac

	return 0
}

complete -F _yassi_nextgen  yassi_nextgen
