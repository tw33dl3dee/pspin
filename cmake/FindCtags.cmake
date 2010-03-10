# - Finds exuberant/GNU (currently only these flavours are supported) ctags.
#
# Variables set:
#   CTAGS_EXECUTABLE  Path to the ctags executable
#

include(FindPackageHandleStandardArgs)

find_program(CTAGS_EXECUTABLE
  NAMES ctags-exuberant exuberant-ctags ctags
)

find_package_handle_standard_args(Ctags DEFAULT_MSG CTAGS_EXECUTABLE)

if(CTAGS_EXECUTABLE AND NOT CTAGS_FLAVOR)
  execute_process(COMMAND ${CTAGS_EXECUTABLE} --version
	OUTPUT_VARIABLE _ctags_stdout
	ERROR_QUIET)
  string(TOLOWER ${_ctags_stdout} _ctags_stdout)
  if(NOT _ctags_stdout MATCHES exuberant)
	set(CTAGS_FLAVOR "GNU")
  else()
	set(CTAGS_FLAVOR "Exuberant")
  endif()
  set(CTAGS_FLAVOR ${CTAGS_FLAVOR} CACHE STRING "Ctags executable flavour" FORCE)
  message(STATUS "Ctags flavour: ${CTAGS_FLAVOR}")
endif()
