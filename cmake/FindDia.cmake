# - Finds dia program
#
# Variables set:
#   DIA_EXECUTABLE  Path to the ctags executable
#

include(FindPackageHandleStandardArgs)

find_program(DIA_EXECUTABLE
  NAMES dia
)

find_package_handle_standard_args(Dia DEFAULT_MSG DIA_EXECUTABLE)

if(DIA_EXECUTABLE)

  macro(add_dia_files)
	foreach(_dia_file ${ARGN})
	  string(REGEX REPLACE \\.dia$ .eps _eps_file ${_dia_file})
	  string(REGEX REPLACE \\.dia$ .pdf _pdf_file ${_dia_file})

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_dia_file}
		COMMAND ${DIA_EXECUTABLE} -t eps -e ${_eps_file} ${_dia_file}
		COMMENT "Exporting ${_dia_file}"
		)

	  add_custom_command(OUTPUT ${_pdf_file}
		DEPENDS ${_eps_file}
		COMMAND epstopdf --outfile=${_pdf_file} ${_eps_file}
		COMMENT "Converting ${_eps_file}"
		)

	endforeach()
  endmacro()

endif()
