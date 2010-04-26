# - Finds dia program
#
# Variables set:
#   DIA_EXECUTABLE       Path to the ctags executable
#   EPSTOPDF_EXECUTABLE  Path to the epstopdf executable
#
# Commands:
#   ADD_DIA_FILES(target file1 file2 ...) 
#      Adds rules to build PDF files from DIA files, make <target> depend on it
#

include(FindPackageHandleStandardArgs)

find_program(DIA_EXECUTABLE
  NAMES dia
)

find_program(EPSTOPDF_EXECUTABLE
  NAMES epstopdf
)

find_package_handle_standard_args(Dia DEFAULT_MSG DIA_EXECUTABLE)

if(DIA_EXECUTABLE)

  macro(add_dia_files TARGET)
	unset(_pdf_files)

	foreach(_dia_file ${ARGN})
	  string(REGEX REPLACE \\.dia$ .eps _eps_file ${_dia_file})
	  string(REGEX REPLACE \\.dia$ .pdf _pdf_file ${_dia_file})

	  list(APPEND _pdf_files ${_pdf_file})

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_dia_file}
		COMMAND ${DIA_EXECUTABLE}
		ARGS    -t eps -e ${_eps_file} ${_dia_file}
		COMMENT "Exporting ${_dia_file}"
		)

	  add_custom_command(OUTPUT ${_pdf_file}
		DEPENDS ${_eps_file}
		COMMAND ${EPSTOPDF_EXECUTABLE} 
		ARGS    --outfile=${_pdf_file} ${_eps_file}
		COMMENT "Converting ${_eps_file}"
		)

	endforeach()

	add_custom_target(${TARGET} DEPENDS ${_pdf_files})
  endmacro()

endif()
