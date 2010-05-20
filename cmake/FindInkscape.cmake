# - Finds inkscape program
#
# Variables set:
#   INKSCAPE_EXECUTABLE       Path to the ctags executable
#
# Commands:
#   ADD_SVG_FILES(target file1 file2 ...) 
#      Adds rules to build PDF files from SVG files, make <target> depend on it
#

include(FindPackageHandleStandardArgs)

find_program(INKSCAPE_EXECUTABLE
  NAMES inkscape
)

find_package_handle_standard_args(Inkscape DEFAULT_MSG INKSCAPE_EXECUTABLE)

if(INKSCAPE_EXECUTABLE)

  macro(add_svg_files TARGET)
	unset(_pdf_files)

	foreach(_svg_file ${ARGN})
	  string(REGEX REPLACE \\.svg$ .eps _eps_file ${_svg_file})
	  string(REGEX REPLACE \\.eps$ .pdf _pdf_file ${_eps_file})

	  list(APPEND _pdf_files ${_pdf_file})

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_svg_file}
		COMMAND ${INKSCAPE_EXECUTABLE} 
		ARGS -D -z --file=${_svg_file} --export-eps=${_eps_file}
		COMMENT "Exporting ${_svg_file}"
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
