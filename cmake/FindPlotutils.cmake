# - Finds plotutils (currently limited to pic2plot)
#
# Variables set:
#   PIC2PLOT_EXECUTABLE       Path to the ctags executable
#
# Commands:
#   ADD_PIC_FILES(target file1 file2 ...) 
#      Adds rules to build PDF files from PIC files, make <target> depend on it
#

include(FindPackageHandleStandardArgs)

find_program(PIC2PLOT_EXECUTABLE
  NAMES pic2plot
)

find_program(EPSTOPDF_EXECUTABLE
  NAMES epstopdf
)

find_package_handle_standard_args(Plotutils DEFAULT_MSG PIC2PLOT_EXECUTABLE)

if(PIC2PLOT_EXECUTABLE)

  macro(add_pic_files TARGET)
	unset(_pdf_files)

	foreach(_pic_file ${ARGN})
	  string(REGEX REPLACE \\.pic$ .eps _eps_file ${_pic_file})
	  string(REGEX REPLACE \\.eps$ .pdf _pdf_file ${_eps_file})

	  list(APPEND _pdf_files ${_pdf_file})

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_pic_file}
		COMMAND ${PIC2PLOT_EXECUTABLE} 
		ARGS -f 0.015 -F HersheyCyrillic -Tps ${_pic_file} > ${_eps_file}
		COMMENT "Plotting ${_pic_file}"
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
