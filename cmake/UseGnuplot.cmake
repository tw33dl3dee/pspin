# - Support for converting gnuplot plots into PDF
#
# Depends:  FindGnuplot
#
# Commands:
#   ADD_PLOT_FILES(target file1 file2 ...) 
#      Adds rules to build PDF files from PLOT files and corresponding DAT files, make <target> depend on it
#

if(GNUPLOT_FOUND)
  find_program(EPSTOPDF_EXECUTABLE
	NAMES epstopdf
	)

  macro(add_plot_files TARGET)
	unset(_pdf_files)

	foreach(_plot_file ${ARGN})
	  string(REGEX REPLACE \\.plot$ "" _basename ${_plot_file})
	  set(_eps_file "${_basename}.eps")
	  set(_pdf_file "${_basename}.pdf")
	  set(_data_glob "${_basename}*.dat")

	  list(APPEND _pdf_files ${_pdf_file})

	  file(GLOB _data_files ${_data_glob})

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_plot_file} ${_data_files}
		COMMAND ${GNUPLOT_EXECUTABLE}
		ARGS ${_plot_file}
		COMMENT "Plotting ${_plot_file}"
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
