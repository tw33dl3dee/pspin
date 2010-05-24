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

  find_program(ICONV_EXECUTABLE
	NAMES iconv
	)

  macro(add_plot_files TARGET)
	unset(_pdf_files)

	foreach(_plot_file ${ARGN})
	  string(REGEX REPLACE \\.plot$ "" _basename ${_plot_file})
	  set(_eps_file "${_basename}.eps")
	  set(_pdf_file "${_basename}.pdf")
	  set(_data_glob "${_basename}*.dat")
	  set(_koi8_plot_file "${_basename}-koi8.gpl")

	  list(APPEND _pdf_files ${_pdf_file})

	  file(GLOB _data_files ${_data_glob})

	  add_custom_command(OUTPUT ${_koi8_plot_file}
		DEPENDS ${_plot_file}
		COMMAND ${ICONV_EXECUTABLE}
		ARGS    -f utf8 -t koi8r ${_plot_file} > ${_koi8_plot_file}
		COMMENT "Translating ${_plot_file} into KOI8-R"
		)

	  add_custom_command(OUTPUT ${_eps_file}
		DEPENDS ${_koi8_plot_file} ${_data_files}
		COMMAND ${GNUPLOT_EXECUTABLE}
		ARGS    ${_koi8_plot_file}
		COMMENT "Plotting ${_plot_file}"
		)

	  add_custom_command(OUTPUT ${_pdf_file}
		DEPENDS ${_eps_file}
		COMMAND ${EPSTOPDF_EXECUTABLE} 
		ARGS    --autorotate=All --outfile=${_pdf_file} ${_eps_file}
		COMMENT "Converting ${_eps_file}"
		)
	endforeach()

	add_custom_target(${TARGET} DEPENDS ${_pdf_files})
  endmacro()
endif()
