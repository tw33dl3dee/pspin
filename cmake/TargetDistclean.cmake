#
# Adds a file or directory to the FILES_TO_DELETE var so that it is removed
# when "make distclean" is run
#
# Prototype:
#    ADD_FILE_TO_DISTCLEAN(file)
#    ADD_DIR_TO_DISTCLEAN(dir)
# Parameters:
#    file    A file (absolute or project-source-dir-relative path)
#    dir     A directory (absolute or project-source-dir-relative path)
#

MACRO(ADD_FILE_TO_DISTCLEAN TARGET_TO_DELETE)
  SET_PROPERTY(GLOBAL APPEND PROPERTY DISTCLEAN_FILES_TO_DELETE ${TARGET_TO_DELETE})
ENDMACRO(ADD_FILE_TO_DISTCLEAN)

MACRO(ADD_DIR_TO_DISTCLEAN TARGET_TO_DELETE)
  SET_PROPERTY(GLOBAL APPEND PROPERTY DISTCLEAN_DIRS_TO_DELETE ${TARGET_TO_DELETE})
ENDMACRO(ADD_DIR_TO_DISTCLEAN)

#
# Add current directory and specified targets to list of distcleaned objects
#
# Prototype:
#    ENABLE_DISTCLEAN([target1 target2...])
# Parameters:
#    target1, target2...  List of targets which output dirs shall be additionally distcleaned
#

MACRO(ENABLE_DISTCLEAN)
  #MESSAGE(STATUS "Adding ${CMAKE_CURRENT_BINARY_DIR} to distclean")
  IF(MSVC)
    ADD_DIR_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/*.dir )
    ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/*.vcproj )
    ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/*.vcproj.cmake )
    ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}.sln )
  ENDIF(MSVC)
  ADD_DIR_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/distclean.dir )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/CMakeCache.txt )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/install_manifest.txt )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/CPackConfig.cmake )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/CPackSourceConfig.cmake )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/_CPack_Packages )
  ADD_DIR_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/PACKAGE.dir )
  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/cmake_install.cmake )

  # This code does not work yet. I don't know why CPACK_GENERATOR is null.
  IF(CPACK_GENERATOR)
    FOREACH(_gen ${CPACK_GENERATOR})
      #MESSAGE(STATUS "Adding file ${CMAKE_CURRENT_BINARY_DIR}/${CPACK_SOURCE_PACKAGE_FILE_NAME}.${_gen} to distclean")
	  ADD_FILE_TO_DISTCLEAN( ${CMAKE_CURRENT_BINARY_DIR}/${CPACK_SOURCE_PACKAGE_FILE_NAME}.${_gen} )
	ENDFOREACH(_gen)
  ELSE(CPACK_GENERATOR)
	#MESSAGE("CPACK_GENERATOR was not defined (value: ${CPACK_GENERATOR})")
  ENDIF(CPACK_GENERATOR)

  FOREACH(_target ${ARGN})
	#MESSAGE("Target: ${_target}")
	FOREACH(_propname LIBRARY_OUTPUT_DIRECTORY ARCHIVE_OUTPUT_DIRECTORY RUNTIME_OUTPUT_DIRECTORY)
	  #MESSAGE("Propname: ${_propname}")
	  GET_TARGET_PROPERTY(_prop ${_target} ${_propname})
	  #MESSAGE("Prop: ${_prop}")
	  IF(NOT ${_prop} STREQUAL _prop-NOTFOUND)
		GET_FILENAME_COMPONENT(_path ${_prop} ABSOLUTE)
		# TODO: this is dangerous, coz' it may contain other files
		# Moreover, it doesn't work with Out-of-source builds
		MESSAGE(STATUS "Adding output directory ${_path} to distclean")
		ADD_DIR_TO_DISTCLEAN(${_path})
	  ENDIF()
	ENDFOREACH(_propname)
  ENDFOREACH(_target)

  ADD_DIR_TO_DISTCLEAN(${CMAKE_CURRENT_BINARY_DIR}${CMAKE_FILES_DIRECTORY})
  ADD_FILE_TO_DISTCLEAN(${CMAKE_CURRENT_BINARY_DIR}/Makefile)
ENDMACRO(ENABLE_DISTCLEAN)

#
# Create a "make distclean" target
#
# Prototype:
#    GENERATE_DISTCLEAN_TARGET()
# Parameters:
#    (none)
#

MACRO(GENERATE_DISTCLEAN_TARGET)
  GET_PROPERTY(_files_to_delete GLOBAL PROPERTY DISTCLEAN_FILES_TO_DELETE)
  GET_PROPERTY(_dirs_to_delete GLOBAL PROPERTY DISTCLEAN_DIRS_TO_DELETE)

  ADD_CUSTOM_TARGET(distclean cmake -E cmake_echo_color --switch= --yellow "Performing distribution clean..." 	
	# Dirty workaround
	COMMAND make clean)
  ADD_CUSTOM_COMMAND(
	DEPENDS clean
	COMMAND cmake -E remove -f ${_files_to_delete}
	TARGET distclean
	)

  FOREACH(_dir ${_dirs_to_delete})
	ADD_CUSTOM_COMMAND(TARGET distclean
	  COMMAND cmake -E remove_directory ${_dir}
	  )
  ENDFOREACH(_dir)
ENDMACRO(GENERATE_DISTCLEAN_TARGET)

DEFINE_PROPERTY(GLOBAL PROPERTY DISTCLEAN_FILES_TO_DELETE
  BRIEF_DOCS "List of files which are distclean-ed"
  FULL_DOCS "List of files which are distclean-ed")
DEFINE_PROPERTY(GLOBAL PROPERTY DISTCLEAN_DIRS_TO_DELETE
  BRIEF_DOCS "List of dirs which are distclean-ed"
  FULL_DOCS "List of dirs which are distclean-ed")

IF(NOT DISTCLEAN_ENABLED)
  SET(DISTCLEAN_ENABLED 1 CACHE INTERNAL "True if distclean target support has been enabled" FORCE)
  MESSAGE(STATUS "Enabled distclean support")
ENDIF()
