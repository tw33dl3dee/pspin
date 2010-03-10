# - Try to find precompiled headers support for GCC 3.4 and 4.x
# Once done this will define:
#
# Variable:
#   PCHSupport_FOUND
#
# Macro:
#   ADD_PRECOMPILED_HEADER  _targetName _input  _dowarn
#   ADD_PRECOMPILED_HEADER_TO_TARGET _targetName _input _pch_output_to_use _dowarn
#   ADD_NATIVE_PRECOMPILED_HEADER _targetName _input _dowarn
#   GET_NATIVE_PRECOMPILED_HEADER _targetName _input

IF(CMAKE_COMPILER_IS_GNUCXX)

    EXEC_PROGRAM(
    	${CMAKE_CXX_COMPILER}  
        ARGS 	${CMAKE_CXX_COMPILER_ARG1} -dumpversion 
        OUTPUT_VARIABLE gcc_compiler_version)
    #MESSAGE("GCC Version: ${gcc_compiler_version}")
    IF(gcc_compiler_version MATCHES "4\\.[0-9]\\.[0-9]")
        SET(PCHSupport_FOUND TRUE)
    ELSE(gcc_compiler_version MATCHES "4\\.[0-9]\\.[0-9]")
        IF(gcc_compiler_version MATCHES "3\\.4\\.[0-9]")
            SET(PCHSupport_FOUND TRUE)
        ENDIF(gcc_compiler_version MATCHES "3\\.4\\.[0-9]")
    ENDIF(gcc_compiler_version MATCHES "4\\.[0-9]\\.[0-9]")
    
	SET(_PCH_include_prefix "-I")
	
ELSE(CMAKE_COMPILER_IS_GNUCXX)
	IF(WIN32)	
		SET(PCHSupport_FOUND TRUE) # for experimental msvc support
		SET(_PCH_include_prefix "/I")
	ELSE(WIN32)
		SET(PCHSupport_FOUND FALSE)
	ENDIF(WIN32)	
ENDIF(CMAKE_COMPILER_IS_GNUCXX)


MACRO(_PCH_GET_COMPILE_FLAGS _out_compile_flags)

  IF(CMAKE_BUILD_TYPE)
    STRING(TOUPPER "CMAKE_CXX_FLAGS_${CMAKE_BUILD_TYPE}" _flags_var_name)
  ELSE(CMAKE_BUILD_TYPE)
    SET(_flags_var_name "CMAKE_CXX_FLAGS")
  ENDIF(CMAKE_BUILD_TYPE)
  SET(${_out_compile_flags} ${${_flags_var_name}} )
  
  IF(CMAKE_COMPILER_IS_GNUCXX)
    
    GET_TARGET_PROPERTY(_targetType ${_PCH_current_target} TYPE)
    IF(${_targetType} STREQUAL SHARED_LIBRARY)
      LIST(APPEND ${_out_compile_flags} "${${_out_compile_flags}} ${CMAKE_SHARED_LIBRARY_CXX_FLAGS}")
    ENDIF(${_targetType} STREQUAL SHARED_LIBRARY)
	
    IF(CMAKE_BUILD_TYPE)
      STRING(TOUPPER "COMPILE_DEFINITIONS_${CMAKE_BUILD_TYPE}" _dir_flags_var_name)
      GET_DIRECTORY_PROPERTY(_directory_flags2 ${_dir_flags_var_name})
      #MESSAGE("_directory_flags2 ${_directory_flags2}" )
	  FOREACH(item ${_directory_flags2})
		STRING(CONFIGURE -D@item@ _flag @ONLY ESCAPE_QUOTES)
		STRING(REPLACE \" \\\" _flag ${_flag})
        LIST(APPEND ${_out_compile_flags} ${_flag})
      ENDFOREACH(item)
    ENDIF(CMAKE_BUILD_TYPE)
    
  ELSE(CMAKE_COMPILER_IS_GNUCXX)
    ## TODO ... ? or does it work out of the box 
  ENDIF(CMAKE_COMPILER_IS_GNUCXX)
  
  GET_DIRECTORY_PROPERTY(DIRINC INCLUDE_DIRECTORIES )
  FOREACH(item ${DIRINC})
    LIST(APPEND ${_out_compile_flags} "${_PCH_include_prefix}${item}")
  ENDFOREACH(item)
  
  GET_DIRECTORY_PROPERTY(_directory_flags COMPILE_DEFINITIONS)
  #MESSAGE("_directory_flags ${_directory_flags}" )
  FOREACH(item ${_directory_flags})
	STRING(CONFIGURE -D@item@ _flag @ONLY ESCAPE_QUOTES)
	STRING(REPLACE \" \\\" _flag ${_flag})
    LIST(APPEND ${_out_compile_flags} ${_flag})
  ENDFOREACH(item)
  #MESSAGE("Flags: ${${_out_compile_flags}}")
  LIST(APPEND ${_out_compile_flags} ${CMAKE_CXX_FLAGS} )

  SEPARATE_ARGUMENTS(${_out_compile_flags})

  #MESSAGE("PCH flags: ${${_out_compile_flags}}")

ENDMACRO(_PCH_GET_COMPILE_FLAGS)


MACRO(_PCH_WRITE_PCHDEP_CXX _targetName _include_file _dephelp)

  _EXPAND_PCH_OUTPUT_DIR()
  SET(${_dephelp} "${PCH_OUTPUT_DIR}/${_targetName}_pch_dephelp.cxx")
  IF(${CMAKE_CURRENT_SOURCE_DIR}/${_include_file} IS_NEWER_THAN ${${_dephelp}})
    FILE(WRITE  ${${_dephelp}}
"#include \"${CMAKE_CURRENT_SOURCE_DIR}/${_include_file}\" 
int testfunction()
{
    return 0;
}
"
      )
  ENDIF()
  IF(DISTCLEAN_ENABLED)
	ADD_FILE_TO_DISTCLEAN(${${_dephelp}})
  ENDIF()

ENDMACRO(_PCH_WRITE_PCHDEP_CXX )

MACRO(_PCH_GET_COMPILE_COMMAND out_command _input _output)

	FILE(TO_NATIVE_PATH ${_input} _native_input)
	FILE(TO_NATIVE_PATH ${_output} _native_output)
	

	IF(CMAKE_COMPILER_IS_GNUCXX)
          IF(CMAKE_CXX_COMPILER_ARG1)
	    # remove leading space in compiler argument
            STRING(REGEX REPLACE "^ +" "" pchsupport_compiler_cxx_arg1 ${CMAKE_CXX_COMPILER_ARG1})

	    SET(${out_command} 
	      ${CMAKE_CXX_COMPILER} ${pchsupport_compiler_cxx_arg1} ${_compile_FLAGS}	-x c++-header -c -o ${_output} ${_input} 
	      )
	  ELSE(CMAKE_CXX_COMPILER_ARG1)
	    SET(${out_command} 
	      ${CMAKE_CXX_COMPILER}  ${_compile_FLAGS}	-x c++-header -c -o ${_output} ${_input} 
	      )
          ENDIF(CMAKE_CXX_COMPILER_ARG1)
	ELSE(CMAKE_COMPILER_IS_GNUCXX)
		
		SET(_dummy_str "#include <${_input}>")
		FILE(WRITE ${CMAKE_CURRENT_BINARY_DIR}/pch_dummy.cpp ${_dummy_str})
	
		SET(${out_command} 
			${CMAKE_CXX_COMPILER} ${_compile_FLAGS} /c /Fp${_native_output} /Yc${_native_input} pch_dummy.cpp
		)	
		#/out:${_output}

	ENDIF(CMAKE_COMPILER_IS_GNUCXX)
	
ENDMACRO(_PCH_GET_COMPILE_COMMAND )



MACRO(_PCH_GET_TARGET_COMPILE_FLAGS _cflags  _header_name _pch_path _dowarn )

  FILE(TO_NATIVE_PATH ${_pch_path} _native_pch_path)
  
  IF(CMAKE_COMPILER_IS_GNUCXX)
    # for use with distcc and gcc >4.0.1 if preprocessed files are accessible
    # on all remote machines set
    # PCH_ADDITIONAL_COMPILER_FLAGS to -fpch-preprocess
    # if you want warnings for invalid header files (which is very inconvenient
    # if you have different versions of the headers for different build types
    # you may set _pch_dowarn
    STRING(REGEX REPLACE "\\.gch$" "" _pch_name ${_pch_path})
    IF (_dowarn)
      SET(${_cflags} "${PCH_ADDITIONAL_COMPILER_FLAGS} -include ${_pch_name} -Winvalid-pch " )
    ELSE (_dowarn)
      SET(${_cflags} "${PCH_ADDITIONAL_COMPILER_FLAGS} -include ${_pch_name} " )
    ENDIF (_dowarn)
  ELSE(CMAKE_COMPILER_IS_GNUCXX)
    
    set(${_cflags} "/Fp${_native_pch_path} /Yu${_header_name}" )	
    
  ENDIF(CMAKE_COMPILER_IS_GNUCXX)	
  
ENDMACRO(_PCH_GET_TARGET_COMPILE_FLAGS )

MACRO(GET_PRECOMPILED_HEADER_OUTPUT _targetName _input _output)
  _EXPAND_PCH_OUTPUT_DIR()
  # TODO: use _path, too
  GET_FILENAME_COMPONENT(_name ${_input} NAME)
  GET_FILENAME_COMPONENT(_path ${_input} PATH)
  SET(_output "${PCH_OUTPUT_DIR}/${_targetName}_${_name}.gch")
ENDMACRO(GET_PRECOMPILED_HEADER_OUTPUT _targetName _input)

# @brief Adds existing (local or global) PCH to a target.
# @param _targetName Target to attach PCH to.
# @param _input Path to header used as PCH.
# @param _pch_output_to_use Path to GCH file.
# @param _pchTarget Target name which was passed as "PCH target name" to GENERATE_PRECOMPILED_HEADER.
#                   It may be the same as _targetName, if PCH was generated previously for _targetName.

MACRO(ADD_PRECOMPILED_HEADER_TO_TARGET _targetName _input _pch_output_to_use _pchTarget)
   
  # to do: test whether compiler flags match between target  _targetName
  # and _pch_output_to_use
  GET_FILENAME_COMPONENT(_name ${_input} NAME)

  IF( "${ARGN}" STREQUAL "0")
    SET(_dowarn 0)
  ELSE( "${ARGN}" STREQUAL "0")
    SET(_dowarn 1)
  ENDIF("${ARGN}" STREQUAL "0")


  _PCH_GET_TARGET_COMPILE_FLAGS(_target_pch_cflags ${_name} ${_pch_output_to_use} ${_dowarn})
  GET_TARGET_PROPERTY(_target_cflags ${_targetName} COMPILE_FLAGS)
  IF(NOT _target_cflags)
	SET(_target_cflags " ")
  ENDIF()
  #MESSAGE("Set flags ${_target_pch_cflags} ${_target_cflags} to ${_targetName} " )
  SET_TARGET_PROPERTIES(${_targetName} 
    PROPERTIES	
    COMPILE_FLAGS "${_target_pch_cflags} ${_target_cflags}"
    )

  #ADD_CUSTOM_TARGET(pch_Generate_${_targetName}
  #  DEPENDS	${_pch_output_to_use} 
  #  )
  
  ADD_DEPENDENCIES(${_targetName} pch_Generate_${_pchTarget} )
  
ENDMACRO(ADD_PRECOMPILED_HEADER_TO_TARGET)

# @brief Creates PCH (GCH) without attaching it to a target. 
# @param _targetName shall be an existing target name, which will become "PCH target name".
# @param _input Path to header to use as PCH.
# @return _output_var Path to generated GCH.
# Creates top-level target pch_Generate_${_targetName}
# Note that although _targetName is later used solely to identify the GCH,
#  it _shall_ exist and be buildable. Moreover, it's type (static/dynamic)
#  determines type of generated GCH, coz' PIC and non-PIC GCH are not interchangeble

MACRO(GENERATE_PRECOMPILED_HEADER _targetName _input _output_var)

  IF( "${ARGN}" STREQUAL "0")
    SET(_dowarn 0)
  ELSE( "${ARGN}" STREQUAL "0")
    SET(_dowarn 1)
  ENDIF("${ARGN}" STREQUAL "0")

  SET(_PCH_current_target ${_targetName})

  GET_FILENAME_COMPONENT(_name ${_input} NAME)
  GET_FILENAME_COMPONENT(_path ${_input} PATH)
  GET_PRECOMPILED_HEADER_OUTPUT(${_targetName} ${_input} _output)

  SET(${_output_var} ${_output})
  SET_TARGET_PROPERTIES(${_targetName} 
	PROPERTIES 
	PCH_OUTPUT ${_output}
	PCH_NAME ${_input})

  GET_FILENAME_COMPONENT(_outdir ${_output} PATH )

  GET_TARGET_PROPERTY(_targetType ${_PCH_current_target} TYPE)
   _PCH_WRITE_PCHDEP_CXX(${_targetName} ${_input} _pch_dephelp_cxx)

  IF(${_targetType} STREQUAL SHARED_LIBRARY)
    ADD_LIBRARY(${_targetName}_pch_dephelp SHARED ${_pch_dephelp_cxx} )
  ELSE(${_targetType} STREQUAL SHARED_LIBRARY)
    ADD_LIBRARY(${_targetName}_pch_dephelp STATIC ${_pch_dephelp_cxx})
  ENDIF(${_targetType} STREQUAL SHARED_LIBRARY)

  _EXPAND_PCH_OUTPUT_DIR()
  # TODO: set output dir of ${_targetName}_pch_dephelp
  SET_TARGET_PROPERTIES(${_targetName}_pch_dephelp 
	PROPERTIES 
	LIBRARY_OUTPUT_DIRECTORY "${PCH_OUTPUT_DIR}"
	ARCHIVE_OUTPUT_DIRECTORY "${PCH_OUTPUT_DIR}"
	)

  FILE(MAKE_DIRECTORY ${_outdir})


  _PCH_GET_COMPILE_FLAGS(_compile_FLAGS)
  
  #MESSAGE("_compile_FLAGS: ${_compile_FLAGS}")
  #message("COMMAND ${CMAKE_CXX_COMPILER}	${_compile_FLAGS} -x c++-header -c -o ${_output} ${_input}")
 
  GET_FILENAME_COMPONENT(_f1 ${CMAKE_CURRENT_BINARY_DIR}/${_name} ABSOLUTE)
  GET_FILENAME_COMPONENT(_input_abspath ${_input} ABSOLUTE)
  IF(NOT ${_f1} STREQUAL ${_input_abspath})
    SET_SOURCE_FILES_PROPERTIES(${CMAKE_CURRENT_BINARY_DIR}/${_name} PROPERTIES GENERATED 1)
    ADD_CUSTOM_COMMAND(
     OUTPUT	${CMAKE_CURRENT_BINARY_DIR}/${_name} 
     COMMAND ${CMAKE_COMMAND} -E copy  ${_input_abspath} ${CMAKE_CURRENT_BINARY_DIR}/${_name} # ensure same directory! Required by gcc
     DEPENDS ${_input_abspath}
    )
    #MESSAGE(STATUS "Will copy PCH ${_input_abspath} to ${CMAKE_CURRENT_BINARY_DIR}/${_name}")
  ENDIF(NOT ${_f1} STREQUAL ${_input_abspath})

  _PCH_GET_COMPILE_COMMAND(_command  ${CMAKE_CURRENT_BINARY_DIR}/${_name} ${_output})
  
  #message(${_input} )
  #message("_output ${_output}")

  ADD_CUSTOM_COMMAND(
    OUTPUT ${_output}
    COMMAND ${_command}
    DEPENDS ${_input} ${CMAKE_CURRENT_BINARY_DIR}/${_name} ${_targetName}_pch_dephelp
	)

  ADD_CUSTOM_TARGET(
	pch_Generate_${_targetName}
	DEPENDS ${_output}
	)

ENDMACRO(GENERATE_PRECOMPILED_HEADER _targetName _input _output_var)

# @brief Creates PCH and attaches it to target
# @param _targetName Target to attach PCH to. "PCH target name" will be the same
# @param _input Path to header to use as PCH.

MACRO(ADD_PRECOMPILED_HEADER _targetName _input)
  IF( "${ARGN}" STREQUAL "0")
    SET(_dowarn 0)
  ELSE( "${ARGN}" STREQUAL "0")
    SET(_dowarn 1)
  ENDIF("${ARGN}" STREQUAL "0")

  #MESSAGE("GENERATE_PRECOMPILED_HEADER ${_targetName} ${_input} ${_dowarn}")
  GENERATE_PRECOMPILED_HEADER(${_targetName} ${_input} _output ${_dowarn})
  #MESSAGE("ADD_PRECOMPILED_HEADER_TO_TARGET ${_targetName} ${_input}  ${_output} ${_dowarn}")
  ADD_PRECOMPILED_HEADER_TO_TARGET(${_targetName} ${_input} ${_output} ${_targetName} ${_dowarn})
ENDMACRO(ADD_PRECOMPILED_HEADER)

# @brief Attaches an existing global GCH (created via GENERATE_PRECOMPILED_HEADER to an existing target
# @param _targetName Target to attach to.
# @param _pchTarget "PCH target name" (Target passed to GENERATE_PRECOMPILED_HEADER)
# Note that both targets must be either static or dynamic, otherwise PCH will fail.

MACRO(ADD_GLOBAL_PRECOMPILED_HEADER _targetName _pchTarget)
  IF( "${ARGN}" STREQUAL "0")
    SET(_dowarn 0)
  ELSE( "${ARGN}" STREQUAL "0")
    SET(_dowarn 1)
  ENDIF("${ARGN}" STREQUAL "0")

  GET_TARGET_PROPERTY(_pch_output ${_pchTarget} PCH_OUTPUT)
  GET_TARGET_PROPERTY(_pch_input ${_pchTarget} PCH_NAME)
  #message("Adding PCH ${_pch_output} (${_pch_input}) to target ${_targetName}")
  ADD_PRECOMPILED_HEADER_TO_TARGET(${_targetName} ${_pch_input} ${_pch_output} ${_pchTarget} ${_dowarn})
ENDMACRO(ADD_GLOBAL_PRECOMPILED_HEADER)

# Generates the use of precompiled in a target,
# without using depency targets (2 extra for each target)
# Using Visual, must also add ${_targetName}_pch to sources
# Not needed by Xcode

MACRO(GET_NATIVE_PRECOMPILED_HEADER _targetName _input)

	if(CMAKE_GENERATOR MATCHES Visual*)

		SET(_dummy_str "#include \"${_input}\"\n"
										"// This is required to suppress LNK4221.  Very annoying.\n"
										"void *g_${_targetName}Dummy = 0\;\n")

		# Use of cxx extension for generated files (as Qt does)
		SET(${_targetName}_pch ${CMAKE_CURRENT_BINARY_DIR}/${_targetName}_pch.cxx)
		if(EXISTS ${${_targetName}_pch})
			# Check if contents is the same, if not rewrite
			# todo
		else(EXISTS ${${_targetName}_pch})
			FILE(WRITE ${${_targetName}_pch} ${_dummy_str})
		endif(EXISTS ${${_targetName}_pch})
	endif(CMAKE_GENERATOR MATCHES Visual*)

ENDMACRO(GET_NATIVE_PRECOMPILED_HEADER)


MACRO(ADD_NATIVE_PRECOMPILED_HEADER _targetName _input)

	IF( "${ARGN}" STREQUAL "0")
		SET(_dowarn 0)
	ELSE( "${ARGN}" STREQUAL "0")
		SET(_dowarn 1)
	ENDIF("${ARGN}" STREQUAL "0")
	
	if(CMAKE_GENERATOR MATCHES Visual*)
		# Auto include the precompile (useful for moc processing, since the use of 
		# precompiled is specified at the target level
		# and I don't want to specifiy /F- for each moc/res/ui generated files (using Qt)

		GET_TARGET_PROPERTY(oldProps ${_targetName} COMPILE_FLAGS)
		if (${oldProps} MATCHES NOTFOUND)
			SET(oldProps "")
		endif(${oldProps} MATCHES NOTFOUND)

		SET(newProperties "${oldProps} /Yu\"${_input}\" /FI\"${_input}\"")
		SET_TARGET_PROPERTIES(${_targetName} PROPERTIES COMPILE_FLAGS "${newProperties}")
		
		#also inlude ${oldProps} to have the same compile options 
		SET_SOURCE_FILES_PROPERTIES(${${_targetName}_pch} PROPERTIES COMPILE_FLAGS "${oldProps} /Yc\"${_input}\"")
		
	else(CMAKE_GENERATOR MATCHES Visual*)
	
		if (CMAKE_GENERATOR MATCHES Xcode)
			# For Xcode, cmake needs my patch to process
			# GCC_PREFIX_HEADER and GCC_PRECOMPILE_PREFIX_HEADER as target properties
			
			GET_TARGET_PROPERTY(oldProps ${_targetName} COMPILE_FLAGS)
			if (${oldProps} MATCHES NOTFOUND)
				SET(oldProps "")
			endif(${oldProps} MATCHES NOTFOUND)

			# When buiding out of the tree, precompiled may not be located
			# Use full path instead.
			GET_FILENAME_COMPONENT(fullPath ${_input} ABSOLUTE)

			SET_TARGET_PROPERTIES(${_targetName} PROPERTIES XCODE_ATTRIBUTE_GCC_PREFIX_HEADER "${fullPath}")
			SET_TARGET_PROPERTIES(${_targetName} PROPERTIES XCODE_ATTRIBUTE_GCC_PRECOMPILE_PREFIX_HEADER "YES")

		else (CMAKE_GENERATOR MATCHES Xcode)

			#Fallback to the "old" precompiled suppport
			#ADD_PRECOMPILED_HEADER(${_targetName} ${_input} ${_dowarn})
		endif(CMAKE_GENERATOR MATCHES Xcode)
	endif(CMAKE_GENERATOR MATCHES Visual*)

ENDMACRO(ADD_NATIVE_PRECOMPILED_HEADER)

MACRO(_EXPAND_PCH_OUTPUT_DIR)
  IF("${PCH_OUTPUT_DIR}" STREQUAL "")
	SET(PCH_OUTPUT_DIR ".")
  ENDIF()
  IF(NOT IS_ABSOLUTE "${PCH_OUTPUT_DIR}")
	SET(PCH_OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/${PCH_OUTPUT_DIR}")
  ENDIF()
ENDMACRO(_EXPAND_PCH_OUTPUT_DIR)

IF(NOT PCH_ENABLED)
  SET(PCH_ENABLED 1 CACHE INTERNAL "True if PCH support has been enabled" FORCE)
  MESSAGE(STATUS "Enabled PCH support")
ENDIF()
