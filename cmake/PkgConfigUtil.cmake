# - Utils to be used with FindPkgConfig module.
#
# Macro:
#   ADD_PKGCONFIG_MODULES module1 module2...

#
# Add include_directories() and add_definitions() for specified packages (prevoiously found by FindPkgConfig)
# Prototype:
#    ADD_PKGCONFIG_MODULES(module1 [module2 ...])
# Parameters:
#    module1, module2... Names of packages to be added
#

MACRO(ADD_PKGCONFIG_MODULES)
  FOREACH(_prefix ${ARGN})
	INCLUDE_DIRECTORIES(${${_prefix}_INCLUDE_DIRS})
	ADD_DEFINITIONS(${${_prefix}_OTHER_CFLAGS})
  ENDFOREACH(_prefix)
ENDMACRO(ADD_PKGCONFIG_MODULES)
