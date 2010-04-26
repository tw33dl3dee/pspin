project(pspin)
cmake_minimum_required(VERSION 2.6)

set(CMAKE_BUILD_TYPE Debug)

set(PACKAGE "pspin")
set(PRODUCT "pspin")
set(VERSION "0.1")

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
include(TargetDistclean)

set(CMAKE_C_FLAGS         "${CMAKE_C_FLAGS}         -std=c99")
set(CMAKE_C_FLAGS_DEBUG   "${CMAKE_C_FLAGS_DEBUG}   -Wall -Wno-unused -DDEBUG -g")
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -UDEBUG -O3")

find_package(MPI REQUIRED)
find_package(Dia REQUIRED)

add_subdirectory(src/pspin)
add_subdirectory(graphics)
add_subdirectory(articles)

find_package(Ctags)
if(CTAGS_FOUND AND CTAGS_FLAVOR MATCHES Exuberant)
  set(TAGS_DIR ${CMAKE_SOURCE_DIR})
  add_custom_target(ctags
	${CTAGS_EXECUTABLE} -R src
	WORKING_DIRECTORY ${TAGS_DIR}
	COMMENT "Generating tags..."
	)	
  add_custom_target(etags
	${CTAGS_EXECUTABLE} -eR src
	WORKING_DIRECTORY ${TAGS_DIR}
	COMMENT "Generating Emacs tags..."
	)
endif()

enable_distclean()
generate_distclean_target()

include(FeatureSummary)
print_enabled_features()
