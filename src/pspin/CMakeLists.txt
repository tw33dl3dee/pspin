set(PROMELA_MODEL test.pml)

set(STATEGEN_FILE ${CMAKE_CURRENT_BINARY_DIR}/stategen.c)
set(PROMELA_FILE  ${CMAKE_CURRENT_SOURCE_DIR}/${PROMELA_MODEL})
set(PMLPARSE_DIR  ${CMAKE_CURRENT_SOURCE_DIR}/../pmlparse)

set(PSPIN_SRC state.c state.h state_hash.c state_hash.h bfs.c bfs.h)
set(PAREMU_SRC paremu.c)
set(PARMPI_SRC parmpi.c mpi_async.c mpi_async.h mpi_debug.c)

set(DEBUG_FLAGS STATE_DEBUG)
set(MPI_DEBUG_FLAGS ${DEBUG_FLAGS};MPI_DEBUG)

set_source_files_properties(${PSPIN_SRC} ${PAREMU_SRC} ${PARMPI} PROPERTIES
  OBJECT_DEPENDS ${STATEGEN_FILE}
)

add_custom_command(OUTPUT ${STATEGEN_FILE}
  DEPENDS ${PROMELA_FILE} ${PMLPARSE_DIR}/*.py*
  COMMAND ./pmlparse.py ${PROMELA_FILE} ${STATEGEN_FILE}
  WORKING_DIRECTORY ${PMLPARSE_DIR}
  COMMENT "Parsing ${PROMELA_MODEL}"
)

add_custom_command(OUTPUT ${PROMELA_MODEL}
  COMMAND echo "You must create symlink ${PROMELA_MODEL}" && exit 1
  COMMENT "Checking ${PROMELA_MODEL} existence"
)

set(MPI_TEST_NODE_COUNT 4)
add_custom_target(mpirun 
  COMMAND mpirun -n ${MPI_TEST_NODE_COUNT} ./pspin-mpi
  DEPENDS pspin-mpi
  COMMENT "Running ${MPI_TEST_NODE_COUNT} MPI nodes..."
)

include_directories(${MPI_INCLUDE_PATH})

add_definitions(-DSTATEGEN_FILE=\"${STATEGEN_FILE}\" -DNODECOUNT=4 -UENDSTATE -DSTATE_PARTITION_HASH -USTATE_PARTITION_FIRST_PROC)

add_executable(pspin-mpi ${PSPIN_SRC} ${PARMPI_SRC})
target_link_libraries(pspin-mpi ${MPI_LIBRARIES})
set_target_properties(pspin-mpi 
  PROPERTIES COMPILE_DEFINITIONS_DEBUG "${MPI_DEBUG_FLAGS}"
)
set_target_properties(pspin-mpi 
  PROPERTIES COMPILE_DEFINITIONS "MPI"
)

add_executable(pspin-emu ${PSPIN_SRC} ${PAREMU_SRC})
set_target_properties(pspin-emu 
  PROPERTIES COMPILE_DEFINITIONS_DEBUG "${DEBUG_FLAGS}"
)

enable_distclean(pspin)
