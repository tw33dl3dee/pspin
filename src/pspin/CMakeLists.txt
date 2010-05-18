set(PROMELA_MODEL test.pml)

set(STATEGEN_FILE ${CMAKE_CURRENT_BINARY_DIR}/stategen.c)
set(PROMELA_FILE  ${CMAKE_CURRENT_SOURCE_DIR}/${PROMELA_MODEL})
set(PMLPARSE_DIR  ${CMAKE_CURRENT_SOURCE_DIR}/../pmlparse)

set(PSPIN_SRC state.c state.h state_hash.c state_hash.h bfs.c bfs.h)
set(PAREMU_SRC paremu.c)
set(PARMPI_SRC parmpi.c mpi_async.c mpi_async.h mpi_debug.c)

set(REMOTE_RUN_SCRIPT tools/run-mpi-job.sh)
set(REMOTE_INPUT ${STATEGEN_FILE} ${PSPIN_SRC} ${PARMPI_SRC} Makefile.bare pspin.job ${REMOTE_RUN_SCRIPT})
set(REMOTE_OUTPUT "pspin.std*")

set(MPI_HOST mpi)
set(MPI_HOST_REMOTE_PATH work/pspin)

set(DEBUG_FLAGS STATE_DEBUG;HASH_DEBUG)
set(MPI_DEBUG_FLAGS ${DEBUG_FLAGS};MPI_DEBUG)

set_source_files_properties(${PSPIN_SRC} ${PAREMU_SRC} ${PARMPI_SRC} PROPERTIES
  OBJECT_DEPENDS ${STATEGEN_FILE}
)

if (NOT EXISTS ${PROMELA_FILE})
  message(FATAL_ERROR "You must create symlink ${PROMELA_MODEL} to a file with PROMELA model")
endif()

add_custom_command(OUTPUT ${STATEGEN_FILE}
  DEPENDS ${PROMELA_FILE} ${PMLPARSE_DIR}/*.py*
  COMMAND ./pmlparse.py ${PROMELA_FILE} ${STATEGEN_FILE} $(PP)
  WORKING_DIRECTORY ${PMLPARSE_DIR}
  COMMENT "Parsing ${PROMELA_MODEL}"
)

set(MPI_TEST_NODE_COUNT 4)
add_custom_target(mpilocal
  COMMAND mpirun -n ${MPI_TEST_NODE_COUNT} ./pspin-mpi
  DEPENDS pspin-mpi
  COMMENT "Running ${MPI_TEST_NODE_COUNT} MPI nodes..."
)

add_custom_target(mpiupload
  COMMAND scp ${REMOTE_INPUT} ${MPI_HOST}:${MPI_HOST_REMOTE_PATH}
  DEPENDS ${REMOTE_INPUT}
  COMMENT "Uploading files to job server..."
)

add_custom_target(mpisubmit
  COMMAND ssh ${MPI_HOST} 'cd ${MPI_HOST_REMOTE_PATH} && ./run-mpi-job.sh'
  COMMENT "Submitting job..."
)

add_custom_target(mpidownload
  COMMAND scp ${MPI_HOST}:${MPI_HOST_REMOTE_PATH}/${REMOTE_OUTPUT} ./
  COMMAND tools/process-results.sh
  COMMENT "Downloading results..."
)

add_custom_target(mpirun)

add_dependencies(mpirun mpidownload)
add_dependencies(mpidownload mpisubmit)
add_dependencies(mpisubmit mpiupload)

include_directories(${MPI_INCLUDE_PATH})

add_definitions(-DSTATEGEN_FILE=\"${STATEGEN_FILE}\")

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
set_target_properties(pspin-emu 
  PROPERTIES COMPILE_DEFINITIONS "EMULATION"
)

enable_distclean(pspin)
