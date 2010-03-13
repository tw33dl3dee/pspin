set(CODEGEN_FILE pan.c)
set(PSPIN_SRC paremu.c state.c state.h state_hash.c state_hash.h bfs.c bfs.h)

set_source_files_properties(${PSPIN_SRC} PROPERTIES
  OBJECT_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/${CODEGEN_FILE}
)

include_directories(${MPI_INCLUDE_PATH})

add_definitions(-DCODEGEN_FILE=\"${CODEGEN_FILE}\" -DNODECOUNT=4 -DSTATE_PARTITION_HASH -USTATE_PARTITION_FIRST_PROC)

add_executable(pspin ${PSPIN_SRC})
target_link_libraries(pspin ${MPI_LIBRARIES})

enable_distclean(pspin)
