file(GLOB DIA_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.dia)

add_dia_files(dia-pdf ${DIA_FILES})
