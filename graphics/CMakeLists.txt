file(GLOB DIA_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.dia)
file(GLOB SVG_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.svg)
file(GLOB PIC_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.pic)

add_dia_files(dia-pdf ${DIA_FILES})
add_svg_files(svg-pdf ${SVG_FILES})
add_pic_files(pic-pdf ${PIC_FILES})

add_custom_target(graphics)
add_dependencies(graphics dia-pdf svg-pdf pic-pdf)
