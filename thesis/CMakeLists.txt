set(LATEX_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/output/tex)

file(GLOB TEX_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} [0-9][0-9]-*.tex *.cls *.sty *.clo *.bst ../data/*.tex)

add_latex_document(thesis.tex 
  INPUTS ${TEX_FILES}
  DEPENDS graphics
  IMAGE_DIRS ../graphics ../data/plots
  BIBFILES thesis.bib
  DEFAULT_PDF MANGLE_TARGET_NAMES
)

add_custom_target(thesis ALL)
add_dependencies(thesis thesis_pdf)

add_custom_command(TARGET thesis POST_BUILD
  COMMAND cp ${LATEX_OUTPUT_PATH}/thesis.pdf ${CMAKE_CURRENT_BINARY_DIR}/
)

add_custom_target(texclean ALL rm -f *.aux *.toc *.log *.out *.bbl *.blg)
