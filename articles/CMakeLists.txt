set(LATEX_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/output/tex)

file(GLOB INC_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} ../data/inc/*)

add_latex_document(report1.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(report2.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(report2-slides.tex 
  DEPENDS graphics
  IMAGE_DIRS ../graphics
  DEFAULT_PDF MANGLE_TARGET_NAMES
)

add_latex_document(report3.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(report3-slides.tex 
  INPUTS ${INC_FILES}
  DEPENDS graphics
  IMAGE_DIRS ../graphics ../data/plots
  DEFAULT_PDF MANGLE_TARGET_NAMES
)

add_latex_document(paco-thesis.tex 
  BIBFILES ../thesis/thesis.bib
  DEFAULT_PDF MANGLE_TARGET_NAMES 
)

add_latex_document(review.tex DEFAULT_PDF MANGLE_TARGET_NAMES)

add_custom_target(articles ALL)
add_dependencies(articles report1_pdf report2_pdf report2-slides_pdf report3_pdf report3-slides_pdf review_pdf)

add_custom_command(TARGET articles POST_BUILD
  COMMAND cp ${LATEX_OUTPUT_PATH}/*.pdf ${CMAKE_CURRENT_BINARY_DIR}/
)
