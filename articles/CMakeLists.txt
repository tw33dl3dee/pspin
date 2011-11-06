set(LATEX_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/output/tex)

file(GLOB INC_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} ../data/inc/* ../thesis/*.bst)

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
  INPUTS ${INC_FILES}
  BIBFILES ../thesis/thesis.bib
  DEFAULT_PDF MANGLE_TARGET_NAMES 
)

add_latex_document(paco-article.tex 
  INPUTS ${INC_FILES}
  DEPENDS graphics
  IMAGE_DIRS ../graphics
  BIBFILES ../thesis/thesis.bib
  DEFAULT_PDF MANGLE_TARGET_NAMES 
)

add_latex_document(paco-slides.tex 
  INPUTS ${INC_FILES}
  DEPENDS graphics
  IMAGE_DIRS ../graphics
  BIBFILES ../thesis/thesis.bib
  DEFAULT_PDF MANGLE_TARGET_NAMES 
)

add_latex_document(phd-proposals.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(phd-abstract.tex 
  INPUTS ${INC_FILES}
  BIBFILES ../thesis/thesis.bib  
  DEFAULT_PDF MANGLE_TARGET_NAMES
)
add_latex_document(phd-abstract-review.tex DEFAULT_PDF MANGLE_TARGET_NAMES)

add_latex_document(review.tex DEFAULT_PDF MANGLE_TARGET_NAMES)

# add_latex_document(techomag-article.tex
#   INPUTS ${INC_FILES}
#   IMAGE_DIRS ../graphics
#   DEFAULT_PDF MANGLE_TARGET_NAMES
# )

add_custom_target(articles ALL)
add_dependencies(articles
  report1_pdf report2_pdf report2-slides_pdf report3_pdf report3-slides_pdf review_pdf
  paco-thesis_pdf paco-article_pdf paco-slides_pdf
)

add_custom_target(phd ALL)
add_dependencies(phd phd-proposals_pdf phd-abstract_pdf phd-abstract-review_pdf)

add_custom_command(TARGET articles POST_BUILD
  COMMAND cp ${LATEX_OUTPUT_PATH}/*.pdf ${CMAKE_CURRENT_BINARY_DIR}/
)
add_custom_command(TARGET phd POST_BUILD
  COMMAND cp ${LATEX_OUTPUT_PATH}/*.pdf ${CMAKE_CURRENT_BINARY_DIR}/
)
