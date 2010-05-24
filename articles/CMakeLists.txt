set(LATEX_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/output/tex)

add_latex_document(report1.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(report2.tex DEFAULT_PDF MANGLE_TARGET_NAMES)
add_latex_document(report2-slides.tex 
  DEPENDS graphics
  IMAGE_DIRS ../graphics
  DEFAULT_PDF MANGLE_TARGET_NAMES
)

add_latex_document(review.tex DEFAULT_PDF MANGLE_TARGET_NAMES)

add_custom_target(articles ALL)
add_dependencies(articles report1_pdf report2_pdf report2-slides_pdf review_pdf)
