add_custom_command(
  OUTPUT  report1.pdf report1.aux report1.log
  DEPENDS report1.tex
  COMMAND ${PDFLATEX_COMPILER}
  ARGS    report1.tex
)

add_custom_command(
  OUTPUT  report2-slides.pdf report2-slides.aux report2-slides.log
  DEPENDS report2-slides.tex
  COMMAND ${PDFLATEX_COMPILER}
  ARGS    report2-slides.tex
)

add_custom_target(articles ALL DEPENDS report1.pdf report2-slides.pdf)
add_dependencies(articles graphics)
