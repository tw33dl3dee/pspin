add_custom_command(
  OUTPUT  report1.pdf report1.aux report1.log
  DEPENDS report1.tex
  COMMAND ${PDFLATEX_COMPILER}
  ARGS    report1.tex
)

add_custom_target(articles DEPENDS report1.pdf)
add_dependencies(articles dia-pdf)
