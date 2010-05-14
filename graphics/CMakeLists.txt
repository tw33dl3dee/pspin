file(GLOB DIA_FILES RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.dia)

add_dia_files(dia-pdf ${DIA_FILES})

# pic2plot -f 0.012 -F HersheyCyrillic -Tps $< | epstopdf --filter --outfile=$@
# inkscape -D -z --file=image.svg --export-pdf=image.pdf --export-latex
 