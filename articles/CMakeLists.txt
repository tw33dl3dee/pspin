add_dia_files(state-partition.dia idef0-codegen.dia)

add_custom_target(dia-pdf ALL DEPENDS state-partition.pdf idef0-codegen.pdf)
