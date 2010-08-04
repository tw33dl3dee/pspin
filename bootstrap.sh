#!/bin/sh

(cd src/pspin && ./set-model.sh $(ls -1 models/*.pml | head -n1))

while ! (cmake . && make) ; do : ; done
