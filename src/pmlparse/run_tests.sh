#!/bin/sh

for T in ./t_*.py; do
	$T -v
done
