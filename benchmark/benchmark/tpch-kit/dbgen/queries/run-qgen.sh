#!/bin/bash

for q in {1..22}; do
	./qgen -d $q > "postgres/$q.sql"
done
