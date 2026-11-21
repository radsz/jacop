#!/bin/bash
#find * -name *.fzn -o -name *.mzn | sed 's/\.fzn$//' | sed 's/\.mzn$//' | sort> list.txt
find * -name *.fzn | sed 's,^[^/]*/,, ; s/\.fzn$//' | sort > listtmp.txt
#find * -name *.fzn | sed 's/\.fzn$//' | sort > list.txt
find * -name *.fzn | sed 's/\.fzn$//' > list.txt
