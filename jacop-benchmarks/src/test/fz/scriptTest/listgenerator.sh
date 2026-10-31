#!/bin/bash

rm list.txt
readarray -t arr < <(find * -maxdepth 1 -type d)
for i in ${arr[@]}; do

if [[ -n $(find $i -name *.dzn) ]]
then
    find $i -name *.dzn | sed 's/\.dzn$//' >> list.txt
fi

 if [[ ! -n $(find $i -name *.dzn) && -n $(find $i -name *.mzn) ]]
 then
   find $i -name *.mzn | sed 's/\.mzn$//' >> list.txt
fi

 if [[ ! -n $(find $i -name *.dzn) && ! -n $(find $i -name *.mzn) && -n $(find $i -name *.fzn) ]]
 then

   find $i -name *.fzn | sed 's/\.fzn$//' >> list.txt

fi

done
#sort list.txt -o list.txt