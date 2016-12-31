#!/bin/bash
readarray -t arr < <(find test -name \*.mzn );

for i in ${arr[@]}; do

z=${i%/*}
ii=${i##*/}
iii=${ii%.*}

if [ ! -d "$z/fzn$iii" ]; then
	mkdir $z/fzn$iii

fi


if [[ -z $(find $z -name \*.dzn) ]]
then

mzn2fzn -G jacop $i
for file in $z/*.fzn; do mv "$file" $z/fzn$iii/"${file/*.fzn/$iii.fzn}"; done

fi

readarray -t arr2 < <(find $z -name \*.dzn)
for j in ${arr2[@]}; do
    mzn2fzn -G jacop $i -d $j
	path=${j%.*}
	filename=${path##*/}

	for file in $z/*.fzn; do mv "$file" $z/fzn$iii/"${file/*.fzn/$filename.fzn}"; done
done

done