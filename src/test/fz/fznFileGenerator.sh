#!/bin/bash
readarray -t arr < <(find test -name \*.mzn );

for i in ${arr[@]}; do

z=${i%/*}
ii=${i##*/}
iii=${ii%.*}

if [ ! -d "$z/$iii" ]; then
	mkdir $z/$iii

fi


if [[ -z $(find $z -name \*.dzn) ]]
then

mzn2fzn -G jacop $i
for file in $z/*.fzn; do mv "$file" $z/$iii/"${file/*.fzn/$iii.fzn}"; done

fi

readarray -t arr2 < <(find $z -name \*.dzn)
for j in ${arr2[@]}; do
    mzn2fzn -G jacop $i -d $j
	path=${j%.*}
	filename=${path##*/}

	for file in $z/*.fzn; do mv "$file" $z/$iii/"${file/*.fzn/$filename.fzn}"; done
done

done
echo "-------------------------------------------------"
readarray -t arr3 < <(find $z -name \*.fzn)
	for k in ${arr3[@]};do

          start=$(date +%s )
	    out=$(java -cp ../../../../jacop-*.jar org.jacop.fz.Fz2jacop $k)
	  stop=$(date +%s )
    echo $out
	timesec=$(($stop-$start))

		result=$out
		diff <(echo $result) <(echo $out)
		#echo "Rezultat" $?

	i=0
	while [ $? == 0 -a $i != 4 ];
	   do
		out=$(java -cp ../../../../jacop-*.jar org.jacop.fz.Fz2jacop $k)
		diff <(echo $result) <(echo $out)
		let i++
		count=$i

	   done

	if [ $count -eq 4 ];	then

	   if [ $timesec -lt 15 ];then

			st=${k#*/*/}

			if [ ! -d "upTo5sec/${st%/*}" ]; then
		            mkdir -p upTo5sec/${st%/*}
			fi

			echo $out > upTo5sec/${st%.*}.out
  			#mv ${k%%/*}/${st%/*}/${st%.*}.fzn upTo5sec/${st%.*}.fzn
			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5sec/${st%.*}.fzn
		fi

	   if [ $timesec -gt 15 ] && [ $timesec -lt 80 ]  ;then
		   echo "wejście"
			st=${k#*/*/}

			if [ ! -d "upTo30sec/${st%/*}" ]; then
		            mkdir -p upTo30sec/${st%/*}
			fi

			echo $out > upTo30sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo30sec/${st%.*}.fzn
		fi

	   if [ $timesec -gt 80 ] && [ $timesec -le 120 ];then

			st=${k#*/*/}

			if [ ! -d "upTo1min/${st%/*}" ]; then
		            mkdir -p upTo1min/${st%/*}
			fi

			echo $out > upTo1min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1min/${st%.*}.fzn
		fi


	  if [ $timesec -ge 120 ] && [ $timesec -le 600 ];then

			st=${k#*/*/}

			if [ ! -d "upTo5min/${st%/*}" ]; then
		            mkdir -p upTo5min/${st%/*}
			fi

			echo $out > upTo5min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5min/${st%.*}.fzn
		fi

	  if [ $timesec -ge 600 ] && [ $timesec -le 1200 ];then

			st=${k#*/*/}

			if [ ! -d "upTo10min/${st%/*}" ]; then
		            mkdir -p upTo10min/${st%/*}
			fi

			echo $out > upTo10min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo10min/${st%.*}.fzn
		fi

	  if [ $timesec -ge 1200 ] && [ $timesec -le 5400 ];then

			st=${k#*/*/}

			if [ ! -d "upTo1hour/${st%/*}" ]; then
		            mkdir -p upTo1hour/${st%/*}
			fi

			echo $out > upTo1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1hour/${st%.*}.fzn
		fi

	  if [ $timesec -ge 5400 ] && [ $timesec -le 172800 ];then

			st=${k#*/*/}

			if [ ! -d "above1hour/${st%/*}" ]; then
		            mkdir -p above1hour/${st%/*}
			fi

			echo $out > above1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above1hour/${st%.*}.fzn
		fi




	fi

done





















