#!/bin/bash
#author: Mariusz Swierkot

# First make sure you copy src\main\minizinc\org\jacop\minizinc directory as jacop directory inside your minizinc installation ( share\minizinc ).
# Second run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository.
# Third execute this script in the directory where this script resides.

function timeCategory(){

readarray -t arr3 < <(find $z -name \*.fzn)
	for k in ${arr3[@]};do # i contains a relative path to a found mzn file.

        ii=${k##*/} # fzn filename with extension
        iii=${ii%.*} # fzn filename without extension

        start=$(date +%s ) # start time in seconds
    	   out=$(java -cp ../../../../jacop-*.jar org.jacop.fz.Fz2jacop $k) # Program Fz2jacop generate test result
        stop=$(date +%s )  # end time in seconds

        echo "$out"
	    timesec=$(($stop-$start))

		result=$out
		diff <(echo $result) <(echo $out)

        diffresult=$?

    	i=0
        count=0
	        while [ $diffresult == 0 -a $i != 1 ];
	        do
	    	  out=$(java -cp ../../../../jacop-*.jar org.jacop.fz.Fz2jacop $k) # Program Fz2jacop generate test result
		      diff <(echo $result) <(echo $out) # diff compare results test to find the difference between two results test
		      let i++
		      count=$i
            done

	if [ $count -eq 1 ];	then

	    if [ $timesec -lt 15 ];then

			st=${k#*/*/}

			if [ ! -d "upTo5sec/${st%/*}" ]; then
		            mkdir -p upTo5sec/${st%/*}
			fi

			echo "$out" > upTo5sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5sec/${st%.*}.fzn

		fi

	    if [ $timesec -gt 15 ] && [ $timesec -lt 80 ]  ;then

			st=${k#*/*/}

			if [ ! -d "upTo30sec/${st%/*}" ]; then
		            mkdir -p upTo30sec/${st%/*}
			fi

			echo "$out" > upTo30sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo30sec/${st%.*}.fzn
		fi

        if [ $timesec -gt 80 ] && [ $timesec -le 120 ];then

			st=${k#*/*/}

			if [ ! -d "upTo1min/${st%/*}" ]; then
		            mkdir -p upTo1min/${st%/*}
			fi

			echo "$out" > upTo1min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1min/${st%.*}.fzn
		fi


        if [ $timesec -ge 120 ] && [ $timesec -le 600 ];then

			st=${k#*/*/}

			if [ ! -d "upTo5min/${st%/*}" ]; then
		            mkdir -p upTo5min/${st%/*}
			fi

			echo "$out" > upTo5min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5min/${st%.*}.fzn
		fi

        if [ $timesec -ge 600 ] && [ $timesec -le 1200 ];then

			st=${k#*/*/}

			if [ ! -d "upTo10min/${st%/*}" ]; then
		            mkdir -p upTo10min/${st%/*}
			fi

			echo "$out" > upTo10min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo10min/${st%.*}.fzn
		fi

        if [ $timesec -ge 1200 ] && [ $timesec -le 5400 ];then

			st=${k#*/*/}

			if [ ! -d "upTo1hour/${st%/*}" ]; then
		            mkdir -p upTo1hour/${st%/*}
			fi

			echo "$out" > upTo1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1hour/${st%.*}.fzn
		fi

	    if [ $timesec -ge 5400 ] && [ $timesec -le 7200 ];then

			st=${k#*/*/}

			if [ ! -d "above1hour/${st%/*}" ]; then
		            mkdir -p above1hour/${st%/*}
			fi

			echo "$out" > above1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above1hour/${st%.*}.fzn
	fi

    else {
            echo "Flaky test"
            st=${k#*/*/}

			if [ ! -d "flakyTests/${st%/*}" ]; then
		            mkdir -p flakyTests/${st%/*}
			fi

			echo "$out" > flakyTests/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn flakyTests/${st%.*}.fzn
         }

	fi
#fi
done

}


#main
echo "Start test: "
readarray -t arr < <(find test -name \*.mzn );

for i in ${arr[@]}; do

z=${i%/*} # directory that contains mzn filename
ii=${i##*/} # mzn filename with extension
iii=${ii%.*} # mzn filename without extension

# Creating a temporary directory in the same directory as mzn file has resided using the mzn file without extension as the name.

if [ ! -d "$z/${z#*/}" ]; then
	mkdir $z/${z#*/}

fi


if [[ -z $(find $z -name \*.dzn) ]]
then


   if [[ -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $iii.fzn 2>/dev/null ) || -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $iii.out 2>/dev/null) ]]
        then
        # Generating fzn files and moving to the temporary directory

        mzn2fzn -G jacop $i
        for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$iii.fzn}"; done

        timeCategory

   fi
fi

readarray -t arr2 < <(find $z -name \*.dzn)
for j in ${arr2[@]}; do # j contains a relative path to dzn file.

    path=${j%.*}
	filename=${path##*/}

 if [[ -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $filename.fzn 2>/dev/null )  ||  -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $filename.out 2>/dev/null ) ]]
 then
    # Generating fzn files and moving to the temporary directory
    mzn2fzn -G jacop $i -d $j
	for file in $z/*.fzn; do mv "$file" $z/$iii/"${file/*.fzn/$filename.fzn}"; done

 fi
done

      timeCategory
done