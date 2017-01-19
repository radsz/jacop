#!/bin/bash
#author: Mariusz Swierkot

# First make sure you copy src\main\minizinc\org\jacop\minizinc directory as jacop directory inside your minizinc installation ( share\minizinc ).
# Second run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository.
# Third execute this script in the directory where this script resides.
removingEmptyDirectories(){
    find test -mindepth 1 -type d -empty -delete
}

removingDznMznFiles() {

dznCounter=0

readarray -t arr < <(find test -name \*.dzn);
for i in ${arr[@]}; do

let dznCounter++
      readarray -t arr1 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour flakyTests  -name \*.fzn);


            ii=${i#*/}
            iii=${ii%.*}

        for j in ${arr1[@]}; do

            jj=${j#*/}
            jjj=${jj%.*}

            if [ "$iii" == "$jjj" ]; then
            rm $i
            let dznCounter--

        fi
        done
done
      ii=${i#*/}
      iii=${ii%/*}

    if [ $dznCounter == 0 ] ; then
        if [ "$iii" != "" ];then
            rm -r test/$iii/
        fi
    fi

}

function diffDifference(){

    if [ $diffresult -ne 0 ];then

           count=5
           out="First computing result: `echo -e "\n$result"` `echo -e "\n\nSecond computing result:"` `echo -e "\n$out"`"

    fi

}

function timeCategory( ) {

readarray -t arr3 < <(find $z -name \*.fzn)
	for k in ${arr3[@]};do # i contains a relative path to a found mzn file.

        ii=${k##*/} # fzn filename with extension
        iii=${ii%.*} # fzn filename without extension

        echo "Computing first result for $k"
        start=$(date +%s ) # start time in seconds
        # First timeout is set to 3600 seconds
    	   out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop -t 3600 $k) # Program Fz2jacop generate test result
        echo "$out"
        stop=$(date +%s )  # end time in seconds

        # TODO, if out contains text below then the timeout occurred and the test should be automatically categorized to above 1hour test
        # =====UNKNOWN=====
        # %% =====TIME-OUT=====

	    timesec=$(($stop-$start))

		result=$out
		diff <(echo $result) <(echo $out)

        diffresult=$?
        i=0
        count=0

        if [ "${out%\%*}" == "%" ];then

           diffresult=1
           count=5

        fi

        if [ "${out#*%}" == "% =====TIME-OUT=====" ];then

            diffresult=1
            count=4
            timesec=6000
            out="=====UNKNOWN===== `echo -e "\n%% =====TIME-OUT====="`"

        fi


	        while [ $diffresult == 0 -a $i != 4 ];
	        do
	          echo "Computing again result for $k"
	          # Second timeout is set to 7200 seconds to avoid situation of the timeout when the first one did not timeout.
	    	  out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop -t 7200 $k) # Program Fz2jacop generate test result
		      diff <(echo $result) <(echo $out) # diff compare results test to find the difference between two results test

		      diffresult=$?
		      let i++
		      count=$i
              diffDifference

            done

	if [ $count -eq 4 ];	then

	    if [ $timesec -lt 15 ];then

            echo "Problem $k was classified in time category upTo5sec"
			st=${k#*/*/}
			if [ ! -d "upTo5sec/${st%/*}" ]; then
		            mkdir -p upTo5sec/${st%/*}
			fi
			echo "$out" > upTo5sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5sec/${st%.*}.fzn
            removingDznMznFiles
		fi

	    if [ $timesec -gt 15 ] && [ $timesec -lt 80 ]  ;then

            echo "Problem $k was classified in time category upTo30sec"
			st=${k#*/*/}

			if [ ! -d "upTo30sec/${st%/*}" ]; then
		            mkdir -p upTo30sec/${st%/*}
			fi

			echo "$out" > upTo30sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo30sec/${st%.*}.fzn
  			removingDznMznFiles
		fi

        if [ $timesec -gt 80 ] && [ $timesec -le 120 ];then

            echo "Problem $k was classified in time category upTo1min"
			st=${k#*/*/}

			if [ ! -d "upTo1min/${st%/*}" ]; then
		            mkdir -p upTo1min/${st%/*}
			fi

			echo "$out" > upTo1min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1min/${st%.*}.fzn
  			removingDznMznFiles
		fi


        if [ $timesec -ge 120 ] && [ $timesec -le 600 ];then

            echo "Problem $k was classified in time category upTo5min"
			st=${k#*/*/}

			if [ ! -d "upTo5min/${st%/*}" ]; then
		            mkdir -p upTo5min/${st%/*}
			fi

			echo "$out" > upTo5min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5min/${st%.*}.fzn
  			removingDznMznFiles
		fi

        if [ $timesec -ge 600 ] && [ $timesec -le 1200 ];then

            echo "Problem $k was classified in time category upTo10min"
			st=${k#*/*/}

			if [ ! -d "upTo10min/${st%/*}" ]; then
		            mkdir -p upTo10min/${st%/*}
			fi

			echo "$out" > upTo10min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo10min/${st%.*}.fzn
  			removingDznMznFiles
		fi

        if [ $timesec -ge 1200 ] && [ $timesec -le 5400 ];then

            echo "Problem $k was classified in time category upTo1hour"
			st=${k#*/*/}

			if [ ! -d "upTo1hour/${st%/*}" ]; then
		            mkdir -p upTo1hour/${st%/*}
			fi

			echo "$out" > upTo1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1hour/${st%.*}.fzn
  			removingDznMznFiles
		fi

	    if [ $timesec -ge 5400 ];then

            echo "Problem $k was classified in time category above1hour"
			st=${k#*/*/}

			if [ ! -d "above1hour/${st%/*}" ]; then
		            mkdir -p above1hour/${st%/*}
			fi

			echo "$out" > above1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above1hour/${st%.*}.fzn
  			removingDznMznFiles
	fi

    else {

            if [ "${out%\%*}" == "%" ];then
                echo "Problem $k was classified as errors test"
            st=${k#*/*/}

			if [ ! -d "errors/${st%/*}" ]; then
		            mkdir -p errors/${st%/*}
			fi

			echo "$out" > errors/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn errors/${st%.*}.fzn
  			removingDznMznFiles
            else

            echo "Problem $k was classified as flaky test"
            st=${k#*/*/}

			if [ ! -d "flakyTests/${st%/*}" ]; then
		            mkdir -p flakyTests/${st%/*}
			fi

			echo "$out" > flakyTests/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn flakyTests/${st%.*}.fzn
  			removingDznMznFiles

        fi
        }
	fi

done

}


#main
echo "Start test: "

removingDznMznFiles
readarray -t arr4 < <(find test -maxdepth 2 -name \*.fzn);
for i in ${arr4[@]}; do
      readarray -t arr5 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour flakyTests  -name \*.fzn);
        ii=${i#*/}
        iii=${ii%.*}
        for j in ${arr5[@]}; do
        jj=${j#*/}
        jjj=${jj%.*}
            if [ "$iii" == "$jjj" ]; then
            rm $i
        fi
        done
done

counter=0
counter2=0
readarray -t arr3 < <(find test -maxdepth 2 -name \*.fzn);

for i in ${arr3[@]}; do

  let counter2++
  z=${i%/*} # directory that contains mzn filename

    if [ ! -d "$z/${z#*/}" ]; then
	   mkdir "$z/${z#*/}"

    fi

     path=${i%.*}
     filename=${path##*/}

	 for file in "$z/$filename.fzn"; do mv "$file" "$z/${z#*/}/${file/*.fzn/$filename.fzn}"; done
done
tab=${arr3[@]}
    if [ -z ${arr3[0]} ]; then
        let counter2++
    fi


while [ $counter -lt $counter2 ]
do
if [ -z $z ]; then

    readarray -t arr3 < <(find test -maxdepth 3 -name \*.fzn);
    if [ -z ${arr3[0]} ]; then

    let counter2--
    fi

    for i in ${arr3[@]}; do
       z=${i%/*}
       let counter2++

    done

    if [ ! -z $z ]; then

            let counter++
            timeCategory

    fi
else

     let counter++
     if [ -d $z ]; then
            timeCategory
            z=""
     fi
fi
done

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

   if [[ -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo10min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $iii.fzn 2>/dev/null ) || -z $(find upTo5sec/$iii upTo30sec/$iii upTo1min/$iii upTo5min/$iii upTo10min/$iii upTo1hour/$iii above1hour/$iii flakyTests/$iii -name $iii.out 2>/dev/null) ]]
   then
        # Generating fzn files and moving to the temporary directory
        echo "Generating fzn file for $i"
        mzn2fzn -G jacop $i
        for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$iii.fzn}"; done
        rm $i
        timeCategory

   fi
fi

readarray -t arr2 < <(find $z -name \*.dzn)
for j in ${arr2[@]}; do # j contains a relative path to dzn file.

    path=${j%.*}
	filename=${path##*/}

  if [[ -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.fzn 2>/dev/null )  ||  -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.out 2>/dev/null )  ]]
  then
     # Generating fzn files and moving to the temporary directory
     echo "Generating fzn file for $i and data file $j"
     mzn2fzn -G jacop $i -d $j
	 for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$filename.fzn}"; done
  fi
done
    timeCategory
done

removingEmptyDirectories


