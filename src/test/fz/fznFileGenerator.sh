#!/bin/bash
#author: Mariusz Swierkot

# First make sure you copy src\main\minizinc\org\jacop\minizinc directory as jacop directory inside your minizinc installation ( share\minizinc ).
# Second run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository.
# Third execute this script in the directory where this script resides.
removingEmptyDirectories(){

    find test -type d -empty -delete -mindepth 1
}



function diffDifference(){

if [ $diffresult -ne 0 ];then

            count=5
            out="First computing result: `echo -e "\n$result"` `echo -e "\n\nSecond computing result:"` `echo -e "\n$out"`"

        fi

}

function timeCategory( ) {

readarray -t arr3 < <(find $z -name \*.fzn 2>/dev/null)

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
		diff <(echo $result) <(echo $out) #diff compare results test to find the difference between two results test

        diffresult=$?
        i=0
        count=0

        if [ "${out%\%*}" == "%" ];then

           diffresult=1
           count=5

        fi

        if [ "${out#*%}" == "% =====TIME-OUT=====" ];then
            echo "Out result" ${out#*%}
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


             if ls test/${st%/*}/*.mzn 2>/dev/null; then
                if [ ! -d upTo5sec/${st%/*}/dznFolder ]; then
		            mkdir -p upTo5sec/${st%/*}/dznFolder
			    fi
			 fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo5sec/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo5sec/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l ` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}  #remove dzn files
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo5sec/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
                fi

            fi
		fi

	    if [ $timesec -gt 15 ] && [ $timesec -lt 80 ]  ;then

            echo "Problem $k was classified in time category upTo30sec"
			st=${k#*/*/}

			if [ ! -d "upTo30sec/${st%/*}" ]; then
		            mkdir -p upTo30sec/${st%/*}
			fi

			echo "$out" > upTo30sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo30sec/${st%.*}.fzn

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d upTo30sec/${st%/*}/dznFolder ]; then
		            mkdir -p upTo30sec/${st%/*}/dznFolder
			    fi
			 fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo30sec/${st%/*}/dznFolder/  #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo30sec/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0  ]; then
                     rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo30sec/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
                fi
            fi

		fi

        if [ $timesec -gt 80 ] && [ $timesec -le 120 ];then

            echo "Problem $k was classified in time category upTo1min"
			st=${k#*/*/}

			if [ ! -d "upTo1min/${st%/*}" ]; then
		            mkdir -p upTo1min/${st%/*}
			fi

			echo "$out" > upTo1min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1min/${st%.*}.fzn

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d upTo1min/${st%/*}/dznFolder ]; then
		            mkdir -p upTo1min/${st%/*}/dznFolder
			    fi
			fi

                if ls test/${st%/*}/*.dzn 2>/dev/null; then
                    mv ${k%%/*}/${st%.*}.dzn upTo1min/${st%/*}/dznFolder/ #move dzn file to time category
                    cp ${k%%/*}/${st%/*}/*.mzn upTo1min/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                      rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo1min/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
                fi
             fi
		fi


        if [ $timesec -ge 120 ] && [ $timesec -le 600 ];then

            echo "Problem $k was classified in time category upTo5min"
			st=${k#*/*/}

			if [ ! -d "upTo5min/${st%/*}" ]; then
		            mkdir -p upTo5min/${st%/*}
			fi

			echo "$out" > upTo5min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5min/${st%.*}.fzn

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
                if [ ! -d upTo5min/${st%/*}/dznFolder ]; then
		            mkdir -p upTo5min/${st%/*}/dznFolder
			    fi
			fi

            if ls test/${st%/*}/*.dzn 2>/dev/null ; then

                mv ${k%%/*}/${st%.*}.dzn upTo5min/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo5min/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo5min/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
                fi
             fi

		fi

        if [ $timesec -ge 600 ] && [ $timesec -le 1200 ];then

            echo "Problem $k was classified in time category upTo10min"
			st=${k#*/*/}

			if [ ! -d "upTo10min/${st%/*}" ]; then
		            mkdir -p upTo10min/${st%/*}
			fi

			echo "$out" > upTo10min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo10min/${st%.*}.fzn


  		if ls test/${st%/*}/*.mzn 2>/dev/null; then
  			if [ ! -d upTo10min/${st%/*}/dznFolder ]; then

		            mkdir -p upTo10min/${st%/*}/dznFolder

		    fi
	    fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo10min/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo10min/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l`  == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo10min/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
                fi
            fi

		fi

        if [ $timesec -ge 1200 ] && [ $timesec -le 5400 ];then

            echo "Problem $k was classified in time category upTo1hour"
			st=${k#*/*/}

			if [ ! -d "upTo1hour/${st%/*}" ]; then
		            mkdir -p upTo1hour/${st%/*}
			fi

			echo "$out" > upTo1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1hour/${st%.*}.fzn

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
      			if [ ! -d upTo1hour/${st%/*}/dznFolder ]; then
		            mkdir -p upTo1hour/${st%/*}/dznFolder

			    fi
			fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo1hour/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo1hour/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ] ; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo10min/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
            fi
         fi


		fi

	    if [ $timesec -ge 5400 ];then

            echo "Problem $k was classified in time category above1hour"
			st=${k#*/*/}

			if [ ! -d "above1hour/${st%/*}" ]; then
		            mkdir -p above1hour/${st%/*}
			fi

			echo "$out" > above1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above1hour/${st%.*}.fzn

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
      			if [ ! -d above1hour/${st%/*}/dznFolder ]; then
		            mkdir -p above1hour/${st%/*}/dznFolder
			    fi
			fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn above1hour/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn above1hour/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn above1hour/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
            fi
         fi


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

            if ls test/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d errors/${st%/*}/dznFolder ]; then
		            mkdir -p errors/${st%/*}/dznFolder
			    fi
			fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn errors/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn errors/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn errors/${st%/*}/dznFolder/${stt%.*}.mzn
                    rm -r ${k%%/*}/${st%/*}/
            fi
         fi

            else

            echo "Problem $k was classified as flaky test"
            st=${k#*/*/}

			if [ ! -d "flakyTests/${st%/*}" ]; then
		            mkdir -p flakyTests/${st%/*}
			fi

			echo "$out" > flakyTests/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn flakyTests/${st%.*}.fzn

  			if ls test/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d flakyTests/${st%/*}/dznFolder ]; then
		            mkdir -p flakyTests/${st%/*}/dznFolder
			    fi
			fi

            if ls test/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn flakyTests/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn flakyTests/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l test/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else


                if ls test/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn flakyTests/${st%/*}/dznFolder/${stt%.*}.mzn #copy mzn to time category
                    rm -r ${k%%/*}/${st%/*}/
                fi
            fi
         fi

        }
	fi

done

}


#main
file="../../../target/jacop-*-SNAPSHOT.jar"
if [ ! -e $file ]; then
    echo "Jar file don't exist."
    echo "Run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository."
    exit
fi

readarray -t arr4 < <(find test -name \*.fzn);
for i in ${arr4[@]}; do
      readarray -t arr5 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour flakyTests  -name \*.fzn );

        for j in ${arr5[@]}; do

            if [ "${i##*/}" == "${j##*/}" ]; then
                rm -r ${i%/*}/${i##*/}
            fi
        done
done


counter=0
counter2=0
readarray -t arr3 < <(find test -mindepth 2 -maxdepth 2 -name \*.fzn 2>/dev/null);

for t in ${arr3[@]}; do

let counter2++
    z=${t%/*} # directory that contains fzn filename
    if [ ! -d "$z/${z#*/}" ]; then
	   mkdir "$z/${z#*/}"
    fi

     path=${t%.*}
     filename=${path##*/}

	 for file in "$z/$filename.fzn"; do mv "$file" "$z/${z#*/}/${file/*.fzn/$filename.fzn}"; done
done
#tab=${arr3[@]}
if [ -z ${arr3[0]} ]; then
     let counter2++
fi

while [ $counter -lt $counter2 ]
do
if [ -z $z ]; then
    readarray -t arr3 < <(find test -mindepth 3 -maxdepth 3 -name \*.fzn );
    if [ -z ${arr3[0]} ]; then
    let counter2--
    fi
    for t in ${arr3[@]}; do
       z=${t%/*}
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
removingEmptyDirectories
readarray -t arr < <(find test -mindepth 2 -maxdepth 2 -name \*.mzn 2>/dev/null);

for i in ${arr[@]}; do
z=${i%/*} # directory that contains mzn filename


if [ `ls -l $z/*.mzn 2>/dev/null | wc -l` != 1  ]; then # Tests number *.mzn files in a directory.
    echo "Only one *.mzn file in the same directory" $z
    exit

fi

ii=${i##*/} # mzn filename with extension
iii=${ii%.*} # mzn filename without extension

# Creating a temporary directory in the same directory as mzn file has resided using the mzn file without extension as the name.
if [ ! -d "$z/${z#*/}" ]; then
	mkdir $z/${z#*/}
fi

if [[ -z $(find  $z -mindepth 1 -maxdepth 1 -name \*.dzn 2>/dev/null) ]]
then

   if [[ -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $iii.fzn 2>/dev/null ) || -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $iii.out 2>/dev/null) ]]
   then

        # Generating fzn files and moving to the temporary directory
        echo "Generatig fzn file for $i"
        mzn2fzn -G jacop $i
        for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$iii.fzn}"; done
        timeCategory
    else
     rm -r $z

   fi
fi
count1=0
readarray -t arr2 < <(find $z -mindepth 1 -maxdepth 1 -name \*.dzn 2>/dev/null)
    arraysize=${#arr2[@]}

for j in ${arr2[@]}; do # j contains a relative path to dzn file.
    path=${j%.*}
	filename=${path##*/}

  if [[ -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.fzn 2>/dev/null )  ||  -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.out 2>/dev/null )  ]]
  then
     # Generating fzn files and moving to the temporary directory
     echo "Generatig fzn file for $i and data file $j"
     mzn2fzn -G jacop $i -d $j
	 for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$filename.fzn}"; done
  else

      let count1++
      rm $z/$filename.dzn
  fi
    if [ "$count1" -eq "$arraysize" ]; then
       rm -r $z
    fi
done
     timeCategory
done

    #removingEmptyDirectories
