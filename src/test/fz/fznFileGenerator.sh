#!/bin/bash
#author: Mariusz Swierkot

# First make sure you copy src\main\minizinc\org\jacop\minizinc directory as jacop directory inside your minizinc installation ( share\minizinc ).
# Second run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository.
# Third execute this script in the directory where this script resides.

TEMP=`getopt -o h::,d:,t:,s: --long directory:,timeout:,fznsize:,help:: -n 'fznFilegGenerator.sh' -- "$@" `

if [ "$TEMP" = " --" ] && [ "$#" != 0  ];then
    echo "Try './fznFileGenerator --help' for more information---."
    exit;
fi

eval set -- "$TEMP"

setDirectory="x"
FZNSIZE=0
while true ; do
    case "$1" in
        -d|--directory)
            case "$2" in
                "") shift 2;;
                *) DIR=$2 ; shift 2;;
            esac ;;
	    -t|--timeout)

            case "$2" in
                "") shift 2;;
                *)
                TIMEOUT=$2 ;   shift 2 ;;
            esac ;;

        -s|--fznsize)
           case "$2" in
                "") shift 2;;
                *) FZNSIZE=$2 ; setDirectory="setDirectory"; shift 2 ;;
            esac ;;
        -h|--help)
            case "$2" in
                "") if [ "$#" -ne 3 ]; then
                      exit;
                    else
                      echo "  -d,  --directory "
                      echo "  -t,  --timeout   upto5sec, upto30sec, upto1min,  upto5min, upto10min, upto30min, upto1hour"
                      echo "  -s,  --fznsize - Specify file size limit in MB."
                      echo "  -h,  --help "
                      exit;
                    fi
            esac;;

        --) shift ; break ;;
        *) echo "Internal error!!!" ; exit 1 ;;
    esac
done

if [ -z "$DIR" ];then #if parameter($directory) doesn't exist
  if [ "$(ls -A --ignore="README" test)" ]; then
    folderPath="test"
  else
    echo "Directory test is Empty"
    exit;
  fi
else
    if [ ! -d "$DIR" ];then
      echo "Directory $DIR does't exist"
      exit;
    else
      if [ "$(ls -A $DIR)" ]; then
        p=$DIR
        folderPath=${p##*/}
      else
        echo "$DIR is Empty"
        exit;
    fi

    fi
fi
removingEmptyDirectories(){

    find $folderPath -type d -empty -delete -mindepth 1 2>/dev/null
}



function diffDifference(){

if [ $diffresult -ne 0 ];then

            count=5
            out="First computing result: `echo -e "\n$result"` `echo -e "\n\nSecond computing result:"` `echo -e "\n$out"`"

        fi

}

function above()
{

category=${pa,,}
    echo "Problem $k was classified in time category above${category#*o}"
    echo "_________________________________________________________________________________"
			st=${k#*/*/}

			if [ ! -d "above${category#*o}/${st%/*}" ]; then
		            mkdir -p above${category#*o}/${st%/*}
			fi

			echo "$out" > above${category#*o}/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above${category#*o}/${st%.*}.fzn 2>/dev/null
            cp ${k%/*/*}/options.opt above${category#*o}/${st%/*}/ 2>/dev/null #copy options.opt to time category
            if ls $folderPath/${st%/*}/*.mzn >/dev/null 2>&1; then
#               echo "ls 1"
                if [ ! -d above${category#*o}/${st%/*}/dznFolder ]; then
		            mkdir -p above${category#*o}/${st%/*}/dznFolder
			    fi
			 fi

            if ls $folderPath/${st%/*}/*.dzn >/dev/null 2>&1; then

                mv ${k%%/*}/${st%.*}.dzn above${category#*o}/${st%/*}/dznFolder/ >/dev/null #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn above${category#*o}/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn >/dev/null 2>&1 | wc -l ` == 0  ]; then

                    rm -r ${k%%/*}/${st%/*}  #remove *.dzn files
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn >/dev/null 2>&1; then

                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn above${category#*o}/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.dzn files
                fi

            fi

}

function sizeFznFiles
{
readarray -t arr3 < <(find $z -name \*.fzn 2>/dev/null)

	for k in ${arr3[@]};do

        if [ $setDirectory == "setDirectory" ]; then
            re='^[0-9]+$'
        if ! [[ $FZNSIZE =~ $re ]] ; then
            echo "error: Not a number" >&2; exit 1
        fi
            sizeFznFile=$[1048576*FZNSIZE]
        else
            sizeFznFile=15728640
        fi

        file_size=`stat -c %s "$k"`
        if [ $file_size -le $sizeFznFile ]; then #1197181
             file_size=`stat -c %s "$k"`
        else
            echo "The file $k is larger than $sizeFznFile"
            rm $k;

        fi

done

}






function timeCategory
 {

 folderPath=$1

if [ "${TIMEOUT,,}" == "upto5sec" ] || [ "${TIMEOUT,,}" == "upto30sec" ] || [ "${TIMEOUT,,}" == "upto1min" ] || [ "${TIMEOUT,,}" == "upto5min" ] || [ "${TIMEOUT,,}" == "upto10min" ] || [ "${TIMEOUT,,}" == "upto1hour" ];
then
   echo "setTime" $TIMEOUT
   pa=$TIMEOUT
else
    if [ "$TIMEOUT" != "" ];then
        echo "Try './fznFileGenerator --help' for more information.1"
        exit;
    else
        pa="x"
    fi
fi
readarray -t arr3 < <(find $z -name \*.fzn 2>/dev/null)

	for k in ${arr3[@]};do # k contains a relative path to a found mzn file.
        ii=${k##*/} # *.fzn filename with extension
        iii=${ii%.*} # *.fzn filename without extension

        echo "Computing first result for $k"
        start=$(date +%s ) # start time in seconds
        # First timeout is set to 3600 seconds

        if [ ${pa,,} == "upto5sec" ] || [ ${pa,,} == "upto30sec" ] || [ ${pa,,} == "upto1min" ] || [ ${pa,,} == "upto5min" ] || [ ${pa,,} == "upto10min" ] || [ ${pa,,} == "upto1hour" ]
        then
            case "${pa,,}" in #Sets the maximum time to complete the test
                "upto5sec") time="-t 15" ;;
                "upto30sec") time="-t 80" ;;
                "upto1min") time="-t 120" ;;
                "upto5min") time="-t 600" ;;
                "upto10min") time="-t 1200" ;;
                "upto1hour") time="-t 5400" ;;

            esac

            else
             echo "Set time 3600sec"
             time="-t 3600"
            fi

          if [ -f ${k%/*/*}/options.opt ]; then

              opt=`sed -n 1p ${k%/*/*}/options.opt`
              out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop $time $opt $k) # Program Fz2jacop generate test result
              echo "$out"
          else
              out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop $time $k) # Program Fz2jacop generate test result
              echo "$out"
          fi
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

        if [ "${out:0:2}" == "%%" ];then
           diffresult=1
           count=5
        fi

        if [ "${out#*%}" == "% =====TIME-OUT=====" ];then
          case "${pa,,}" in #Sets the maximum time to complete the test
            "upto5sec") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upto30sec") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upto1min") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upto5min") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upto10min") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001  
			            out="" ;;
            "upto1hour") above ${pa,,}
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            *){
            echo "Out result" ${out#*%}
            diffresult=1
            count=4
            timesec=6000
            out="=====UNKNOWN===== `echo -e "\n%% =====TIME-OUT====="`"
            }

            esac
        fi
            while [ $diffresult == 0 -a $i != 4 ];
	        do
	          echo "Computing again result for $k"
	          # Second timeout is set to 7200 seconds to avoid situation of the timeout when the first one did not timeout.

            if [ -f ${k%/*/*}/options.opt ]; then
              opt=`sed -n 1p ${k%/*/*}/options.opt`
              out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop $time $opt $k) # Program Fz2jacop generate test result
              echo "$out"
          else
              out=$(java -cp ../../../target/jacop-*-SNAPSHOT.jar org.jacop.fz.Fz2jacop $time $k) # Program Fz2jacop generate test result
              echo "$out"
          fi
		      diff <(echo $result) <(echo $out) # diff compare results test to find the difference between two results test

		      diffresult=$?
		      let i++
		      count=$i
              diffDifference

            done
if [ "${out#*%}" == "% =====TIME-OUT=====" ];then
          case "$pa" in
            "upTo5sec") above $pa
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upTo30sec") above $pa
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upTo1min") above $pa
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upTo5min") above $pa
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            "upTo10min") above $pa
                        diffresult=1
                        count=4
                        timesec=6001  
			            out="" ;;

            "upTo1hour") above $pa
                        diffresult=1
                        count=4
                        timesec=6001
                        out="" ;;
            *){
            echo "Out result-" ${out#*%}
            diffresult=1
            count=4
            timesec=6000
            out="=====UNKNOWN===== `echo -e "\n%% =====TIME-OUT====="`"
            }

            esac
        fi

	if [ $count -eq 4 ];	then

	    if [ $timesec -lt 15 ];then

            echo "Problem $k was classified in time category upTo5sec"
			st=${k#*/*/}

			if [ ! -d "upTo5sec/${st%/*}" ]; then
		            mkdir -p upTo5sec/${st%/*}
			fi

			echo "$out" > upTo5sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5sec/${st%.*}.fzn #move *.fzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                if [ ! -d upTo5sec/${st%/*}/dznFolder ]; then
		            mkdir -p upTo5sec/${st%/*}/dznFolder
			    fi
			 fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo5sec/${st%/*}/dznFolder/ #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo5sec/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l ` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}  #remove *.dzn files
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo5sec/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file
                fi

            fi
        #timeParameter $pa
		fi

	    if [ $timesec -gt 15 ] && [ $timesec -lt 80 ]  ;then

            echo "Problem $k was classified in time category upTo30sec"
			st=${k#*/*/}

			if [ ! -d "upTo30sec/${st%/*}" ]; then
		            mkdir -p upTo30sec/${st%/*}
			fi

			echo "$out" > upTo30sec/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo30sec/${st%.*}.fzn #move *.dzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d upTo30sec/${st%/*}/dznFolder ]; then
		            mkdir -p upTo30sec/${st%/*}/dznFolder
			    fi
			 fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo30sec/${st%/*}/dznFolder/  #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo30sec/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0  ]; then
                     rm -r ${k%%/*}/${st%/*} #remove *.dzn files
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo30sec/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file
                fi
            fi
        #timeParameter $pa
		fi

        if [ $timesec -gt 80 ] && [ $timesec -le 120 ];then

            echo "Problem $k was classified in time category upTo1min"
			st=${k#*/*/}

			if [ ! -d "upTo1min/${st%/*}" ]; then
		            mkdir -p upTo1min/${st%/*}
			fi

			echo "$out" > upTo1min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1min/${st%.*}.fzn #move *.fzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d upTo1min/${st%/*}/dznFolder ]; then
		            mkdir -p upTo1min/${st%/*}/dznFolder
			    fi
			fi

                if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then
                    mv ${k%%/*}/${st%.*}.dzn upTo1min/${st%/*}/dznFolder/ #move *.dzn file to time category
                    cp ${k%%/*}/${st%/*}/*.mzn upTo1min/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                      rm -r ${k%%/*}/${st%/*} #remove *.dzn files
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo1min/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file from test folder
                fi
             fi
             #timeParameter $pa
		fi


        if [ $timesec -ge 120 ] && [ $timesec -le 600 ];then

            echo "Problem $k was classified in time category upTo5min"
			st=${k#*/*/}

			if [ ! -d "upTo5min/${st%/*}" ]; then
		            mkdir -p upTo5min/${st%/*}
			fi

			echo "$out" > upTo5min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo5min/${st%.*}.fzn #move mv file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                if [ ! -d upTo5min/${st%/*}/dznFolder ]; then
		            mkdir -p upTo5min/${st%/*}/dznFolder
			    fi
			fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null ; then

                mv ${k%%/*}/${st%.*}.dzn upTo5min/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo5min/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo5min/${st%/*}/dznFolder/${stt%.*}.mzn #copy mzn to time category
                    rm -r ${k%%/*}/${st%/*}/
                fi
             fi
            #timeParameter $pa
		fi

        if [ $timesec -ge 600 ] && [ $timesec -le 1200 ];then

            echo "Problem $k was classified in time category upTo10min"
			st=${k#*/*/}

			if [ ! -d "upTo10min/${st%/*}" ]; then
		            mkdir -p upTo10min/${st%/*}
			fi

			echo "$out" > upTo10min/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo10min/${st%.*}.fzn #move fzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

  		if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
  			if [ ! -d upTo10min/${st%/*}/dznFolder ]; then

		            mkdir -p upTo10min/${st%/*}/dznFolder

		    fi
	    fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo10min/${st%/*}/dznFolder/ #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo10min/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l`  == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo10min/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn file to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file
                fi
            fi
        #timeParameter $pa
		fi

        if [ $timesec -ge 1200 ] && [ $timesec -le 5400 ];then

            echo "Problem $k was classified in time category upTo1hour"
			st=${k#*/*/}

			if [ ! -d "upTo1hour/${st%/*}" ]; then
		            mkdir -p upTo1hour/${st%/*}
			fi

			echo "$out" > upTo1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn upTo1hour/${st%.*}.fzn #move *.fzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
      			if [ ! -d upTo1hour/${st%/*}/dznFolder ]; then
		            mkdir -p upTo1hour/${st%/*}/dznFolder

			    fi
			fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn upTo1hour/${st%/*}/dznFolder/ #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn upTo1hour/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ] ; then
                    rm -r ${k%%/*}/${st%/*} #remove *.dzn file
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn upTo10min/${st%/*}/dznFolder/${stt%.*}.mzn #move *.dzn file to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file
            fi
         fi

        #timeParameter $pa
		fi

	    if [ $timesec -ge 5400 ] && [ $timesec -ne 6001 ];
	    then

            echo "Problem $k was classified in time category above1hour-"
			st=${k#*/*/}

			if [ ! -d "above1hour/${st%/*}" ]; then
		            mkdir -p above1hour/${st%/*}
			fi

			echo "$out" > above1hour/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn above1hour/${st%.*}.fzn #move *.dzn file to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
      			if [ ! -d above1hour/${st%/*}/dznFolder ]; then
		            mkdir -p above1hour/${st%/*}/dznFolder
			    fi
			fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn above1hour/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn above1hour/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*}
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn above1hour/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn file to time category
                    rm -r ${k%%/*}/${st%/*}/ #copy mzn to time category
            fi
         fi


	fi

    else {
            if [ "${out:0:2}" == "%%" ];then
                echo "Problem $k was classified as errors test"
            st=${k#*/*/}

			if [ ! -d "errors/${st%/*}" ]; then
    	            mkdir -p errors/${st%/*}
			fi

			echo "$out" > errors/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn errors/${st%.*}.fzn #move *.mzn file to time category

            if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d errors/${st%/*}/dznFolder ]; then
		            mkdir -p errors/${st%/*}/dznFolder
			    fi
			fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn errors/${st%/*}/dznFolder/ #move *.dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn errors/${st%/*}/dznFolder/ #copy *.mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*} #remove *.dzn file
                fi

            else

                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
                    stt=${st#*/}
                    cp ${k%%/*}/${st%/*}/${stt%.*}.mzn errors/${st%/*}/dznFolder/${stt%.*}.mzn #copy *.mzn to time category
                    rm -r ${k%%/*}/${st%/*}/ #remove *.mzn file
            fi
         fi

            else

            echo "Problem $k was classified as flaky test"
            st=${k#*/*/}

			if [ ! -d "flakyTests/${st%/*}" ]; then
		            mkdir -p flakyTests/${st%/*}
			fi

			echo "$out" > flakyTests/${st%.*}.out
  			mv ${k%%/*}/$(echo "$k" | cut -d / -f 2)/${st%.*}.fzn flakyTests/${st%.*}.fzn #move *.fzn to time category
            cp ${k%/*/*}/options.opt upTo5sec/${st%/*}/ 2>/dev/null #copy options.opt to time category

  			if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
  			    if [ ! -d flakyTests/${st%/*}/dznFolder ]; then
		            mkdir -p flakyTests/${st%/*}/dznFolder
			    fi
			fi

            if ls $folderPath/${st%/*}/*.dzn 2>/dev/null; then

                mv ${k%%/*}/${st%.*}.dzn flakyTests/${st%/*}/dznFolder/ #move dzn file to time category
                cp ${k%%/*}/${st%/*}/*.mzn flakyTests/${st%/*}/dznFolder/ #copy mzn to time category

                if [ `ls -l $folderPath/${st%/*}/*.dzn 2>/dev/null | wc -l` == 0 ]; then
                    rm -r ${k%%/*}/${st%/*} #remove *.mzn file
                fi

            else


                if ls $folderPath/${st%/*}/*.mzn 2>/dev/null; then
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
mzicnpath="/usr/share/minizinc/jacop"
if [ ! -e $mzincpath ]; then
    echo "Path /usr/share/minizinc/jacop don't exist"
    echo "copy JaCoP minizinc directory (jacop/src/main/minizinc) into the minizinc
          directory of your minizinc installation and rename it to jacop.
          This directory is located, for example on Mac at /usr/local/share/minizinc."
    exit

fi

file="../../../target/jacop-*-SNAPSHOT.jar"
if [ ! -e $file ]; then
    echo "Jar file don't exist."
    echo "Run command mvn package to create a jar file for jacop inside target directory. Copy this jar one level higher than jacop git repository."
    exit
fi



readarray -t arr4 < <(find $folderPath -name \*.fzn);
for i in ${arr4[@]}; do

      readarray -t arr5 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour flakyTests  -name \*.fzn );

        for j in ${arr5[@]}; do

            if [ "${i#*/}" == "${j#*/}" ]; then
                echo "Test $i exist in time category"
                rm -r ${i%/*}/${i##*/}
            fi
        done
done


counter=0
counter2=0
readarray -t arr3 < <(find $folderPath -mindepth 2 -maxdepth 2 -name \*.fzn 2>/dev/null);

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

if [ -z ${arr3[0]} ]; then
     let counter2++
fi

while [ $counter -lt $counter2 ]
do
if [ -z $z ]; then
    readarray -t arr3 < <(find $folderPath -mindepth 3 -maxdepth 3 -name \*.fzn );
    if [ -z ${arr3[0]} ]; then
    let counter2--
    fi
    for t in ${arr3[@]}; do
       z=${t%/*}
       let counter2++
    done

    if [ ! -z $z ]; then
           let counter++
           sizeFznFiles
           timeCategory $folderPath $2

    fi
else

        let counter++
        if [ -d $z ]; then
        sizeFznFiles
        timeCategory $folderPath $2
        z=""
        fi
fi


done
removingEmptyDirectories
readarray -t arr < <(find $folderPath -mindepth 2 -maxdepth 2 -name \*.mzn 2>/dev/null);

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

        echo "Generatig fzn file for $i"
        mzn2fzn -G jacop $i

        readarray -t arr4 < <(find $folderPath -name \*.fzn);
        for i in ${arr4[@]}; do

            readarray -t arr5 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour flakyTests  -name \*.fzn );

                for j in ${arr5[@]}; do

                    if [ "${i#*/}" == "${j#*/}" ]; then
                        echo "Test $i exist in time category"
                    rm -r ${i%/*}/${i##*/}
                fi
            done
        done

    b=${i##*/} # *.fzn filename with extension
    bb=${b%.*} # *.mzn filename without extension
     findRes=$(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $iii.fzn 2>/dev/null)
     diff $findRes ${i%/*}/$iii.fzn 2>/dev/null
     diffre=$?
     if [[ -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $iii.fzn 2>/dev/null ) || -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $iii.out 2>/dev/null) || $diffre -ne 0 ]]
     then
            for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$iii.fzn}" 2>/dev/null ; done
            sizeFznFiles
            timeCategory $folderPath $2
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
     echo "Generatig fzn file for $i and data file $j"
     mzn2fzn -G jacop $i -d $j

        xx=${j#*/%.*}
        xxx=${xx%.*}.fzn

 readarray -t arr4 < <(find $folderPath -name \*.fzn);
        for ii in ${arr4[@]}; do

            readarray -t arr5 < <(find upTo5sec upTo30sec upTo1min upTo5min upTo10min upTo1hour above1hour  -name \*.fzn );

                for j in ${arr5[@]}; do

                    if [ "${xxx#*/}" == "${j#*/}" ]; then
                        echo "Test $xxx exist in time category"
                    rm -r ${ii%/*}/${ii##*/}
                fi
            done
        done

    b=${i##*/} # *.fzn filename with extension
    bb=${b%.*} # *.mzn filename without extension

     findRes=$(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.fzn 2>/dev/null)
     diff $findRes ${i%/*}/$iii.fzn 2>/dev/null
     diffre=$?


  if [[ -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.fzn 2>/dev/null )  ||  -z $(find upTo5sec/${z#*/} upTo30sec/${z#*/} upTo1min/${z#*/} upTo5min/${z#*/} upTo10min/${z#*/} upTo1hour/${z#*/} above1hour/${z#*/} flakyTests/${z#*/} -name $filename.out 2>/dev/null ) || $diffre -ne 0 ]]
  then
	 for file in $z/*.fzn; do mv "$file" $z/${z#*/}/"${file/*.fzn/$filename.fzn}" 2>/dev/null; done
  else

      let count1++
      rm $z/$filename.dzn
  fi
    if [ "$count1" -eq "$arraysize" ]; then
       rm -r $z
    fi

done
     sizeFznFiles
     timeCategory $folderPath $2
done

    #removingEmptyDirectories
