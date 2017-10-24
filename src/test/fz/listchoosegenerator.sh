#!/bin/bash
if [ $# -lt 1 ]
then
read -p "Please enter the string which you want to find: " string
find above1hour/ upTo1hour/ upTo1min/ upTo5min/ upTo5sec/ upTo10min/ upTo30sec/ -name \*.fzn -exec  grep -il $string {} +  | sed 's/\.fzn$//'  > mizincbasedchosen/list.txt 
cat  mizincbasedchosen/list.txt
else
string=$1
find above1hour/ upTo1hour/ upTo1min/ upTo5min/ upTo5sec/ upTo10min/ upTo30sec/ -name \*.fzn -exec  grep -il $string {} +  | sed 's/\.fzn$//' > mizincbasedchosen/list.txt
cat mizincbasedchosen/list.txt
fi
