#!/bin/bash
echo changing file $1;
mv $1 $1.bak;
sed -e "s/@version 4.1/@version 4.2/g" < $1.bak > $1;
rm $1.bak;
