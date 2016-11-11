#! /bin/bash

TC=$(find ../.. /opt -maxdepth 2 -name 'toolchain*' 2> /dev/null )
BIN=$(find / $TC -maxdepth 2 -name 'bin' 2> /dev/null )
GCC=$(find $BIN -maxdepth 2 -name 'arm-none-eabi-gcc' 2> /dev/null )

if [[ -z $GCC ]]
then
  echo "No cross compiler found, install arm-none-eabi-gcc?" 1>&2
else
  ls $GCC | sed 's/-gcc$/-/' | head -n 1
fi


