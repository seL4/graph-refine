#!/bin/sh

command -v curl >/dev/null 2>&1 || { 
  echo >&2 "Your report could not be submitted: 'curl' is not installed. Aborting."
  exit 1 
}

command -v realpath >/dev/null 2>&1 || { 
  echo >&2 "Your report could not be submitted: 'realpath' is not installed. Aborting."
  exit 1 
}

if [ ! -f "$1" ]; then
  echo "Your report could not be submitted: the file $1 does not exist."
  exit 1
fi

if [ ! -n "$APIKEY" ]; then
  echo "APIKEY not supplied."
fi
if [ ! -n "$SERVER" ]; then
  echo "SERVER not supplied."
fi

FILEPATH=$(realpath $1)

echo "Uploading $FILEPATH..."

curl \
  -F "reporttxt=@$FILEPATH" \
  -F "apikey=$APIKEY" \
  -F "submit=Submit Query" \
  "$SERVER/upload.php"

