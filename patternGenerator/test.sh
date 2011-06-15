#!/bin/bash
gcc $1 2>/dev/null

if [ $? -ne 0 ]
then
{
    echo "The file outputs errors when being compiled using gcc, please review your code!"
    exit 1
}
else
{
echo "success"
}
fi

make
make run ARG=$1