#! /bin/bash
echo "var x is $1 in while (0 <= x) (x = x + -1 ;)" > countdown.imp
~/code/k-framework/dist/bin/krun countdown.imp

