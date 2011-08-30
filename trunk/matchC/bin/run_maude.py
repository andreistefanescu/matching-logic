#!/usr/bin/env python3

'''
    This file is part of the Matching Logic Verification Framework

    Copyright (C) 2009-2011 Grigore Rosu

    This file is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.
'''


import os
import subprocess
import sys
import time

from ansi_colors import *
import timeout_function


### 
print_prefix = '\{print'
print_suffix = '\}'
timer_flag = 't'
reset_flag = 'r'
open_flag = 'o'


def format_timer(timer):
    return '[' + '%.3f' % timer + 's' + ']'


verification_time = None

def default_filter(line):
    pass

def default_timeout_handle():
    print()


#@timeout(2, default_timeout_handle)
def run(cmd='maude', cmd_args=[], path=None, filter=default_filter, epilog=''):
    global verification_time

    if path != None:
        args = [os.path.abspath(os.path.join(path, cmd))]
    else:
        args = [cmd]
    args += cmd_args

    print("Loading Maude .......", end=' ')
    start = time.time()

    maude = None
    if os.name == 'posix' or os.name == 'mac':
        try:
            import pty
            (master, slave) = pty.openpty()
            maude = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=slave)
            maude_out = os.fdopen(master, 'r')
        except OSError:
            maude = None 
    if maude == None:
        maude = subprocess.Popen(args, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE)
        maude_out = maude.stdout
    maude.stdin.close()

    while True:
        line = maude_out.readline()
        if line.startswith("Bye"):
            end = time.time()
            elapsed = round(end - start, 3)
            print(epilog + ' ' + format_timer(elapsed))
            verification_time = '%.3f' % elapsed
            break

        print_suffix_index = line.find(print_suffix)
        if line.startswith(print_prefix) and print_suffix_index != -1:
            content = line[print_suffix_index + len(print_suffix):].rstrip('\n')
            format = line[len(print_prefix):print_suffix_index].strip(' ')

            isTimer = isReset = isOpen = False
            isFormat = True
            for c in format:
                if c == timer_flag:
                    isTimer = True
                elif c == reset_flag:
                    isReset = True
                elif c == open_flag:
                    isOpen = True
                else:
                    isFormat = False
            if not isFormat:
                filter(line)
                continue

            end = time.time()
            elapsed = round(end - start, 3)
            if isReset: start = end

            formated_line = content
            if isTimer:
                formated_line += ' ' + format_timer(elapsed)
            if isOpen:
                print(formated_line, end=' ')
            else:
                print(formated_line)
        else:
            filter(line)

    return maude.wait()


