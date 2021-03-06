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


import sys
if sys.version_info[0:2] < (3,2):
    print("matchC requires Python 3.2 or higher")
    exit(1)

import argparse
import os
import platform
import subprocess
import tempfile
import time

from ansi_colors import *
import run_maude


ml_lang = 'matchC'

ml_bin_dir = os.path.abspath(sys.path[0])
ml_lib_dir = os.path.abspath(os.path.join(ml_bin_dir, '..', 'lib'))

antlr_jar = os.path.join(ml_lib_dir, 'antlrworks-1.4.jar')
ml_parser_jar = os.path.join(ml_lib_dir, 'matchCparser.jar')
ml_parser_main_class = 'KernelCPreK'
maude_dir = os.path.join(ml_bin_dir, 'maude2.6')
ml_prelude = os.path.join(ml_lib_dir, 'ml-prelude.maude')
ml_semantics_compiled = os.path.join(ml_lib_dir, ml_lang + '-compiled.maude')
ml_utils = os.path.join(ml_lib_dir, 'utils.maude')
ml_viewer_jar = os.path.join(ml_lib_dir, 'matchCviewer.jar')
ml_viewer_text_main_class = 'TextViewer'
ml_viewer_visual_main_class = 'VisualViewer'

ml_prog = 'prog'
ml_prog_header = ['load ' + ml_prelude + '\n',
    'load ' + ml_semantics_compiled + '\n',
    'load ' + ml_utils + '\n',
    'mod ' + ml_prog.upper() + ' is inc ' + ml_lang.upper() + ' + UTILS .\n']
ml_prog_footer = ['endm\n\n',
    'set print attribute on .\n',
    'rew check(' + ml_prog + ') .\n',
    'q\n']


def timer(start_message, stop_message):
    def timer_function(function):
        def timer_wrapper(*args, **kwargs):
            print(start_message, end='')
            sys.stdout.flush()
            start = time.time()

            retval = function(*args, **kwargs)

            end = time.time()
            elapsed = "%.3f" % round(end - start, 3) + "s"
            print(stop_message + ' [' + elapsed + ']')
            sys.stdout.flush()

            return retval
        return timer_wrapper
    return timer_function
 


### check the c program compiles with some c compiler
@timer('CC program ..........', ' DONE!')
def checkc(source_filename, cc='gcc'):
    # check that cc binary exists
    try:
        null_fd = os.open(os.devnull, os.O_WRONLY)
        subprocess.call(cc, stdout=null_fd, stderr=null_fd)
    except OSError:
        return 127;

    # compile the c program with the cc compiler
    (file_obj, compiled_file) = tempfile.mkstemp()
    os.close(file_obj)
    cmd = [cc, '-c', '-o', compiled_file, source_filename]
    return subprocess.call(cmd)


### compile c program with ml annotation into labeled k (maude format)
@timer('Compiling program ...', ' DONE!')
def compile(in_filename, out_filename):
    if os.name == 'posix' or os.name == 'mac':
        cp_sep = ':'
    elif os.name == 'nt':
        cp_sep = ';' 
    cp = ['-cp', antlr_jar + cp_sep + ml_parser_jar]
    cmd = ['java'] + cp + [ml_parser_main_class]
    in_file = open(in_filename, 'r')
    out_file = open(out_filename, 'w')

    out_file.writelines(ml_prog_header)
    out_file.flush()

    retcode = subprocess.call(cmd, bufsize=-1, stdin=in_file, stdout=out_file)

    out_file.writelines(ml_prog_footer)
    in_file.close()
    out_file.close()

    return retcode


### verify the program in maude + smt
def verify(prog_filename, log_filename=None):
    global is_verified
    is_verified = True

    cmd = None
    if platform.system() == 'Linux':
        if platform.machine() == 'i686':
            cmd = 'maude.linux'
        elif platform.machine() == 'x86_64':
            cmd = 'maude.linux64'
    elif platform.system() == 'Darwin':
        cmd = 'maude.intelDarwin'

    args = ['-no-prelude', '-no-banner', '-no-wrap', '-no-ansi-color']
    if log_filename != None:
        args += ['-xml-log=' + log_filename]
    args += [prog_filename]

    retcode = run_maude.run(
                  cmd=cmd,
                  cmd_args=args,
                  path=maude_dir,
                  filter=output_filter,
                  epilog='DONE!')
    if retcode != 0: sys.exit(retcode)

    if is_verified:
        print(green_color + 'Verification succeeded!' + no_color, statistics)
    else:
        print(red_color + 'Verification failed!' + no_color, statistics)
    if output_stream != None:
        if output_stream != "" and output_stream != "epsilon":
            print('Output:', output_stream)


is_timeout = False
is_verified = False
statistics = None
output_stream = None

def timeout_handle():
    global is_timeout

def output_filter(line):
    global is_verified
    global statistics
    global output_stream

    line = line.strip()
    if line.startswith('rewrites'):
        rewrites = line.split()[1]
        statistics = '[' + rewrites + ' rewrites, '
    elif line.startswith('< feasible >'):
        feasible = green_color + line.split()[3][15:-10] + no_color
        statistics += feasible + ' feasible and '
    elif line.startswith('< infeasible >'):
        infeasible = red_color + line.split()[3][15:-10] + no_color
        statistics += infeasible + ' infeasible paths]'
    elif line.startswith('< tasks >'):
        is_verified = False
    elif line.startswith('< mainOut >'):
        output_stream = line.replace(' @ ', ' ')
        output_stream = output_stream.replace('[', '').replace(']', '')
        output_stream = output_stream[19:-14]


args = None
### parse command line arguments
def parse_args():
    global args

    parser = argparse.ArgumentParser(
        description='Matching logic verifier',
        prog='matchC')

    parser.add_argument(
        '-c', '--compile-only',
        action='store_true',
        default=False,
        help='compile progam and specifications into labeled k (maude format)' \
            +' only; do not verify any function',
        dest='compile')
    parser.add_argument(
        '-cc',
        default='gcc',
        help='check c syntax of program with compiler',
        metavar='compiler',
        dest='cc')
    parser.add_argument(
        '-d', '--display',
        action='store_true',
        default=False,
        help='display verifier output into a java widget')
    parser.add_argument(
        '-o',
        help='place tool output into file',
        metavar='file',
        dest='output')
    parser.add_argument(
        '-s', '--silent',
        action='store_true',
        default=False,
        help='do not generate any verifier output')
    parser.add_argument(
        'file',
        help='file to verify',
        metavar='file')

    args = parser.parse_args()
    return args


###
def main():
    args = parse_args()

    if not os.path.isfile(args.file):
        sys.exit('matchC: ' + args.file + ': no such file or directory')

    if args.output == None:
        rootname = os.path.splitext(os.path.basename(args.file))[0]
        if not args.compile:
            args.output = rootname + '.kml'
        else:
            args.output = rootname + '.maude'

    retcode = checkc(args.file, cc=args.cc)
    if retcode != 0: return retcode

    if not args.compile:
        (file_obj, compiled_file) = tempfile.mkstemp(suffix='.maude')
        os.close(file_obj)
    else:
        compiled_file = args.output
    retcode = compile(args.file, compiled_file)
    if retcode != 0: return retcode

    if args.compile: return 0

    if not args.silent:
        (file_obj, log_filename) = tempfile.mkstemp(suffix='.xml')
        os.close(file_obj)
        verify(compiled_file, log_filename=log_filename)
    else:
        verify(compiled_file)

    if is_verified: return 0

    if not args.silent and not args.display:
        cmd = ['java', '-cp', ml_viewer_jar, ml_viewer_text_main_class,
              log_filename, args.output]

        start = time.time()
        print('Generating error ....', end="")

        retcode = subprocess.call(cmd)
        if retcode != 0: return retcode

        end = time.time()
        elapsed = "%.3f" % round(end - start, 3) + "s"
        print(' DONE! [' + elapsed + ']')

        print('Check ' + args.output + ' for the complete output.')

    if not args.silent and args.display:
        cmd = ['java', '-cp', ml_viewer_jar, ml_viewer_visual_main_class,
              log_filename]

        retcode = subprocess.call(cmd)
        if retcode != 0: return retcode


if __name__ == '__main__':
    main()
