#!/usr/bin/env python3


import os
import sys

import run_maude
import matchC


matchC.main()

rootname = os.path.splitext(os.path.basename(matchC.args.file))[0]
xml_filename = "test_" + rootname + ".xml"
xml_file = open(xml_filename, "w")
xml_file.write("<?xml version='1.0' encoding='UTF-8' ?>\n")
xml_file.write("<testsuite name='adhoc'>\n")
xml_file.write("  <testcase name='" + matchC.args.file + "'")
if run_maude.verification_time != None:
    xml_file.write(" time='" + run_maude.verification_time + "'")
xml_file.write(">\n")
if matchC.args.file.find("undefined") != -1 and matchC.is_verified:
    failure_text = "matchC passed for an undefined program!!!"
    xml_file.write("    <failure> " + failure_text + " </failure>")
if matchC.args.file.find("undefined") == -1 and not matchC.is_verified:
    failure_text = "matchC failed for a valid program!!!"
    xml_file.write("    <failure> " + failure_text + " </failure>")
xml_file.write("  </testcase>\n")
xml_file.write("</testsuite>\n")
xml_file.close()

