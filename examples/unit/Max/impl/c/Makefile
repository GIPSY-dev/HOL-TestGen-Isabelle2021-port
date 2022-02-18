#############################################################################
# HOL-TestGen --- theorem-prover based test case generation
#                 http://www.brucker.ch/projects/hol-testgen/
#                                                                            
# Makefile ---  Makefile for compling the "List" testbed 
# This file is part of HOL-TestGen.
#
# Copyright (c) 2013-2015 Achim D. Brucker, Germany
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#
#     * Redistributions in binary form must reproduce the above
#       copyright notice, this list of conditions and the following
#       disclaimer in the documentation and/or other materials provided
#       with the distribution.
#
#     * Neither the name of the copyright holders nor the names of its
#       contributors may be used to endorse or promote products derived
#       from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
##############################################################################
# $Id: Makefile 11098 2015-01-12 10:52:24Z brucker $

HARNESSDIR=../../../../../harness/sml/
HARNESS=$(HARNESSDIR)/harness.sml
MAIN=$(HARNESSDIR)/main.sml



default: run

test: $(HARNESS) max.sml max.c max_test_script.sml $(MAIN)
	mlton -default-ann 'allowFFI true' test.mlb max.c

run: test
	./test

clean:
	rm -rf .cm test

realclean: clean
	rm -rf *test_script.sml
