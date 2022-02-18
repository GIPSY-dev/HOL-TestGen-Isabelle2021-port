#############################################################################
# HOL-TestGen --- 
#                 http://www.brucker.ch/projects/hol-testgen/
#                                                                            
# Makefile ---  
# This file is part of HOL-TestGen.
#
# Copyright (c) 2013 Achim D. Brucker, Germany
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
# $Id: Makefile 9462 2012-10-15 09:12:46Z lukasbru $

JAVAC=javac
SCALAC=scalac
SCALA=scala
HARNESSDIR=../../../../../harness/scala/
HARNESS=$(HARNESSDIR)/harness.scala
MAIN=$(HARNESSDIR)/main.scala

default: run

classes/JavaList.class: JavaList.java
	$(JAVAC) -d classes JavaList.java

classes/Main.class: classes/JavaList.class typeConv.scala is_sorted_test_script.scala $(HARNESS) $(MAIN)
	$(SCALAC) -cp classes -d classes typeConv.scala is_sorted_test_script.scala $(HARNESS) $(MAIN)

run: classes/Main.class
	$(SCALA) -classpath classes Main

clean:
	$(RM) -r classes/*
