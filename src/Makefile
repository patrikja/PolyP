# PolyP can be 
#  compiled with ghc or hbc
#  or interpreted by hugs
# This Makefile is invoked by ../Makefile

default:	ghc

# Clear the implicit suffix-rules
.SUFFIXES:

# The C-preprocessor
CPP = cpp -P -C -traditional
#CPP = gcc -E -C -P -traditional -x c-header

hugssrc:
	cp hugs.mk ../hugssrc/Makefile
	cppdir . ../hugssrc -D__HUGS__

oldhugssrc:
	cp hugs.mk ../hugssrc/Makefile
	cppdir . ../hugssrc "-D__OLD_HUGS__ -D__HUGS__"

ghcsrc:
	cp ghc.mk ../ghcsrc/Makefile
	cp rules.mk depends.mk ../ghcsrc/
	cppdir . ../ghcsrc -D__GLASGOW_HASKELL__

hbcsrc:
	cp hbc.mk ../hbcsrc/Makefile
	-cp hbcdepends.mk ../hbcsrc/
	cppdir . ../hbcsrc -D__HBC__

# make ghc/hbc in this directory uses cpp as a filter
export hs_flags += -cpp

ghc:
	$(MAKE) -f ghc.mk osuf=g_o hisuf=g_hi
# let ghc use .g_o and .g_hi instead of .o and .hi
#   => both ghc and hbc can compile in the same directory

hbc:
# the -o prevents remaking of hbcdepends.mkAXS
	$(MAKE) -f hbc.mk -o hbcdepends.mk  \
                   hs_link_flags=$(HOME)/haskell/hbcfix/fix.o
# last line is a hack to overcome an hbc-installation problem at
#     Linux croak.cs.yale.edu 2.0.31 #1 Sun Nov 9 21:45:23 EST 1997 i686 unknown

hugs:
	@echo "Ignore any warnings about closed pipes."
	hugs -F"$(CPP) -D__HUGS__" Main.lhs

clean::	ghcclean hbcclean
	rm -f *~
	rm -f *.bak

ghcclean::
	rm -f *.g_o

hbcclean::
	rm -f *.o

veryclean::	clean
	rm -f *.hi
	rm -f *.g_hi

