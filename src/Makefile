# PolyP can be 
#  compiled with ghc or hbc
#  or interpreted by hugs

default:	ghc

# Clear the implicit suffix-rules
.SUFFIXES:

# make ghc/hbc in this directory uses cpp as a filter
export hs_flags += -cpp

ghc:
	$(MAKE) -f ghc.mk osuf=g_o hisuf=g_hi
# let ghc use .g_o and .g_hi instead of .o and .hi
#   => both ghc and hbc can compile in the same directory

hbc:
# Hack: to overcome an hbc-installation problem at
#     Linux croak.cs.yale.edu 2.0.31 #1 Sun Nov 9 21:45:23 EST 1997 i686 unknown
#   hs_link_flags
	$(MAKE) -f hbc.mk hs_link_flags=$(HOME)/haskell/hbcfix/fix.o
hugs:
	@echo "Ignore any warnings about closed pipes."
	hugs -F"cpp -P -C -traditional -D__HUGS__" Main.lhs

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

hugssrc:
	cp hugs.mk ../hugssrc/Makefile
	cppdir . ../hugssrc -D__HUGS__

ghcsrc:
	cp ghc.mk ../ghcsrc/Makefile
	cp rules.mk depends.mk ../ghcsrc/
	cppdir . ../ghcsrc -D__GLASGOW_HASKELL__

hbcsrc:
	cp hbc.mk ../hbcsrc/Makefile
	cppdir . ../hbcsrc -D__HBC__
