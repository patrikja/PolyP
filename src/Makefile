# PolyP can be 
#  compiled with ghc or hbc
#  or interpreted by hugs
# This Makefile is invoked by ../Makefile

default:	ghc

# Clear the implicit suffix-rules
.SUFFIXES:

POLYPDIR = $(dir $(shell pwd))
POLYPPRELUDE = $(POLYPDIR)lib/PolyPrel.hs
# The C-preprocessor
CPP = gcc -E -C -P -traditional -x c-header
#CPP = cpp -P -C -traditional
CPPFLAGS += -D__POLYPPRELUDE__=\"$(POLYPPRELUDE)\"

# All Haskell source files in this directory
lhs_files = $(wildcard *.lhs)

hugssrc: $(lhs_files:%=../hugssrc/%)
	cp hugs.mk ../hugssrc/Makefile

../hugssrc/%.lhs:	../src/%.lhs
	$(CPP) $(CPPFLAGS) -D__HUGS__ $< -o $@  

ghcsrc: $(lhs_files:%=../ghcsrc/%)
	cp ghc.mk ../ghcsrc/Makefile
	cp rules.mk ../ghcsrc/
	sed -e "s/\.g_o/\.o/g" -e "s/\.g_hi/\.hi/g" <depends.mk >../ghcsrc/depends.mk

../ghcsrc/%.lhs:	../src/%.lhs
	$(CPP) $(CPPFLAGS) -D__GLASGOW_HASKELL__ $< -o $@  

hbcsrc: $(lhs_files:%=../hbcsrc/%)
	cp hbc.mk ../hbcsrc/Makefile
	-cp hbcdepends.mk ../hbcsrc/

../hbcsrc/%.lhs:	../src/%.lhs
	$(CPP) $(CPPFLAGS) -D__HBC__ $< -o $@  

# make ghc/hbc in this directory uses cpp as a filter
export hs_flags += -cpp

ghc:
	$(MAKE) -f ghc.mk osuf=g_o hisuf=g_hi
# let ghc use .g_o and .g_hi instead of .o and .hi
#   => both ghc and hbc can compile in the same directory

hbc:
# the -o prevents remaking of hbcdepends.mk
	$(MAKE) -f hbc.mk -o hbcdepends.mk  \
                   hs_link_flags=$(HOME)/haskell/hbcfix/fix.o
# last line is a hack to overcome an hbc-installation problem at
#     Linux croak.cs.yale.edu 2.0.31 #1 Sun Nov 9 21:45:23 EST 1997 i686 unknown

hugs:
	@echo "Ignore any warnings about closed pipes."
	hugs -F'$(CPP) $(CPPFLAGS) -D__HUGS__' Main.lhs

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

# make sure that the depency files are up to date.
dist:
	$(MAKE) -f ghc.mk depends.mk
	cp depends.mk hbcdepends.mk

# old stuff

oldhugssrc:
	cp hugs.mk ../hugssrc/Makefile
	cppdir . ../hugssrc "$(CPPFLAGS) -D__OLD_HUGS__ -D__HUGS__"

