# This is really a GNUmakefile, i.e. it requires GNU make extensions

prog = ../bin/hbcpolyp
#hs_flags += -O
hc = hbc
hbcmakedepends = hbcmake -g

.SUFFIXES:
.SUFFIXES: .hs .lhs .$(hisuf) .$(osuf)

default: $(prog)

%.hi:	%.o
	@
#echo tillverkar .hi fran .o

%.o:	%.hs
	$(hc) -c $(hs_flags) $<

%.o:	%.lhs
	$(hc) -c $(hs_flags) $<

lhs_files = $(wildcard *.lhs)
hi_files  = $(lhs_files:.lhs=.hi)
o_files   = $(lhs_files:.lhs=.o)

clean::	
	rm -f *~
	rm -f $(o_files)
	rm -f $(prog)

veryclean::	clean
	rm -f $(hi_files)


$(prog):	$(o_files)
	$(hc) $(hs_flags) $(hs_link_flags) $^ -o $(prog) 

depends: hbcdepends.mk

# use hbcmake to recreate the dependencies in hbcdepends.mk
hbcdepends.mk: $(lhs_files)
	$(hbcmakedepends) Main.lhs > hbcdepends.mk

include hbcdepends.mk
