################################################################
# Standard Rules from here on
################################################################

default:	$(prog)

hc = ghc
osuf = o
hisuf = hi
hs_flags += -hisuf $(hisuf) -osuf $(osuf)

hs_files  = $(wildcard *.hs)
lhs_files = $(wildcard *.lhs)
o_files   = $(addsuffix .$(osuf),  $(basename $(hs_files) $(lhs_files)))
hi_files  = $(addsuffix .$(hisuf), $(basename $(hs_files) $(lhs_files)))

SUFFIXES= .hs .lhs .$(hisuf) .$(osuf)

%.$(osuf):	%.hs
	rm -f $@
	$(hc) -c $(hs_flags) $<

%.$(osuf):	%.lhs
	rm -f $@
	$(hc) -c $(hs_flags) $<

%.$(hisuf):	%.$(osuf)
	@

$(prog):	$(o_files)
	rm -f $@
	$(hc) $(hs_flags) $^ -o $(prog)

clean::	
	rm -f *~
	rm -f *.bak
	rm -f $(o_files)
	rm -f $(prog)

veryclean::
	rm -f $(hi_files)

install: depends.mk

# 
depends.mk: $(hs_files) $(lhs_files)
		cat /dev/null > depends2.mk
		$(mkdependHS) $(mkdependHS_flags) -f depends2.mk $(hs_files) $(lhs_files) 
		sed -e "s/\.o/\.$(osuf)/g" -e "s/\.hi/\.$(hisuf)/g" <depends2.mk >depends.mk
		rm -f depends2.mk

# A rule copying changed files from ../src would be great
#	gcc -E -C -P -traditional -x c-header $< -o $@  

include depends.mk

################################################################
# End standard rules
################################################################

