# Makefile for hugs 

# This alias is an alternative (in tcsh) to the polyp-command
# alias polyp runhugs `pwd`/Main.lhs

hc = runhugs

default:
	echo $(hc) -98 -h300000 `pwd`/Main.lhs $$\* >../bin/hugspolyp 
	chmod +x ../bin/hugspolyp
