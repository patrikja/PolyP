# Makefile for hugs 

# This alias is an alternative (in tcsh) to the polyp-command
# alias polyp runhugs `pwd`/Main.lhs

hc = runhugs

# The flags mean: 
#   -c70  Use 70 iterations maximum for Class constraint simplification 
#             (default 40 for Hugs98-May1999 was not enough)
#   -98   Hugs mode (not Haskell 98 mode) needed to allow ST-monad extension
#   -h300000 Heap size increased from default 200000 because of bug in Hugs-March1999
default:
	echo $(hc) -c70 -98 -h300000 `pwd`/Main.lhs $$\* >../bin/hugspolyp 
	chmod +x ../bin/hugspolyp
