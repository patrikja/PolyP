export targets
HUGSFLAGS = -98
targets = 1/innoutonlist.hs                   	\
	  2/simplemutreclist.hs               	\
	  3/explicitfunctorsimplification.hs  	\
	  4/simpledataconversion.hs		\
	  5/polytoptyped.hs			\
	  6/parsefloat.hs			\
	  7/testinfixconstructors.hs	        \
	  8/testconstnames.hs

check:: $(targets:.hs=.check)

check:: veryclean

include polyp.mk

