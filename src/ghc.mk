# This makefile is for compiling polyp with ghc

prog = ../bin/ghcpolyp

#hs_flags += -O2
#hs_flags += -O0
#hs_flags += -g
#hs_flags += -syslib hbc
#hs_flags += -auto -prof
#hs_flags += -Wall
# To get to the ST-monad
hs_flags += -fglasgow-exts

mkdependHS = mkdependHS
#mkdependHS_flags = 
include rules.mk
