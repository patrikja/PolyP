# This makefile is for compiling polyp with ghc

prog = ../bin/ghcpolyp

#hs_flags += -O2
#hs_flags += -O0
#hs_flags += -g
#hs_flags += -syslib hbc
#hs_flags += -auto -prof
#hs_flags += -Wall
# To get to the ST-monad and possibly trace
hs_flags += -fglasgow-exts -package lang

mkdependHS = mkdependHS
mkdependHS_flags = -x IOExts -x ST
include rules.mk
