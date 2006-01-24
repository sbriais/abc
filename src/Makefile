#   This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, 
#  USA.
#
VERSION=1.0.6
CC=gcc
CFLAGS=-O2
CAMLC=ocamlc
CAMLOPT=ocamlopt
PRGM=abc
CAMLLIBR=camllibr
CAMLLEX=ocamllex
CAMLYACC=ocamlyacc
CAMLDEP=ocamldep
CAMLDOC=ocamldoc
DOT=dot
COMPFLAGS=   -ccopt $(CFLAGS)
LINKFLAGS=  
COMMONFLAGS= 
LEXFLAGS=
YACCFLAGS=-v
CPP=/lib/cpp -P -DVERSION=$(VERSION)
CAMLLIBPATH=`$CAMLC -where`

LIBS =  unix.cma
MMAKE=make_ocaml
LEXERANDPARSER=lexer.mll
DISTML= agent.ml agent_parse.ml  conditions.ml  distinctions.ml main.ml  multiset.ml  name.ml commands.ml pprinter.ml sprinter.ml parser.ml compile_info.ml formatter.ml semantic.ml bisimulation.ml
SPECML= lexer.ml
DISTMLI=   conditions.mli  distinctions.mli   multiset.mli  name.mli          
SPECMLI= 
CMI = agent.cmi agent_parse.cmi conditions.cmi distinctions.cmi main.cmi multiset.cmi name.cmi commands.cmi pprinter.cmi sprinter.cmi parser.cmi compile_info.cmi formatter.cmi semantic.cmi bisimulation.cmi conditions.cmi distinctions.cmi multiset.cmi name.cmi  lexer.cmi  
OBJS= conditions.cmo multiset.cmo name.cmo agent.cmo agent_parse.cmo distinctions.cmo formatter.cmo semantic.cmo bisimulation.cmo commands.cmo compile_info.cmo lexer.cmo parser.cmo sprinter.cmo pprinter.cmo main.cmo
CMX = $(OBJS:.cmo=.cmx)

EXTRADIST = make_ocaml Makefile.in README LICENSE abc_ug.ps examples Makefile

SPECIAL=$(EXTRADIST) .depend Makefile.am

all: 	depend Makefile 
	@make $(PRGM)

opt:    depend Makefile
	@make $(PRGM).opt

Makefile: Makefile.am 
	$(MMAKE) 2> /dev/null

$(PRGM).ps : all $(DISTML) $(DISTMLI)
	$(CAMLDOC) -dot $(DISTML) $(DISTMLI); $(DOT) -Tps < ocamldoc.out > $(PRGM).ps

$(PRGM).opt : $(CMX) $(CMI) 
	$(CAMLOPT) $(COMMONFLAGS) $(LINKFLAGS) $(LIBS:.cma=.cmxa) -o $(PRGM).opt $(CMX) -ccopt -O2

$(PRGM) : $(OBJS) $(CMI) 
	$(CAMLC) $(COMMONFLAGS) $(LINKFLAGS) $(LIBS) -o $(PRGM) $(OBJS) 

compile_info.ml: Makefile
	@echo "let date_of_compile=\""`date`"\"" > compile_info.ml
	@echo "let version=\""$(VERSION)"\"" >> compile_info.ml
	@echo "let build_info=\""`uname -msrn`"\"" >> compile_info.ml

lexer.ml: lexer.mll 
	$(CAMLLEX) $(LEXFLAGS) lexer.mll






	

%.cmi : %.mli
	$(CAMLC) $(COMMONFLAGS) $(COMPFLAGS) -c $<

%.cmx : %.ml
	$(CAMLOPT) $(COMMONFLAGS) $(COMPFLAGS) -c $<

%.cmo : %.ml
	$(CAMLC) $(COMMONFLAGS) $(COMPFLAGS) -c $<

%.o : %.c
	$(CC) $(CFLAGS) -I$(CAMLLIBPATH)/caml -c $<

clean:
	rm -f $(CMI) $(CMX) $(CMX:.cmx=.o) $(OBJS) $(PRGM) $(PRGM).opt $(PRGM).ps ocamldoc.out $(SPECML) $(SPECMLI) parser.output compile_info.ml .depend *~
	touch .depend

depend: .depend
	@$(CAMLDEP) $(COMMONFLAGS) $(DISTMLI) $(DISTML) $(SPECML) $(SPECMLI) > .depend

dist:	
	tar cvfz $(PRGM)-$(VERSION).tar.gz --exclude compile_info.ml --exclude CVS $(DISTMLI) $(DISTML) $(SPECIAL) $(LEXERANDPARSER) 

-include .depend
