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
VERSION=1.0.1
CC=gcc
CFLAGS=-O2
CAMLC=ocamlc
CAMLOPT=ocamlopt
PRGM=abc
CAMLLIBR=camllibr
CAMLLEX=ocamllex
CAMLYACC=ocamlyacc
CAMLDEP=ocamldep
COMPFLAGS= -unsafe -w m  -ccopt $(CFLAGS)
LINKFLAGS=
LEXFLAGS=
YACCFLAGS=-v
CPP=/lib/cpp -P -DVERSION=$(VERSION)
CAMLLIBPATH=`$CAMLC -where`

LIBS =  unix.cma
MMAKE=make_ocaml
LEXERANDPARSER=lexer.mll
DISTML= agent.ml agent_parse.ml  conditions.ml  distinctions.ml main.ml  multiset.ml  name.ml commands.ml pprinter.ml parser.ml compile_info.ml
SPECML= lexer.ml
DISTMLI=   conditions.mli  distinctions.mli   multiset.mli  name.mli      
SPECMLI= 
CMI = agent.cmi agent_parse.cmi conditions.cmi distinctions.cmi main.cmi multiset.cmi name.cmi commands.cmi pprinter.cmi parser.cmi compile_info.cmi conditions.cmi distinctions.cmi multiset.cmi name.cmi  lexer.cmi  
OBJS= conditions.cmo distinctions.cmo multiset.cmo name.cmo agent.cmo agent_parse.cmo commands.cmo compile_info.cmo lexer.cmo parser.cmo pprinter.cmo main.cmo
CMX = $(OBJS:.cmo=.cmx)

EXTRADIST = make_ocaml Makefile.am README LICENSE abc_ug.ps Makefile

SPECIAL=$(EXTRADIST) .depend Makefile.am

all: 	depend Makefile 
	@make $(PRGM)

opt:    depend Makefile
	@make $(PRGM).opt

Makefile: Makefile.am 
	$(MMAKE) 2> /dev/null


$(PRGM).opt : $(CMX) $(CMI) 
	$(CAMLOPT) $(LINKFLAGS) $(LIBS:.cma=.cmxa) -o $(PRGM).opt $(CMX) -ccopt -O2

$(PRGM) : $(OBJS) $(CMI) 
	$(CAMLC) $(LINKFLAGS) $(LIBS) -o $(PRGM) $(OBJS) 

compile_info.ml: Makefile
	@echo "let date_of_compile=\""`date`"\";;" > compile_info.ml
	@echo "let version=\""$(VERSION)"\";;" >> compile_info.ml
	@echo "let build_info=\""`uname -msrn`"\";;" >> compile_info.ml

lexer.ml: lexer.mll 
	$(CAMLLEX) $(LEXFLAGS) lexer.mll






	

%.cmi : %.mli
	$(CAMLC) $(COMPFLAGS) -c $<

%.cmx : %.ml
	$(CAMLOPT) $(COMPFLAGS) -c $<

%.cmo : %.ml
	$(CAMLC) $(COMPFLAGS) -c $<

%.o : %.c
	$(CC) $(CFLAGS) -I$(CAMLLIBPATH)/caml -c $<

clean:
	rm -f $(CMI) $(CMX) $(CMX:.cmx=.o) $(OBJS) $(PRGM) $(PRGM).opt $(SPECML) $(SPECMLI) parser.output compile_info.ml .depend *~
	touch .depend

depend: .depend
	@$(CAMLDEP) $(DISTMLI) $(DISTML) $(SPECML) $(SPECMLI) > .depend

dist:	
	tar cvfz $(PRGM)-$(VERSION).tar.gz $(DISTMLI) $(DISTML) $(SPECIAL) $(LEXERANDPARSER) --exclude compile_info.ml

include .depend
