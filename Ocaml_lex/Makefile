MAIN=calc

OBJS = lexer.cmo rtcalc.cmo main.cmo

%.cmo : %.ml
	ocamlc -g -c $<

%.cmi : %.mli
	ocamlc -g -c $<


$(MAIN): clean $(OBJS)
	ocamlc -g -o $(MAIN) unix.cma str.cma $(OBJS) 

lexer.ml : lexer.mll
	ocamllex -q $<

lexer.cmo : rtcalc.cmi lexer.ml
	ocamlc -g -c lexer.ml

rtcalc.ml : rtcalc.mly
	ocamlyacc -q $<

rtcalc.mli : rtcalc.mly
	ocamlyacc -q $<

clean:
	rm -f *.cmo *.cmi lexer.ml rtcalc.ml rtcalc.mli $(MAIN)
