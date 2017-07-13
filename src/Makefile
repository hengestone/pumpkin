OBJS = utils.cmo exceptions.cmo scanner.cmo parser.cmo analyzer.cmo processor.cmo \
       codegen.cmo codegen_lua.cmo pumpkin.cmo

pmkn : $(OBJS)
	ocamlc -o pmkn $(OBJS)

scanner.ml : scanner.mll
	ocamllex scanner.mll

parser.ml parser.mli : parser.mly
	ocamlyacc -v parser.mly

analyzer.cmo : sast.cmo ast.cmi utils.cmo
analyzer.cmx : sast.cmx ast.cmi utils.cmi
exceptions.cmo :
exceptions.cmx :
interpret.cmo : sast.cmo
interpret.cmx : sast.cmx
parser.cmo : ast.cmi parser.cmi
parser.cmx : ast.cmi parser.cmi
processor.cmo : scanner.cmo parser.cmi
processor.cmx : scanner.cmx parser.cmx
pumpkin.cmo : utils.cmo processor.cmo parser.cmi exceptions.cmo \
    analyzer.cmo codegen.cmo codegen_lua.cmo
pumpkin.cmx : utils.cmx processor.cmx parser.cmx exceptions.cmx \
    analyzer.cmx codegen.cmx codegen_lua.cmx
sast.cmo : ast.cmi
sast.cmx : ast.cmi
scanner.cmo : parser.cmi exceptions.cmo
scanner.cmx : parser.cmx exceptions.cmx
utils.cmo : sast.cmo parser.cmi ast.cmi
utils.cmx : sast.cmx parser.cmx ast.cmi
codegen.cmo : sast.cmo parser.cmi ast.cmi exceptions.cmo
codegen.cmx : sast.cmx parser.cmx ast.cmi exceptions.cmx
codegen_lua.cmo : sast.cmo parser.cmi ast.cmi exceptions.cmo
codegen_lua.cmx : sast.cmx parser.cmx ast.cmi exceptions.cmx
ast.cmi :
parser.cmi : ast.cmi

%.cmo : %.ml
	ocamlc -c $<

%.cmi : %.mli
	ocamlc -c $<

.PHONY : clean
clean :
	rm -f pmkn parser.ml parser.mli scanner.ml \
	*.cmo *.cmi *.out *.diff *.orig *.output
