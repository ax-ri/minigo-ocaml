
EXE=./minigo
SUBMISSION_FOLDER=../molina--bonnefoy_richard

$(EXE): *.ml*
	opam install . --deps-only
	opam exec -- dune build @all
	mv -f _build/default/$(EXE).exe $(EXE)

test: $(EXE) test.go
	$(EXE) --debug test.go
	gcc -g -z noexecstack -no-pie test.s -o test
	go run test.go
	./test

submission:
	dune build
	find tests -iname "*.s" -exec rm {} \;
	rm -rf $(SUBMISSION_FOLDER)
	mkdir -p $(SUBMISSION_FOLDER)
	cp -r \
		*.{ml,mll,mly} \
		Makefile \
		minigo.opam \
		dune dune-project \
		.ocamlformat \
		README.md \
		project-report.pdf \
		test.go \
		tests \
		$(SUBMISSION_FOLDER)
	tar zcf $(SUBMISSION_FOLDER).tar.gz $(SUBMISSION_FOLDER)

clean:
	dune clean

.PHONY: clean $(EXE)