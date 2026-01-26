
EXE=./minigo.exe

test: $(EXE) test.go
	go run test.go
	$(EXE) --debug test.go
	gcc -g -no-pie test.s -o test
	./test

$(EXE): *.ml*
	dune build @all

.PHONY: clean test
clean:
	dune clean
