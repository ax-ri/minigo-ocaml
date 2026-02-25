
EXE=./minigo.exe

test: $(EXE) test.go
	$(EXE) --debug test.go
	gcc -g -z noexecstack -no-pie test.s -o test
	go run test.go
	./test

$(EXE): *.ml*
	dune build @all

.PHONY: clean test
clean:
	dune clean
