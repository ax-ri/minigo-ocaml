package main
import "fmt"

type T struct {
	x int
	b bool
	s string
	p *int
}

type S struct {
	x int
	b bool
	s string 
	p *int
	t T
}

func main() {
 	var s = new(S)
	var t S
	var i, b, str = new(int), new(bool), new(string)
	fmt.Print("Default values:\n")
	fmt.Print("  - default int: ", t.x, s.x, t.t.x, s.t.x, *i, "\n")
	fmt.Print("  - default boolean: ", t.b, s.b, t.t.b, s.t.b, *b, "\n")
	fmt.Print("  - default string: ", t.s, "-", s.s, "-", t.t.s, "-", s.t.s, "-", *str,"-", "\n")
	fmt.Print("  - default pointer: ", t.p, s.p, t.t.p, s.t.p, "\n")
}
