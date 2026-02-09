package main

import "fmt"

func main() {
	fmt.Print("1 + 1: ", 1 + 1, "\n2 + 1: ", 2 + 1, "\n")
	fmt.Print("(1 + 1) * (2 + 3): ", (1 + 1) * (2 + 3), "\n")
	fmt.Print("5 / 2: ", 5 / 2, "\n")
	fmt.Print("1 == 1: ", 1 == 1, "\n2 == 1: ", 2 == 1, "\n")
	fmt.Print("true && true: ", true && true, "\nfalse && true: ", false && true, "\ntrue && false: ", true && false, "\nfalse && false: ", false && false, "\n")
	fmt.Print("true || true: ", true || true, "\nfalse || true: ", false || true, "\ntrue || false: ", true || false, "\nfalse || false: ", false || false, "\n")
}

