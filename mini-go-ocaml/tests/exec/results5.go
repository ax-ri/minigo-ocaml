package main
import "fmt"

func step1(a, b int) (int, int) {
	return b, a+b
}

func step2(a, b int) (int, int) {
	return b, a+b
}

func main() {
	_, x := step1(step2(step1(0, 1)));
	fmt.Print(x, "\n");
}
