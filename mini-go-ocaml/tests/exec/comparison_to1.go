package main
import "fmt"

func main() {
    fmt.Print(0 == 1, "\n")
    fmt.Print(0 == 0, "\n")
    fmt.Print(0 != 1, "\n")
    fmt.Print(0 != 0, "\n")

    fmt.Print(0 < 1, "\n")
    fmt.Print(1 < 0, "\n")
    fmt.Print(0 < 0, "\n")

    fmt.Print(0 <= 1, "\n")
    fmt.Print(1 <= 0, "\n")
    fmt.Print(0 <= 0, "\n")

    fmt.Print(0 > 1, "\n")
    fmt.Print(1 > 0, "\n")
    fmt.Print(0 > 0, "\n")

    fmt.Print(0 >= 1, "\n")
    fmt.Print(1 >= 0, "\n")
    fmt.Print(0 >= 0, "\n")

    fmt.Print(true && true, "\n")
    fmt.Print(true && false, "\n")
    fmt.Print(true || false, "\n")
    fmt.Print(true || true, "\n")
    fmt.Print(false || true, "\n")
    fmt.Print(false || false, "\n")
}
