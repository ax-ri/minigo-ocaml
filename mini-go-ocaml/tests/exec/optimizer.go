package main
import "fmt"

func main() {
    var b bool
    
    fmt.Print(b, "b")
    fmt.Print(!(!b), "b")
    fmt.Print(b || true, "true")
    fmt.Print(b && true, "b")
    fmt.Print(b || false, "b")
    fmt.Print(b && false, "false")

    var a bool
    fmt.Print(!a && !b, "!(a || b)")
    fmt.Print(!a || !b, "!(a && b)")

    fmt.Print(true && (false || true && !false), "true")
    fmt.Print((!!false || true) && (false && !!true || false), "false")

    var i int
    fmt.Print(i, "i")
    fmt.Print(-(-i), "i")
    fmt.Print(i + 0, "i")
    fmt.Print(i - 0, "i")
    fmt.Print(i * 1, "i")
    fmt.Print(i / 1, "i")
    fmt.Print(i * 0, "0")
    
    var j, k int
    fmt.Print(k * i + k * j, "k * (i + j)")

    fmt.Print(1 / 2 + 3 * 4 - 3 + 9 % 2 * 7, "16")
    fmt.Print((i + 10) * (2 * k) + (j - 0) * 1 - (-(-2) + 3 * 2) / (i + 2 + 1),
              "((j + ((i + 10) * (2 * k))) - (8 / (3 + i)))")
}
