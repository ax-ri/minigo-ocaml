package main
import "fmt"

func main() {
  fmt.Print("Equality with 256: \n")
  fmt.Print("\t0==256: ", 0==256, "\n")
  fmt.Print("\t0!=256: ", 0!=256, "\n")

  fmt.Print("Strict comparison with 256: \n")
  fmt.Print("\t256<0: ", 256<0, "\n")
  fmt.Print("\t0<256: ", 0<256, "\n")
  fmt.Print("\t256>0: ", 256>0, "\n")
  fmt.Print("\t0>256: ", 0>256, "\n")

  fmt.Print("Comparison with 256: \n")
  fmt.Print("\t256<=0: ", 256<=0, "\n")
  fmt.Print("\t0<=256: ", 0<=256, "\n")
  fmt.Print("\t256>=0: ", 256>=0, "\n")
  fmt.Print("\t0>=256: ", 0>=256, "\n")
}
