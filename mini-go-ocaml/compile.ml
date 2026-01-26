
(** Code generation for Mini Go programs (TODO) *)

open Format
open Ast
open Tast
open X86_64

let debug = ref false

let iter f = List.fold_left (fun code x -> code ++ f x) nop
let iter2 f = List.fold_left2 (fun code x y -> code ++ f x y) nop

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r


let file ?debug:(b=false) (dl: Tast.tfile): X86_64.program =
  debug := b;
  { text =
      globl "main" ++ label "main" ++
      nop (* TODO call Go main function here *) ++
      xorq (reg rax) (reg rax) ++
      ret ++
      nop (* TODO assembly code for the Go functions here *) ++
      inline "
# TODO some auxiliary assembly functions, if needed
"
  ++ aligned_call_wrapper ~f:"malloc" ~newf:"malloc_"
  ++ aligned_call_wrapper ~f:"calloc" ~newf:"calloc_"
  ++ aligned_call_wrapper ~f:"printf" ~newf:"printf_"
;
    data =
      nop (* TODO static data here, such as string constants *)
    ;
  }
