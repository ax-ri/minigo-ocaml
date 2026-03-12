# `minigo-ocaml`

A compiler for the MiniGo programming language (a subset of Go), written in OCaml.

This project is the final assignment for CSC_52064 course.

## Installation

To build the project from sources, just run `make`. This will install the project dependencies using `opam` and then build the compiler using `dune`.

If you get some issues with `opam`, this project has been successfully tested with the version `5.3.0` of `ocaml-base-compiler`.
You can use the following steps to get a working build in a Docker container:

```bash
# run this from the root directory of the project (the directory containing this README file)
sudo docker create -it -v $(pwd):/home/opam/minigo --name opam ocaml/opam:ubuntu-25.04-ocaml-5.3
sudo docker start opam && sudo docker exec -it opam bash
# in the opam container
sudo apt update && sudo apt install -y autoconf # needed by opam
cd /home/opam/minigo
# create an opam switch for the dependencies
opam switch create . 5.3.0
eval $(opam env)
# build the compiler
make
```

## Report

The report file is available in the [`project-report.pdf`](./project-report.pdf) file.

## Authors

Elfie Molina--Bonnefoy and Axel Richard
