# opam-config

- install [`batteries`](https://github.com/ocaml/opam-repository/issues/13793#issuecomment-478860592)

The OCaml compiler looks like it is installed system-wide (not by opam).
So, I guess that could be the problem.
I.e. probable workaround: ***use opam to install the ocaml compiler***.

- `opam switch create ocaml-base-compiler.4.07.1`

then, try to install batteries via opam again:

- `opam install batteries`
