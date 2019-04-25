# coq-install-linux

## [Install the latest `opam`](http://opam.ocaml.org/doc/Install.html)
`OPAM` is the package manager for the OCaml programming language, 
the language in which Coq is implemented.

- `sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)`

This will simply check your architecture, 
download and install the proper pre-compiled binary, 
backup your `opam` data if from an older version, and run `opam init`.

## [Using OPAM to install Coq](https://coq.inria.fr/opam-using.html)

- `export OPAMROOT=~/opam-coq.8.9.0` # installation directory
- `opam init -n --comp=ocaml-base-compiler.4.02.3 -j 2` # 2 is the number of CPU cores
- `opam repo add coq-released http://coq.inria.fr/opam/released`
- `opam install coq.8.9.0 && opam pin add coq 8.9.0`

## [Install CoqIDE](https://coq.inria.fr/opam-using.html)

- `sudo apt install libgtksourceview2.0-dev` CoqIDE requires GTK+ development files ([`gtksourceview2`](https://github.com/ocaml/opam-repository/issues/12156)):
- `opam install coqide`

## [Launch CoqIDE](https://stackoverflow.com/a/55846482/1833118)

- Add `export OPAMROOT=~/opam-coq.8.9.0` to `~/.bashrc`
- Run `opam init` to let `opam` modify `~/.bashrc` (chosen interactively) by appending
some configuration to the end of this file (in particular, after the `export` line).
- `source ~/.bashrc`
- `coqide`

If [`coqide `complains](https://askubuntu.com/questions/208431/failed-to-load-module-canberra-gtk-module):
> Gtk-Message: Failed to load module "canberra-gtk-module",

then run
- `sudo apt-get install libcanberra-gtk-module`