# coq-install-linux

## [Install the latest `opam`](http://opam.ocaml.org/doc/Install.html)
`OPAM` is the package manager for the OCaml programming language, 
the language in which Coq is implemented.

> sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)

This will simply check your architecture, 
download and install the proper pre-compiled binary, 
backup your `opam` data if from an older version, and run `opam init`.

## [Using OPAM to install Coq](https://coq.inria.fr/opam-using.html)

> export OPAMROOT=~/opam-coq.8.9.0 				# installation directory
> opam init -n --comp=ocaml-base-compiler.4.02.3 -j 2 		# 2 is the number of CPU cores
> opam repo add coq-released http://coq.inria.fr/opam/released
> opam install coq.8.9.0 && opam pin add coq 8.9.0

## [Install CoqIDE](https://coq.inria.fr/opam-using.html)

### [Install `gtksourceview2`](https://github.com/ocaml/opam-repository/issues/12156)

CoqIDE requires GTK+ development files (`gtksourceview2`).

> sudo apt install libgtksourceview2.0-dev

### [Install CoqIDE](https://coq.inria.fr/opam-using.html)

> opam install coqide

## [Launch CoqIDE](https://coq.inria.fr/opam-using.html)

*Note:* Every time a new shell is opened 
one has to type in the following lines in order to use Coq.

> export OPAMROOT=~/opam-coq.8.9.0
> eval `opam config env`

Then,
> coqide

If it complains:
> Gtk-Message: Failed to load module "canberra-gtk-module"
then [run](https://askubuntu.com/questions/208431/failed-to-load-module-canberra-gtk-module)
> sudo apt-get install libcanberra-gtk-module