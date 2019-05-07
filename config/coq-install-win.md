# coq-install-windows

## Installation from latest released packages

A binary installer for Windows is available at [https://github.com/coq/coq/releases/latest](https://github.com/coq/coq/releases/latest).
The Coq and CoqIDE can be installed following the usual way to install Windows applications.

## Installation of Coq in a virtualized Linux

Some features of Coq are not yet supported under Windows. 
This includes the native compiler and parallel proof processing in CoqIDE.
If you want to take advantage of these features, you can install GNU/Linux in a virtual machine and run CoqIDE from there.
- `Install VirtualBox for Windows and then install Ubuntu inside it`
- `Install Coq following the [Installation of Coq on Linux](https://github.com/hengxin/coq-rock/blob/master/config/coq-install-linux.md) tutorial`

## Installation from Chocolatey

`Chocolatey` is a package manager for Windows. First, install `Chocolatey` following [Installation of Chocolatey](https://chocolatey.org/install) tutorial.
Then Coq and CoqIDE can be installed as follows:
```
chocolatey install coq -y
```
