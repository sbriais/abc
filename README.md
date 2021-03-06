Welcome to this Another Bisimulation Checker!
---------------------------------------------
ABC is an equivalence checker for the pi-calculus.  You can find more
technical explanations in the User's Guide of ABC: abc_ug.ps.

Installation:
------------- 
ABC is a tool written in the programming language OCaml.  

OCaml is a functionnal programming language based on the ML paradygm
and developped at INRIA Rocquencourt in France near Paris. You can
find more informations about OCaml on its web page located at
http://caml.inria.fr.

To compile ABC, you need to install OCaml and at least version
3.06. Distributions for Windows/Cygwin, MacOS-X and Linux can be found
on the OCaml web site.

In the following, we assume that you have a Unix-like system. The
installation procedure has been tested under Linux RedHat 8.0, Linux
Mandrake 9.x and Windows XP (with Cygwin).

We assume moreover that you have put the content of the archive in the
directory /usr/local/abc (this can be any other directory of your
choice but in the following, we give commands assuming you have chosen
/usr/local/abc).

How to compile: 
--------------- 
cd /usr/local/abc

* to build OCaml bytecode and the file 'abc'
ocamlbuild main.byte

* to build native code (if available) and the file 'abc.opt'
ocamlbuild main.native

Of course, if native code is available under your platform, we
strongly advise you to build native code.

How to use:
-----------
Depending on which target you have decided to build the ABC, type
'/usr/local/abc/main.byte' or '/usr/local/abc/main.native' to launch
the ABC.  More detailed explanations can be found in the User's Guide.
Examples can be found in the subdirectory examples.

Line editor:
------------
You will notice quickly that the toplevel of ABC is not really
user-friendly. To enhance the ABC, we strongly advise you to install
'ledit' which is a tool made by Daniel de Rauglaudre that gives any
program a true line editor � la emacs.
You can make a little shell script that launch abc with ledit:

#!/bin/sh
ledit /usr/local/abc/abc

assuming that ledit is in your path.

You may also use rlwrap instead of ledit.

License:
--------
The license is contained in the file LICENSE.

Contact: 
-------- 
Feel free to contact the author at sebastien.briais@gmail.com if you
have any problems using ABC or if you have any suggestions.

References:
-----------
Linux Mandrake web site: http://www.mandrakelinux.com/
Linux RedHat web site  : http://www.redhat.com/
Cygwin web site        : http://www.cygwin.com/
OCaml web site         : http://caml.inria.fr/
Ledit                  : http://cristal.inria.fr/~ddr/
