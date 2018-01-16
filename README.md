# idt
This github repository, named idt, user jeremydaw, contains the paper
(in subdirectory orlowska-idt)
Dawson and Gore,
Machine-checked Meta-theory of Dual-Tableaux for Intuitionistic Logic
in the monograph
"Ewa Orłowska on Relational Methods in Logic and Computer Science"
and the proofs described in it (in subdirectory hol).

The proof were last run using HOL built from github commit
5dbff8c882f39facaa8584351d280fa0c60aea85
(we did this using PolyML version 5.6)

Instruction to run these proofs:

Download HOL from github, at https://github.com/HOL-Theorem-Prover/HOL

Build HOL, as described in the file HOL/INSTALL, into the directory ~/HOL

Then, in the directory hol (containing several files with names
idt_...Script.sml), run
~/HOL/bin/Holmake --qof

When this succeeds, run
~/HOL/bin/hol

load "idt_completeTheory" ;
load "idtLib" ;

open idt_soundTheory idt_genTheory idt_lemmasTheory idtLib idt_completeTheory ;

This should then give access to the theorems and functions described in the
paper.




