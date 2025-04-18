open Top_level;;

(* testsuite.ml
  This batch file can be read to test the theorem-prover Folderol.
  It checks for both provable and unprovable formulae.

  MODIFIED 9 July 1988; April 2025
 *)

(* PROPOSITIONAL EXAMPLES *)

(* absorptive laws of & and | *)
run_goal "P & P <-> P";;
run_goal "P | P <-> P";;

(* commutative laws of & and | *)
run_goal "P & Q <-> Q & P";;
run_goal "P | Q <-> Q | P";;

(* associative laws of & and | *)
run_goal "(P & Q) & R <-> P & (Q & R)";;
run_goal "(P | Q) | R <-> P | (Q | R)";;

(* distributive laws of & and | *)
run_goal "(P & Q) | R <-> (P | R) & (Q | R)";;
run_goal "(P | Q) & R <-> (P & R) | (Q & R)";;

(* Laws involving implication *)
run_goal "(P | Q --> R) <-> (P --> R) & (Q --> R)";;
run_goal "(P & Q --> R) <-> (P --> (Q --> R))";;
run_goal "(P --> Q & R) <-> (P --> Q) & (P --> R)";;

(* Classical theorems *)
run_goal "P | Q --> P | ~P & Q";;
run_goal "((P --> Q) --> Q) <-> P | Q";;
run_goal "(P --> Q) & (~P --> R) --> (P & Q | R)";;
run_goal "P & Q | ~P & R <-> (P --> Q) & (~P --> R)";;
run_goal "(P --> Q) | (P --> R) <-> (P --> Q | R)";;
run_goal "(P <-> Q) <-> (Q <-> P)";;
run_goal "(EXISTS x. EXISTS y. P(x,y)) <-> (EXISTS y. EXISTS x. P(x,y))";;
run_goal "(ALL x. P(x) & Q(x)) <-> (ALL x. P(x)) & (ALL x. Q(x))";;
run_goal "(ALL x. P(x))  |  (ALL x. Q(x)) --> (ALL x. P(x) | Q(x))";;
run_goal "(ALL x. P(x)) | Q <-> (ALL x. P(x) | Q)";;
run_goal "(ALL x. P --> Q(x)) <-> (P --> (ALL x. Q(x)))";;
run_goal "(ALL x. P(x) --> Q) <-> ((EXISTS x. P(x)) --> Q)";;
run_goal "(EXISTS x. P(x) | Q(x)) <-> (EXISTS x. P(x))  |  (EXISTS x. Q(x))";;
run_goal "(EXISTS x. P(x) & Q(x)) --> (EXISTS x. P(x)) & (EXISTS x. Q(x))";;
run_goal "(EXISTS x. P --> Q(x)) <-> (P --> (EXISTS x. Q(x)))";;
run_goal "(EXISTS x. P(x) --> Q) <-> (ALL x. P(x)) --> Q";;

(* hard: needs multiple instantiation of ALL and may loop *)
run_goal "(ALL x. P(x) --> P(f(x))) --> (ALL y. P(y) --> P(f(f(f(y)))))";;

(* needs double instantiation of EXISTS *)
run_goal "EXISTS x. P(x) --> P(f(x)) & P(g(x))";;
run_goal "ALL x. ALL y. EXISTS z. P(z) --> P(x) & P(y)";;
run_goal "EXISTS x. P(x) --> (ALL x. P(x))";;

(* Principia Mathematica *11.53 *)
run_goal
  "(ALL x. ALL y. P(x) --> Q(y)) <-> ((EXISTS x. P(x)) --> (ALL y. Q(y)))"
;;

(* Principia Mathematica *11.55 *)
run_goal
  "(EXISTS x. EXISTS y. P(x) & Q(x,y)) <-> (EXISTS x. P(x) & (EXISTS y. \
   Q(x,y)))"
;;

(* Principia Mathematica *11.61 *)
run_goal
  "(EXISTS y. ALL x. P(x) --> Q(x,y)) --> (ALL x. P(x) --> (EXISTS y. Q(x,y)))"
;;

(* Basic test of quantifier reasoning *)
run_goal "(EXISTS y. ALL x. P(x,y)) --> (ALL x. EXISTS y. P(x,y))";;

(* various non-valid formulae *)
fail_goal 40 "(ALL x. EXISTS y. P(x,y)) --> (EXISTS y. ALL x. P(x,y))";;

(* Should not be provable: different eigenvariables must be chosen *)
fail_goal 40 "(EXISTS x. P(x)) --> (ALL x. P(x))";;
fail_goal 40 "P(?aaaa) --> (ALL x. P(x))";;
fail_goal 40 "(P(?aaaa) --> (ALL x. Q(x))) --> (ALL x. P(x) --> Q(x))";;

(* Not provable, causes looping!  simplest example of Folderol's stupidity *)
fail_goal 40 "(ALL x. P(x)) --> Q";;
run_goal "(ALL x. P(x)) --> (EXISTS x. P(x))";;
run_goal "(ALL x. P(x) --> Q(x)) & (EXISTS x. P(x)) --> (EXISTS x. Q(x))";;
run_goal "(P --> (EXISTS x. Q(x))) & P --> (EXISTS x. Q(x))";;

(* example in text of a theorem not proved due to stupidity *)
read_goalseq
  [ "EXISTS x. P(x)"; "ALL x. P(x) --> Q(x)" ]
  [ "ALL x. ~Q(x) --> ~P(x)" ]
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* the simpler goal is provable... *)
run_goalseq [ "ALL x. P(x) --> Q(x)" ] [ "ALL x. ~Q(x) --> ~P(x)" ];;
print_string "Pelletier's Problems\n";;

(* Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.
*)

(* 1 *)
run_goal "(P --> Q) <-> (~Q --> ~P)";;

(* 2 *)
run_goal "~~P <-> P";;

(* 3 *)
run_goal "~(P --> Q) --> (Q --> P)";;

(* 4 *)
run_goal "(~P --> Q) <-> (~Q --> P)";;
print_string "Problem 5\n";;

(* 5 *)
run_goal "((P | Q) --> (P | R)) --> (P | (Q --> R))";;

(* 6 *)
run_goal "P | ~P";;

(* 7 *)
run_goal "P | ~~~P";;

(* 8.  Peirce's law *)
run_goal "((P --> Q) --> P) --> P ";;
run_goal "(~P --> P) --> P ";;

(* 9 *)
run_goal "((P | Q) & (~P | Q) & (P | ~Q)) --> ~(~P | ~Q) ";;
print_string "Problem 10\n";;

(* 10 *)
run_goalseq [ "Q --> R"; "R --> P & Q"; "P --> Q | R" ] [ "P <-> Q" ];;

(* 11.  Proved in each direction (incorrectly, says Pelletier!!) *)
run_goal "P <-> P ";;

(* 12.  "Dijkstra's law" *)
run_goal "((P <-> Q) <-> R) --> (P <-> (Q <-> R))";;

(* 13.  Distributive law *)
run_goal "P | Q & R <-> (P | Q) & (P | R)";;

(* 14 *)
run_goal "(P <-> Q) <-> ((Q | ~P) & (~Q | P))";;
print_string "Problem 15\n";;

(* 15 *)
run_goal "(P --> Q) <-> (~P | Q)";;

(* 16 *)
run_goal "(P --> Q) | (Q --> P)";;

(* 17 *)
run_goal "(P & (Q --> R) --> S) <-> ((~P | Q | S) & (~P | ~R | S))";;

(* FALSE GOALS, final state gives countermodel *)
fail_goal 1000 "(P | Q --> R) <-> (P --> (Q --> R))";;
fail_goal 1000 "(P --> Q) <-> (Q --> ~P)";;
fail_goal 1000 "~(P --> Q) --> (Q <-> P)";;
fail_goal 1000 "((P --> Q) --> Q) --> P ";;
fail_goal 1000 "((P | Q) & (~P | Q) & (P | ~Q)) --> ~(~P | Q) ";;

(* Indicates need for subsumption *)
fail_goal 1000 "((P & (Q <-> R)) <-> S) <-> ((~P | Q | S) & (~P | ~R | S))";;

(* 18 *)
run_goal "EXISTS y. ALL x. P(y) --> P(x)";;

(* 19 *)
run_goal "EXISTS x. ALL y. ALL z. (P(y) --> Q(z)) --> (P(x) --> Q(x))";;
print_string "Problem 20\n";;

(* 20 *)
run_goal
  "(ALL x. ALL y. EXISTS z. ALL w. (P(x) & Q(y) --> R(z) & S(w))) --> (EXISTS \
   x. EXISTS y. P(x) & Q(y)) --> (EXISTS z. R(z))"
;;

(* 21: hard *)
run_goalseq
  [ "EXISTS x. P --> Q(x)"; "EXISTS x. Q(x) --> P" ]
  [ "EXISTS x. P <-> Q(x)" ]
;;

(* 22 *)
run_goal "(ALL x. P <-> Q(x)) --> (P <-> (ALL x. Q(x)))";;

(* 23 *)
run_goal "(ALL x. P | Q(x)) <-> (P | (ALL x. Q(x)))";;

(* 24: hard *)
run_goalseq
  [
    "~(EXISTS x. S(x) & Q(x))";
    "ALL x. P(x) --> Q(x) | R(x)";
    "(~(EXISTS x. P(x))) --> (EXISTS x. Q(x))";
    "ALL x. Q(x) | R(x) --> S(x)";
  ]
  [ "EXISTS x. P(x) & R(x)" ]
;;

print_string "Problem 25\n";;

(* 25: hard *)
run_goalseq
  [
    "EXISTS x. P(x)";
    "ALL x. F(x) --> ~(G(x) & R(x))";
    "ALL x. P(x) --> (G(x) & F(x))";
    "(ALL x. P(x) --> Q(x)) | (EXISTS x. P(x) & R(x))";
  ]
  [ "EXISTS x. Q(x) & P(x)" ]
;;

(* 26: hard *)
run_goalseq
  [
    "(EXISTS x. P(x)) <-> (EXISTS x. Q(x))";
    "ALL x. ALL y. P(x) & Q(y) --> (R(x) <-> S(y))";
  ]
  [ "(ALL x. P(x) --> R(x)) <-> (ALL x. Q(x) --> S(x))" ]
;;

(* 27 *)
run_goalseq
  [
    "EXISTS x. P(x) & ~Q(x)";
    "ALL x. P(x) --> R(x)";
    "ALL x. G(x) & F(x) --> P(x)";
    "(EXISTS x. R(x) & ~Q(x)) --> (ALL x. F(x) --> ~R(x))";
  ]
  [ "ALL x. G(x) --> ~F(x)" ]
;;

(* 28.  AMENDED *)
run_goalseq
  [
    "ALL x. P(x) --> (ALL x. Q(x))";
    "(ALL x. Q(x) | R(x)) --> (EXISTS x. Q(x) & S(x))";
    "(EXISTS x. S(x)) --> (ALL x. F(x) --> G(x))";
  ]
  [ "ALL x. P(x) & F(x) --> G(x)" ]
;;

(* 29.  Essentially Principia Mathematica *11.71 *)
run_goalseq
  [ "(EXISTS x. P(x)) & (EXISTS x. Q(x))" ]
  [
    "(ALL x. P(x) --> R(x)) & (ALL x. Q(x) --> S(x)) <-> (ALL x. ALL y. P(x) & \
     Q(y) --> R(x) & S(y))";
  ]
;;

print_string "Problem 30\n";;

(* 30 *)
run_goalseq
  [ "ALL x. P(x) | Q(x) --> ~R(x)"; "ALL x. (Q(x) --> ~S(x)) --> P(x) & R(x)" ]
  [ "ALL x. S(x)" ]
;;

(* 31 *)
run_goalseq
  [
    "~(EXISTS x. P(x) & (Q(x) | R(x)))";
    "EXISTS x. F(x) & P(x)";
    "ALL x. ~R(x) --> G(x)";
  ]
  [ "EXISTS x. F(x) & G(x)" ]
;;

(* 32 *)
run_goalseq
  [
    "ALL x. P(x) & (Q(x) | R(x)) --> S(x)";
    "ALL x. S(x) & R(x) --> F(x)";
    "ALL x. G(x) --> R(x)";
  ]
  [ "ALL x. P(x) & G(x) --> F(x)" ]
;;

(* 33 *)
run_goal
  "(ALL x. P(a) & (P(x) --> P(b)) --> P(c)) <-> (ALL x. (~P(a) | P(x) | P(c)) \
   & (~P(a) | ~P(b) | P(c)))"
;;

(* 34  AMENDED.  Not proved!!! *)
read_goal
  "((EXISTS x. ALL y. P(x) <-> P(y)) <-> ((EXISTS x. Q(x)) <-> (ALL y. Q(y)))) \
   <-> ((EXISTS x. ALL y. Q(x) <-> Q(y)) <-> ((EXISTS x. P(x))  <-> (ALL y. \
   P(y))))"
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;
print_string "Problem 35\n";;

(* 35 *)
run_goal "EXISTS x. EXISTS y. P(x,y) --> (ALL x. ALL y. P(x,y))";;

(* 36 *)
run_goalseq
  [
    "ALL x. EXISTS y. F(x,y)";
    "ALL x. EXISTS y. G(x,y)";
    "ALL x. ALL y. F(x,y) | G(x,y) --> (ALL z. F(y,z) | G(y,z) --> H(x,z))";
  ]
  [ "ALL x. EXISTS y. H(x,y)" ]
;;

(* 37.  Here folderol beats the PROLOG version *)
run_goalseq
  [
    "ALL z. EXISTS w. ALL x. EXISTS y. (P(x,z) --> P(y,w)) & P(y,z) & (P(y,w) \
     --> (EXISTS u. Q(u,w)))";
    "ALL x. ALL z. ~P(x,z) --> (EXISTS y. Q(y,z))";
    "(EXISTS x. EXISTS y. Q(x,y)) --> (ALL x. R(x,x))";
  ]
  [ "ALL x. EXISTS y. R(x,y)" ]
;;

(* 38  Not proved!!! *)
read_goal
  "(ALL x. P(a1) & (P(x) --> (EXISTS y. P(y) & R(x,y))) --> (EXISTS z. EXISTS \
   w.P(z) & R(x,w) & R(w,z))) <-> (ALL x. (~P(a1) | P(x) | (EXISTS z. EXISTS \
   w.P(z) & R(x,w) & R(w,z))) & (~P(a1) | ~(EXISTS y. P(y) & R(x,y)) \
   |                   (EXISTS z. EXISTS w. P(z) & R(x,w) & R(w,z))))"
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* 39 *)
run_goal "~(EXISTS x. ALL y. F(x,y) <-> ~F(y,y))";;
print_string "Problem 40\n";;

(* 40.  AMENDED *)
run_goal
  "(EXISTS y. ALL x. F(y,x) <-> ~F(x,x)) --> ~(ALL x. EXISTS y. ALL z. F(z,y) \
   <-> ~F(z,x))"
;;

(* 41  Not proved (proved using random numbers!!) *)
read_goalseq
  [ "ALL z. EXISTS y. ALL x. F(x,y) <-> F(x,z) & ~F(x,x)" ]
  [ "~(EXISTS z. ALL x. F(x,z))" ]
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* 42  Not proved (proved using random numbers!!) *)
read_goal "~(EXISTS y. ALL x. F(x,y) <-> ~(EXISTS z. F(x,z) & F(z,x)))"
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* 43  Not proved (proved using random numbers!!) *)
read_goalseq
  [ "ALL x. ALL y. Q(x,y) <-> (ALL z. F(z,x) <-> F(z,y))" ]
  [ "ALL x. ALL y. Q(x,y) <-> Q(y,x)" ]
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* 44  Not proved!!! *)
read_goalseq
  [
    "ALL x. F(x) --> ((EXISTS y. G(y) & H(x,y)) & (EXISTS y. G(y) & ~H(x,y)))";
    "EXISTS x. J(x) & (ALL y. G(y) --> H(x,y))";
  ]
  [ "EXISTS x. J(x) & ~F(x)" ]
|> steps 40
;;

print_string "Don't expect to have proved this one...\n";;

(* 4 October 1988: loaded this file in 27 secs *)

(* 45.  Here folderol beats the PROLOG version. *)
run_goalseq
  [
    "ALL x. F(x) & (ALL y. G(y) & H(x,y) --> J(x,y))                        \
     --> (ALL y. G(y) & H(x,y) --> K(y))";
    "~(EXISTS y. L(y) & K(y))";
    "EXISTS x. F(x) & (ALL y. H(x,y) --> L(y)) & (ALL y. G(y) & H(x,y) --> \
     J(x,y))";
  ]
  [ "EXISTS x. F(x) & ~(EXISTS y. G(y) & H(x,y))" ]

(* takes 50 seconds!!! *)
