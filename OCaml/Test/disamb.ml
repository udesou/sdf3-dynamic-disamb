(* operator-style ambiguity *)
1 + if 2 then 3 + 4;;

(* brackets that are useless (removing them would produce the same tree) - might improve readability *)
1 + (if 2 then 3 + 4);;
1 + if 2 then (3 + 4);;
(1 + 1 [@foo] * 2);; (* also an operator style ambiguity *)
(1 + 1 [@foo]) * 2;;

(* explicit disambiguation of operator-style deep conflicts by brackets *)
(1 + if 2 then 3) + 4;;
1 + (if 2 then 3) + 4;;
1 + (1 [@foo] * 2);;
1 + (1 [@foo]) * 2;;

(* brackets that disambiguate direct conflicts and operator-style deep conflicts *)
1 + (1 + if 2 then 3) + 4;;

(* brackets that disambiguate direct conflicts *)
1 + (2 + 3) ;;
(if 2 then 3) + 4 ;;
1 * (2 + 3) ;;
if 1 then (if 3 then 4) else 5;;

(* dangling else ambiguity *)
if 1 then 2 + if 3 then 4 else 5;;
if 1 then 2 + if 3 then 4 + 5 else 5;; (* also operator-style ambiguity *)

(* brackets that are useless (removing them would produce the same tree) - might improve readability *)
if 1 then 2 + (if 3 then 4 else 5);;
if 1 then (2 + if 3 then 4 else 5);;

(* explicit disambiguation of dangling else conflicts by brackets *)
if 1 then 2 + (if 3 then 4) else 5;;

(*
(* longest-match ambiguity *)
match m1 with a -> match 2 with b -> 3
                              | c -> 4;;

(* brackets that are useless (removing them would produce the same tree) - might improve readability *)
match m1 with a -> (match 2 with b -> 3
                              | c -> 4);;


(* explicit disambiguation of longest-match conflicts by brackets *)
match m1 with a -> (match 2 with b -> 3)
                               | c -> 4 *)