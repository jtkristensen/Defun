(* **************************************************** *)
(*               Original program                       *)
(* **************************************************** *)

(*
let add =
  (fun f n =
    (fun fn' m =
      (ifz  n
       then ((f pred(n)) succ(m))
       else m
      )))
in
  let mul =
    (fun g x =
      (fun fn' y =
        (ifz  x
         then ((add y) ((g pred(x)) y))
         else 0
        )))
  in
    ((mul ((add 2) 2)) ((add 2) 2))
*)

(* **************************************************** *)
(*               Evaluated to                           *)
(* **************************************************** *)

(* 16 *)

(* **************************************************** *)
(*        Basic operations on natural numbers           *)
(* **************************************************** *)

type nat     = int
fun  pred(n) = if n <> 0 then n - 1 else 0
fun  succ(n) = n + 1

(* **************************************************** *)
(*             Type constructors                        *)
(* **************************************************** *)

datatype fun'natnat' =
    fn''2 of (fun'nat'natnat'' * fun'nat'natnat'' * nat)
  | fn''1 of (fun'nat'natnat'' * nat)

and      fun'nat'natnat'' =
    g'1 of (fun'nat'natnat'')
  | f'1

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'natnat' (fn''2(add, g, x), y) =
     (if  (x) <> 0
      then app'natnat'(app'nat'natnat''(add, y), app'natnat'(app'nat'natnat''(g, (pred(x))), y))
      else 0
     )
  | app'natnat' (fn''1(f, n), m) =
     (if  (n) <> 0
      then app'natnat'(app'nat'natnat''(f, (pred(n))), (succ(m)))
      else m
     )

and app'nat'natnat'' (g'1(add), x) =
     fn''2(add, g'1(add), x)
  | app'nat'natnat'' (f'1, n) =
     fn''1(f'1, n)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add =
    f'1
  in
    let val mul =
      g'1(add)
    in
      app'natnat'(app'nat'natnat''(mul, app'natnat'(app'nat'natnat''(add, 2), 2)), app'natnat'(app'nat'natnat''(add, 2), 2))
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
