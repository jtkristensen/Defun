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
    let sqr =
      (fun fn' x =
        ((mul x) x))
    in
      (sqr 8)
*)

(* **************************************************** *)
(*               Evaluated to                           *)
(* **************************************************** *)

(* 64 *)

(* **************************************************** *)
(*        Basic operations on natural numbers           *)
(* **************************************************** *)

type nat     = int
fun  pred(n) = if n <> 0 then n - 1 else 0
fun  succ(n) = n + 1

(* **************************************************** *)
(*             Type constructors                        *)
(* **************************************************** *)

datatype lam =
    f'0
  | fn''0 of (lam * nat)
  | fn''1 of (lam * lam * nat)
  | fn''2 of (lam)
  | g'0 of (lam)
  | dead_code

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'f'0 (f'0, n) =
     fn''0(f'0, n)

and app'fn''0 (fn''0(f'0, n), m) =
     (if  (n) <> 0
      then app'fn''0(app'f'0(f'0, (pred(n))), (succ(m)))
      else m
     )

and app'fn''1 (fn''1(add'0, g'0(_), x), y) =
     (if  (x) <> 0
      then app'fn''0(app'f'0(add'0, y), app'fn''1(app'g'0(g'0(add'0), (pred(x))), y))
      else 0
     )

and app'fn''2 (fn''2(mul'0), x) =
     app'fn''1(app'g'0(mul'0, x), x)

and app'g'0 (g'0(add'0), x) =
     fn''1(add'0, g'0(add'0), x)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add'0 =
    f'0
  in
    let val mul'0 =
      g'0(add'0)
    in
      let val sqr'0 =
        fn''2(mul'0)
      in
        app'fn''2(sqr'0, 8)
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
