(* **************************************************** *)
(*               Original program                       *)
(* **************************************************** *)

(*
let add =
  (fun a0 n =
    (fun a1 m =
      (ifz  n
       then ((a0 pred(n)) succ(m))
       else m
      )))
in
  let f =
    (fun fn' x =
      (x 1))
  in
    let h =
      (fun fn' y =
        succ(y))
    in
      let g =
        (fun fn' z =
          pred(z))
      in
        ((add (f g)) (f h))
*)

(* **************************************************** *)
(*               Evaluated to                           *)
(* **************************************************** *)

(* 2 *)

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
    a0'0
  | a1'0 of (lam * nat)
  | fn''0
  | fn''1
  | fn''2
  | dead_code

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'a0'0 (a0'0, n) =
     a1'0(a0'0, n)

and app'a1'0 (a1'0(a0'0, n), m) =
     (if  (n) <> 0
      then app'a1'0(app'a0'0(a0'0, (pred(n))), (succ(m)))
      else m
     )

and app'fn''0 (fn''0, x) =
     app'fn''1orfn''2(x, 1)

and app'fn''1 (fn''1, y) =
     (succ(y))

and app'fn''1orfn''2 (fn''1, y) =
     (succ(y))
  | app'fn''1orfn''2 (fn''2, z) =
     (pred(z))

and app'fn''2 (fn''2, z) =
     (pred(z))

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add'0 =
    a0'0
  in
    let val f'0 =
      fn''0
    in
      let val h'0 =
        fn''1
      in
        let val g'0 =
          fn''2
        in
          app'a1'0(app'a0'0(add'0, app'fn''0(f'0, g'0)), app'fn''0(f'0, h'0))
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
