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

datatype fun'natnat' =
    fn''3
  | fn''2
  | a1'1 of (fun'nat'natnat'' * nat)

and      fun'nat'natnat'' =
    a0'1

and      fun''natnat'nat' =
    fn''1

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'natnat' (fn''3, z) =
     (pred(z))
  | app'natnat' (fn''2, y) =
     (succ(y))
  | app'natnat' (a1'1(a0, n), m) =
     (if  (n) <> 0
      then app'natnat'(app'nat'natnat''(a0, (pred(n))), (succ(m)))
      else m
     )

and app'nat'natnat'' (a0'1, n) =
     a1'1(a0'1, n)

and app''natnat'nat' (fn''1, x) =
     app'natnat'(x, 1)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add =
    a0'1
  in
    let val f =
      fn''1
    in
      let val h =
        fn''2
      in
        let val g =
          fn''3
        in
          app'natnat'(app'nat'natnat''(add, app''natnat'nat'(f, g)), app''natnat'nat'(f, h))
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
