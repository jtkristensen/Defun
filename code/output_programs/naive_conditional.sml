(* **************************************************** *)
(*               Original program                       *)
(* **************************************************** *)

(*
let const =
  (fun const x =
    (fun fn' y =
      x))
in
  let gt0 =
    (fun gt0 n =
      ((const 1) n))
  in
    let eq0 =
      (fun eq0 m =
        ((const 0) m))
    in
      let f =
        (fun conditional k =
          (ifz  k
           then gt0
           else eq0
          ))
      in
        ((f 100) 0)
*)

(* **************************************************** *)
(*               Evaluated to                           *)
(* **************************************************** *)

(* 1 *)

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
    eq0'1 of (fun'nat'natnat'')
  | gt0'1 of (fun'nat'natnat'')
  | fn''1 of (nat)

and      fun'nat'natnat'' =
    conditional'1 of (fun'natnat' * fun'natnat')
  | const'1

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'natnat' (eq0'1(const), m) =
     app'natnat'(app'nat'natnat''(const, 0), m)
  | app'natnat' (gt0'1(const), n) =
     app'natnat'(app'nat'natnat''(const, 1), n)
  | app'natnat' (fn''1(x), y) =
     x

and app'nat'natnat'' (conditional'1(eq0, gt0), k) =
     (if  (k) <> 0
      then gt0
      else eq0
     )
  | app'nat'natnat'' (const'1, x) =
     fn''1(x)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val const =
    const'1
  in
    let val gt0 =
      gt0'1(const)
    in
      let val eq0 =
        eq0'1(const)
      in
        let val f =
          conditional'1(eq0, gt0)
        in
          app'natnat'(app'nat'natnat''(f, 100), 0)
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
