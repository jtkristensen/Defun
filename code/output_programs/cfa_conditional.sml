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

datatype lam =
    conditional'0 of (lam * lam)
  | const'1
  | eq0'1 of (lam)
  | fn''0 of (nat)
  | gt0'1 of (lam)
  | dead_code

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'conditional'0 (conditional'0(eq0'0, gt0'0), k) =
     (if  (k) <> 0
      then gt0'0
      else eq0'0
     )

and app'const'1 (const'1, x) =
     fn''0(x)

and app'eq0'1 (eq0'1(const'0), m) =
     app'fn''0(app'const'1(const'0, 0), m)

and app'eq0'1orgt0'1 (eq0'1(const'0), m) =
     app'fn''0(app'const'1(const'0, 0), m)
  | app'eq0'1orgt0'1 (gt0'1(const'0), n) =
     app'fn''0(app'const'1(const'0, 1), n)

and app'fn''0 (fn''0(x), y) =
     x

and app'gt0'1 (gt0'1(const'0), n) =
     app'fn''0(app'const'1(const'0, 1), n)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val const'0 =
    const'1
  in
    let val gt0'0 =
      gt0'1(const'0)
    in
      let val eq0'0 =
        eq0'1(const'0)
      in
        let val f'0 =
          conditional'0(eq0'0, gt0'0)
        in
          app'eq0'1orgt0'1(app'conditional'0(f'0, 100), 0)
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
