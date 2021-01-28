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
  let pair =
    (fun fn' l =
      (fun fn' r =
        (fun fn' s =
          ((s l) r))))
  in
    let fst =
      (fun fn' p =
        (p (fun fn' x =
          (fun fn' y =
            x))))
    in
      let snd =
        (fun fn' p =
          (p (fun fn' x =
            (fun fn' y =
              y))))
      in
        let fib =
          (fun fn' n =
            let fib_aux =
              (fun f n =
                (ifz  n
                 then let p =
                  (f pred(n))
                in
                  ((pair ((add (snd p)) (fst p))) (fst p))
                 else ((pair 1) 1)
                ))
            in
              (snd (fib_aux n)))
        in
          (fib 10)
*)

(* **************************************************** *)
(*               Evaluated to                           *)
(* **************************************************** *)

(* 89 *)

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
  | f'1 of (lam * lam * lam * lam)
  | fn''0 of (lam * nat)
  | fn''1
  | fn''10 of (lam * lam * lam * lam)
  | fn''2 of (nat)
  | fn''3 of (nat * nat)
  | fn''4
  | fn''5
  | fn''6 of (nat)
  | fn''7
  | fn''8
  | fn''9
  | dead_code

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'f'0 (f'0, n) =
     fn''0(f'0, n)

and app'f'1 (f'1(add'0, fst'0, pair'0, snd'0), n) =
     (if  (n) <> 0
      then let val p'0 =
       app'f'1(f'1(add'0, fst'0, pair'0, snd'0), (pred(n)))
     in
       app'fn''2(app'fn''1(pair'0, app'fn''0(app'f'0(add'0, app'fn''7(snd'0, p'0)), app'fn''4(fst'0, p'0))), app'fn''4(fst'0, p'0))
     end
      else app'fn''2(app'fn''1(pair'0, 1), 1)
     )

and app'fn''0 (fn''0(f'0, n), m) =
     (if  (n) <> 0
      then app'fn''0(app'f'0(f'0, (pred(n))), (succ(m)))
      else m
     )

and app'fn''1 (fn''1, l) =
     fn''2(l)

and app'fn''10 (fn''10(add'0, fst'0, pair'0, snd'0), n) =
     let val fib_aux'0 =
       f'1(add'0, fst'0, pair'0, snd'0)
     in
       app'fn''7(snd'0, app'f'1(fib_aux'0, n))
     end

and app'fn''2 (fn''2(l), r) =
     fn''3(l, r)

and app'fn''3 (fn''3(l, r), s) =
     app'fn''6orfn''9(app'fn''5orfn''8(s, l), r)

and app'fn''4 (fn''4, p) =
     app'fn''3(p, fn''5)

and app'fn''5 (fn''5, x) =
     fn''6(x)

and app'fn''5orfn''8 (fn''5, x) =
     fn''6(x)
  | app'fn''5orfn''8 (fn''8, x) =
     fn''9

and app'fn''6 (fn''6(x), y) =
     x

and app'fn''6orfn''9 (fn''6(x), y) =
     x
  | app'fn''6orfn''9 (fn''9, y) =
     y

and app'fn''7 (fn''7, p) =
     app'fn''3(p, fn''8)

and app'fn''8 (fn''8, x) =
     fn''9

and app'fn''9 (fn''9, y) =
     y

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add'0 =
    f'0
  in
    let val pair'0 =
      fn''1
    in
      let val fst'0 =
        fn''4
      in
        let val snd'0 =
          fn''7
        in
          let val fib'0 =
            fn''10(add'0, fst'0, pair'0, snd'0)
          in
            app'fn''10(fib'0, 10)
          end
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
