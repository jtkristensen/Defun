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

datatype fun'natnat' =
    fn''11 of (fun'nat'natnat'' * fun'''nat'natnat''nat'nat' * fun'nat'nat''nat'natnat''nat''' * fun'''nat'natnat''nat'nat')
  | fn''10
  | fn''7 of (nat)
  | fn''1 of (fun'nat'natnat'' * nat)

and      fun'nat'natnat'' =
    fn''9
  | fn''6
  | f'1

and      fun''nat'natnat''nat' =
    fn''4 of (nat * nat)

and      fun'nat''nat'natnat''nat'' =
    f'2 of (fun'nat'natnat'' * fun'''nat'natnat''nat'nat' * fun'nat'nat''nat'natnat''nat''' * fun'''nat'natnat''nat'nat')
  | fn''3 of (nat)

and      fun'nat'nat''nat'natnat''nat''' =
    fn''2

and      fun'''nat'natnat''nat'nat' =
    fn''8
  | fn''5

(* **************************************************** *)
(*             Apply functions                          *)
(* **************************************************** *)

fun app'natnat' (fn''11(add, fst, pair, snd), n) =
     let val fib_aux =
       f'2(add, fst, pair, snd)
     in
       app'''nat'natnat''nat'nat'(snd, app'nat''nat'natnat''nat''(fib_aux, n))
     end
  | app'natnat' (fn''10, y) =
     y
  | app'natnat' (fn''7(x), y) =
     x
  | app'natnat' (fn''1(f, n), m) =
     (if  (n) <> 0
      then app'natnat'(app'nat'natnat''(f, (pred(n))), (succ(m)))
      else m
     )

and app'nat'natnat'' (fn''9, x) =
     fn''10
  | app'nat'natnat'' (fn''6, x) =
     fn''7(x)
  | app'nat'natnat'' (f'1, n) =
     fn''1(f'1, n)

and app''nat'natnat''nat' (fn''4(l, r), s) =
     app'natnat'(app'nat'natnat''(s, l), r)

and app'nat''nat'natnat''nat'' (f'2(add, fst, pair, snd), n) =
     (if  (n) <> 0
      then let val p =
       app'nat''nat'natnat''nat''(f'2(add, fst, pair, snd), (pred(n)))
     in
       app'nat''nat'natnat''nat''(app'nat'nat''nat'natnat''nat'''(pair, app'natnat'(app'nat'natnat''(add, app'''nat'natnat''nat'nat'(snd, p)), app'''nat'natnat''nat'nat'(fst, p))), app'''nat'natnat''nat'nat'(fst, p))
     end
      else app'nat''nat'natnat''nat''(app'nat'nat''nat'natnat''nat'''(pair, 1), 1)
     )
  | app'nat''nat'natnat''nat'' (fn''3(l), r) =
     fn''4(l, r)

and app'nat'nat''nat'natnat''nat''' (fn''2, l) =
     fn''3(l)

and app'''nat'natnat''nat'nat' (fn''8, p) =
     app''nat'natnat''nat'(p, fn''9)
  | app'''nat'natnat''nat'nat' (fn''5, p) =
     app''nat'natnat''nat'(p, fn''6)

(* **************************************************** *)
(*             Tranformed expression                    *)
(* **************************************************** *)

val result' =
  let val add =
    f'1
  in
    let val pair =
      fn''2
    in
      let val fst =
        fn''5
      in
        let val snd =
          fn''8
        in
          let val fib =
            fn''11(add, fst, pair, snd)
          in
            app'natnat'(fib, 10)
          end
        end
      end
    end
  end

(* **************************************************** *)
(*             End of transformation                    *)
(* **************************************************** *)
