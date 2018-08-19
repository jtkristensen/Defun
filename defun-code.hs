---------------------------------------------------
-- Title : Simple Defuntionalization Transformation
-- By    : Joachim Tilsted Kristensen
-- Date  : June 22, 2018
---------------------------------------------------

{-# LANGUAGE DeriveFunctor #-}

import Text.ParserCombinators.Parsec
import Control.Monad.RWS
import Control.Monad      (void)
import Data.List          (sort, intercalate, nub, union)
import Data.Either        (isLeft)
import Data.Tuple.Select  (sel2)
import Data.Maybe         (fromJust)
import System.Environment (getArgs)
import qualified Control.Monad.State as StateM
import qualified Data.Map.Strict     as Map

type X    = String -- variable name.
type F    = String -- function name.
type D    = String -- data constructor name.
type C    = String -- type constructor name.
type Nat  = Int    -- natural number.
showTypes = False  -- Flag about output in show instances for E1 and E2.

---------------------------------------------------
-- Gramma For L1 (Just PCF).
---------------------------------------------------

data E1 a = EVar1 X                        a
          | ENat1 Nat                      a
          | ESucc1    (E1 a)               a
          | EPred1    (E1 a)               a
          | EIf1      (E1 a) (E1 a) (E1 a) a
          | ELet1   X (E1 a) (E1 a)        a
          | EFun1 F X (E1 a)               a
          | EApp1     (E1 a) (E1 a)        a
          deriving (Functor)
type L1 a = E1 a
data Tp1  = TNat1 | TArrow1 Tp1 Tp1 deriving (Eq)

-- Convinient for reading the annotation of an expression in L1
annotation1 :: E1 a -> a
annotation1 (EVar1  _     a) = a
annotation1 (ENat1  _     a) = a
annotation1 (ESucc1 _     a) = a
annotation1 (EPred1 _     a) = a
annotation1 (EIf1   _ _ _ a) = a
annotation1 (ELet1  _ _ _ a) = a
annotation1 (EFun1  _ _ _ a) = a
annotation1 (EApp1  _ _   a) = a

---------------------------------------------------
-- Gramma For L2 (A subset of SML).
---------------------------------------------------
type FD a = (F, [(Pattern, E2 a)])
type DD   = (D, [C2])
type C2   = (C, [Tp2])
data E2 a = EVar2 X                            a
          | ENat2 Nat                          a
          | ESucc2    (E2 a)                   a
          | EPred2    (E2 a)                   a
          | EIf2      (E2 a) (E2 a) (E2 a)     a
          | EDataCon2 (C, [E2 a])              a
          | ELet2    X (E2 a) (E2 a)           a
          | EApp2    F (E2 a)                  a
          | ETuple2  [E2 a]                    a
          deriving (Functor, Show, Eq)
data Pattern = TuplePat [Pattern]
             | ConsturctorPat (C, [Pattern])
             | VarPat X deriving (Show)
data L2 a    = Program ([DD], [FD a], E2 a) deriving (Show, Functor)
data Tp2'    = TNat2        | TData2 D  | TTuple2 [Tp2']
data Tp2     = TSimple Tp2' | TArrowFO2 Tp2' Tp2'

-- Convinient for reading the annotation of an expression in L2
annotation2 :: E2 a -> a
annotation2 (EVar2 _     a) = a
annotation2 (ENat2 _     a) = a
annotation2 (ESucc2 _    a) = a
annotation2 (EPred2 _    a) = a
annotation2 (EIf2 _ _ _  a) = a
annotation2 (EDataCon2 _ a) = a
annotation2 (ELet2 _ _ _ a) = a
annotation2 (EApp2 _ _   a) = a
annotation2 (ETuple2 _   a) = a

--------------------------------------------------------
-- Defunctionalizing Translation : (L1 x Tp1 -> L2 x Tp2)
--------------------------------------------------------
-- Note: we do this in two steps.
--  1) translate expressions (E1 x Tp1 -> E2 x Tp2)
--  2) reconstruct program   (E2 x Tp2 -> L2 x Tp2)
-- This section translates types and expressions (step 1).
-- However, we collect enough information for step 2 as
-- a biproduct.
--------------------------------------------------------

-- Note that while this is not surjective, it is in fact bijective onto its image.
translateType :: Tp1 -> Tp2
translateType TNat1 = nat
translateType t     = (datacon . ("fun"++) . dname) t

-- Generates relevant datatype names from function types in L1.
dname TNat1           = "nat"
dname (TArrow1 t0 t1) = "'" ++ dname t0 ++ dname t1 ++ "'"

-- We collect aforementioned information in the translation monad.
type Closure     = [(X, Tp2)]
data FunInfo a   = HOF F X Closure (E2 a) Tp1 deriving (Show)
type Gamma2      = X -> Tp2
type Nabla       = F -> Closure
data TReader     = R { gamma :: Gamma2
                     , nabla :: Nabla
                     }
reader0          = R { gamma = \x -> error $ x ++ " was unbound in gamma_2"
                     , nabla = \x -> error $ "no known closure for " ++ x
                     }
data TState      = S { xid :: X -> I }
state0           = S { xid = const 0 }
type Translation = RWS TReader [FunInfo Tp2] TState

-- Just a convinient way of constructing a userdefined datatype in L2
datacon2 :: X -> Closure -> Tp2 -> E2 Tp2
datacon2 x c = EDataCon2 (x, map (\x' -> EVar2 (fst x') (snd x')) c)

-- Bump the counter for variables named x
freshId :: X -> Translation ()
freshId x =
  do s <- get
     put $ s {xid = \x' -> if x == x' then xid s x + 1 else xid s x'}

-- Get the latest decorated name of x
nameOf :: X -> Translation X
nameOf x = get >>= \s -> return $ x ++ "'" ++ show (xid s x)

-- Locally declare the type of x to be t
hasType :: X -> Tp2 -> (TReader -> TReader)
hasType x t r = r {gamma = \x' -> if x' == x then t else gamma r x'}

-- Locally store the closure c of f
hasClosure :: X -> Closure -> (TReader -> TReader)
hasClosure x c r = r {nabla = \x' -> if x' == x then c else nabla r x'}

-- The closure of f in e, are the free variables in e,
-- except the parameter bound by f self.
computeClosure :: F -> E1 a -> [X] -> Translation (TReader -> TReader)
computeClosure f e ps =
  do g  <- gamma <$> ask
     let xs = sort $ nub $ freeIn e ps
     let c' = map (\x -> (x, g x)) xs
     freshId f
     return $ f `hasClosure` c'

-- Instead of computing the entire closure of a function,
-- we compute the 'relevant-closure', where relevant means
-- the mappings that belong to some free variables in an expression of L1.
freeIn :: E1 a -> [X] -> [X]
freeIn (EVar1 x _)       env = if x `elem` env then [] else [x]
freeIn (ENat1 _ _)         _ = []
freeIn (ESucc1 e _)      env = freeIn e env
freeIn (EPred1 e _)      env = freeIn e env
freeIn (EIf1 e0 e1 e2 _) env = freeIn e0 env ++ freeIn e1 env ++ freeIn e2 env
freeIn (ELet1 x e0 e1 _) env = freeIn e0 env ++ freeIn e1 (x : env)
freeIn (EFun1 f x e _)   env = freeIn e (f : x : env)
freeIn (EApp1 e0 e1 _)   env = freeIn e0 env ++ freeIn e1 env

-- Substitute f with its clousure c in e
subst2 :: X -> E2 a -> E2 a -> E2 a
subst2 f c (EVar2 f' t)       = if f == f' then c else EVar2 f' t
subst2 _ _ (ENat2 n  t)       = ENat2 n t
subst2 f c (ESucc2 e t)       = ESucc2 (subst2 f c e) t
subst2 f c (EPred2 e t)       = EPred2 (subst2 f c e) t
subst2 f c (EIf2 e0 e1 e2 t) =
  EIf2 (subst2 f c e0) (subst2 f c e1) (subst2 f c e2) t
subst2 f c (EDataCon2 (x, es) t) = EDataCon2 (x, map (subst2 f c) es) t
subst2 f c (ELet2 x e0 e1 t) = -- TODO : avoid variable capturing
  let e0' = subst2 f c e0
  in ELet2 x e0' (if x == f then e1 else subst2 f c e1) t
subst2 f c (EApp2 f' e1 t) = EApp2 f' (subst2 f c e1) t
subst2 f c (ETuple2 es t) = ETuple2 (map (subst2 f c) es) t

-- Main translation (E1 x T1) -> (E2 x T2).
-- However, this only retruns the translated expression.
-- The remaining program will be reconstructed later.
translate :: E1 Tp1 -> Translation (E2 Tp2)
translate (EVar1  x t)       = return $ EVar2 x $ translateType t
translate (ENat1  n t)       = return $ ENat2 n $ translateType t
translate (ESucc1 e t)       =
  do e' <- translate e
     return $ ESucc2 e' $ translateType t
translate (EPred1 e t)       =
  do e' <- translate e
     return $ EPred2 e' $ translateType t
translate (EIf1 e0 e1 e2 t) =
  do e0' <- translate e0
     e1' <- translate e1
     e2' <- translate e2
     return $ EIf2 e0' e1' e2' $ translateType t
translate (ELet1 x e0 e1 t) =
  do e0' <- translate e0
     e1' <- local (x `hasType` (translateType $ annotation1 e0)) $ translate e1
     return $ ELet2 x e0' e1' $ translateType t
translate (EFun1 f x e t)    =
  do let t' = translateType t
     f'      <- freshId f >> nameOf f
     let tEnv =
           case t of
             TNat1        -> error $ f ++ " was supposed to be a function?"
             TArrow1 t0 _ -> (f `hasType` t') . (x `hasType` (translateType t0))
     cEnv    <- computeClosure f' e [f, x]
     (n, e') <- local (cEnv . tEnv) $ (,) <$> (nabla <$> ask) <*> translate e
     let c'  = n f'
     let d'  = datacon2 f' c' t'
     tell [HOF f' x c' (subst2 f d' e') t]
     return $ d'
translate (EApp1 e0 e1 _)   =
  case annotation1 e0 of
    TNat1 -> error $ show e0 ++ "is not a function, and cannot be applied."
    ft@(TArrow1 t0 t1) ->
      do e0' <- translate e0
         e1' <- translate e1
         let (t0', t1', tname) = (translateType t0, translateType t1, dname ft)
         let pair = ETuple2 [e0', e1']        $ fo_pair t0' t1'
         return $ EApp2 ("app" ++ tname) pair $ fo_fun  t0' t1'

---------------------------------------------------
-- Naive type-directed defunctionalization
---------------------------------------------------
-- Input  : A program 'p' in L1 annotated with anything.
-- Output : If 'p' was typeable, then the resulting
--          type-annotated defunctionalized program in L2.
--          Otherwise, this throws an error about typeability.
---------------------------------------------------

defunctionalizeNaive :: L1 a -> L2 Tp2
defunctionalizeNaive program =
  let (p,      types) = infere_types_in program
      (p', _,  funs ) = runRWS (translate p) reader0 state0
      hofdefs         = separate types $ collect [] funs
      typedefs        = getDT   hofdefs
      fundefs         = getFuns hofdefs
  in Program (typedefs, fundefs, p')

-- Collect the type annotations for each HOF.
collect :: [(Tp1, FunInfo Tp2)] -> [FunInfo Tp2] -> [(Tp1, FunInfo Tp2)]
collect ts (hof@(HOF _ _ _ _ t) : hofs) = collect ((t, hof) : ts) hofs
collect ts []                           = ts

-- Make separated lists of HOFs, one for each type.
separate :: [Tp1] -> [(Tp1, FunInfo Tp2)] -> [(Tp1, [FunInfo Tp2])]
separate ts tfs = map (\t -> (t, map snd $ filter (\x -> fst x == t) tfs)) ts

-- Construct relevant datatypes
getDT :: [(Tp1, [FunInfo Tp2])] -> [DD]
getDT thofs =
  map (\(t, hofs) ->
        ("fun" ++ dname t, map (\(HOF f _ c _ _) -> (f, map snd c)) hofs)
      ) thofs

getFuns :: [(Tp1, [FunInfo Tp2])] -> [FD Tp2]
getFuns thofs =
  let definition (HOF f x c e _) =
        (TuplePat [ConsturctorPat (f, map (VarPat . fst) c), VarPat x], e)
  in  map (\(t, hofs) -> ("app" ++ dname t, map definition hofs)) thofs

---------------------------------------------------
-- Control Flow Analysis. (CFA-0)
---------------------------------------------------

data ATp f      = ANat                          -- Annotated type.
                | AArrow (ATp f) f (ATp f)
                deriving (Functor)
type Pnt        = Int                           -- Program point.
data Phi        = Pi [F] | Varphi I             -- Possible functions.
                deriving (Show)
type Gamma3     = X -> ATp Phi                  -- annotated typing environment.
data Constraint = Subset Phi Phi                -- Subset constraint
                deriving (Show)
type Closure2   = [(X, ATp Phi)]
type FunBody    = (F, X, Closure2, E1 (ATp Phi)) -- For the defunctionalization.
type FlowSet    = [F]                            -- List of possible functions.
data CFAState = S2 { fid :: F -> I
                   , phi :: I
                   }

-- Control flow analysis monad. (Reader, Writer, State).
type CFAM = RWS Gamma3 [Either Constraint FunBody] CFAState

-- Strip annotated type down to underlying simple type in L1.
strip :: ATp a -> Tp1
strip  ANat             = TNat1
strip (AArrow t1 _ t2)  = TArrow1 (strip t1) (strip t2)

-- Return a fresh set of functions phi
freshPhi :: CFAM Phi
freshPhi =
  do state <- get
     let i = phi state
     put $ state {phi = phi state + 1}
     return $ Varphi i

-- Return a new globally unique function identifer
freshFun :: F -> CFAM F
freshFun f =
  do state <- get
     let i = fid state $ f
     put $ state {fid = \f' -> if f == f' then i + 1 else fid state $ f'}
     return $ f ++ "'" ++ show i

-- Return a fresh annotated type with the same structure.
freshATp :: Tp1 -> CFAM (ATp Phi)
freshATp (TNat1        ) = return ANat
freshATp (TArrow1 t0 t1) =
  do t0'  <- freshATp t0
     phi0 <- freshPhi
     t1'  <- freshATp t1
     return $ AArrow t0' phi0 t1'

-- Check subtyping constraints.
subtype :: ATp Phi -> ATp Phi -> CFAM ()
subtype ANat ANat = return ()
subtype (AArrow t1' phi' t2') (AArrow t1 phi t2) =
  do t1  `subtype`  t1'
     t2' `subtype`  t2
     tell [Left $ Subset phi' phi]
subtype _ _ = error "types have different shapes!"

-- Extend typing environment.
bind3 :: X -> ATp Phi -> Gamma3 -> Gamma3
bind3 x t s = \y -> if x == y then t else s y

-- Substitute f with the new globally uniqe name f'.
substUniq :: F -> F -> E1 a -> E1 a
substUniq f f' (EVar1  g      t) = (EVar1 (if g == f then f' else g) t)
substUniq _ _  (ENat1  n      t) = (ENat1 n t)
substUniq f f' (ESucc1 e      t) = (ESucc1 (substUniq f f' e) t)
substUniq f f' (EPred1 e      t) = (EPred1 (substUniq f f' e) t)
substUniq f f' (EIf1 e0 e1 e2 t) =
  let s = substUniq f f' in (EIf1 (s e0) (s e1) (s e2) t)
substUniq f f' (ELet1 x e0 e1 t) =
  let s = substUniq f f' in (ELet1 x (s e0) (if x == f then e1 else s e1) t)
substUniq f f' (EFun1 g x e t) =
  (EFun1 g x (if f == g || f == x then e else substUniq f f' e) t)
substUniq f f' (EApp1 e0 e1 t) = let s = substUniq f f' in (EApp1 (s e0) (s e1) t)

-- Main analysis function, we collect constraints about which functions
-- may be called at various program points.
analyze :: L1 Tp1 -> CFAM (L1 (ATp Phi))
analyze (EVar1 x _) =
  do gamma <- ask
     return $ EVar1 x $ gamma x
analyze (ENat1 n  _) = return $ ENat1 n ANat
analyze (ESucc1 e _) =
  do e' <- analyze e
     return $ ESucc1 e' ANat
analyze (EPred1 e _) =
  do e' <- analyze e
     return $ EPred1 e' ANat
analyze (EIf1 e0 e1 e2 t) =
  do e0' <- analyze e0
     e1' <- analyze e1
     e2' <- analyze e2
     t'  <- freshATp t
     (annotation1 e1' `subtype` t')
     (annotation1 e2' `subtype` t')
     return $ EIf1 e0' e1' e2' t'
analyze (ELet1 x e0 e1 t) =
  do x'  <- freshFun x
     e0' <- analyze (substUniq x x' e0)
     e1' <- local (bind3 x' (annotation1 e0')) $ analyze (substUniq x x' e1)
     t'  <- freshATp t
     annotation1 e1' `subtype` t'
     return $ ELet1 x' e0' e1' t'
analyze (EFun1 f x e t) =
  do f'                    <- freshFun f
     t'@(AArrow t0 phi t1) <- freshATp t
     e'          <- local (bind3 f' t' . bind3 x t0) $ analyze $ substUniq f f' e
     annotation1 e' `subtype` t1
     gamma       <- ask
     tell [Left $ Subset (Pi [f']) phi]
     let fv      = sort $ nub $ freeIn e [f, x]
     let closure = zip fv $ map gamma fv -- todo
     tell [Right (f', x, closure, e')]
     return $ EFun1 f' x e' t'
analyze (EApp1 e0 e1 t) =
  do e0' <- analyze e0
     e1' <- analyze e1
     t'  <- freshATp t
     (AArrow arg _ res) <- return $ annotation1 e0'
     annotation1 e1' `subtype` arg
     res             `subtype` t'
     return $ EApp1 e0' e1' t'

-- Utility function for checking subset inclusion
subset :: FlowSet -> FlowSet -> Bool
subset s1 s2 = all (`elem` s2) s1

type TpMap = Map.Map I FlowSet

-- Compute value of label-set expression in effect map
evalPhi :: Phi -> TpMap -> Maybe FlowSet
evalPhi (Varphi i) fm = Map.lookup i fm
evalPhi (Pi    fs)  _ = Just fs

-- Check a single constraint.
--   If everything is fine we return nothing.
--   Otherwise, we return an updated map which may satisfy the constraints.
--   On error: Something went terribly wrong, since the set of function names
--   is finite !
checkConstraint :: Constraint -> TpMap -> Maybe TpMap
checkConstraint (Subset phi0 phi1) fm =
  let (Just phi0') = evalPhi phi0 fm
      (Just phi1') = evalPhi phi1 fm
  in if   phi0' `subset` phi1'
     then Nothing
     else
       case phi1 of
         Varphi i -> Just $ Map.insert i (phi0' `union` phi1') fm
         _        -> error "Unhandled form/Internal error"

-- Main solver function (first arg is number of variables)
solve :: Int -> [Constraint] -> Maybe TpMap
solve n cs =
  let iter [] tm       = return tm
      iter (c' : cs') tm =
        case checkConstraint c' tm of
          Nothing  -> iter cs' tm  -- check remaining constraints
          Just tm' -> iter cs  tm' -- re-check all constraints
  in  iter cs $ Map.fromList $ map (flip (,) []) [0..(n-1)]

-- Applies the analyses, and returns the maps and annotated expression.
refine :: L1 a -> (L1 (ATp Phi), TpMap, FunMap)
refine p =
  let (p', _) = infere_types_in p
      g0 x = error $ "variable " ++ x ++ " was unbound in gamma3"
      ref (program, state, log) =
        let constraints = map fromLeft'  $ filter isLeft log
            fundefs     = map fromRight' $ filter (not . isLeft) log
        in (program, solve (phi state) constraints, fundefs)
      (p'', cs, fm) = ref $ runRWS (analyze p') g0 (S2 {fid = const 0, phi = 0})
  in case cs of
       Nothing  -> error "internal error . unsolvable constraints"
       Just cs' -> (p'', cs', funMap fm)

---------------------------------------------------
-- Control Flow Based Transformation
---------------------------------------------------

-- We map function names to their corresponding function body
-- f : Function name
-- x : Formal parameter name
-- c : Closure of f
-- e : The expression that f evaluates to.
type FunMap = Map.Map F (X, Closure2, E1 (ATp Phi))
funMap :: [FunBody] -> FunMap
funMap bodys = Map.fromList $ map (\(f, x, c, e) -> (f, (x, c, e))) bodys

-- Extract apply-function name from set of possible functions
fname :: [F] -> F
fname fs = "app'" ++ intercalate "or" fs

-- Extract type for L2 from annotated type.
datatype :: ATp a -> Tp2
datatype ANat = TSimple $ TNat2
datatype _    = TSimple $ TData2 "lam"

-- Extracts the relevant datatypes for L2 from the function bodys.
ddCFA :: TpMap -> FunMap -> DD
ddCFA tm fm =
  let sets  = nub $ sort $ map (sort . snd) (Map.toList tm)
      sets' = filter (\x -> length x == 1) sets
      clos  = map (map (\x -> (x, sel2 $ fromJust $ Map.lookup x fm))) sets'
      clos' = map (map (\(x, t) -> (x, map (datatype . snd) t))) clos
  in ("lam", (intercalate [] clos') ++ [("dead_code", [])])

-- Extracts the relevant function definitions for L2 from the result of refine.
fdCFA :: TpMap -> FunMap -> [FD Tp2]
fdCFA tm fm =
  let sets' = nub $ sort $ map (sort . snd) (Map.toList tm)
      sets  = filter (([]/=)) sets'
      funs  = map fname sets
      bodys = map (map (\f -> (f, fromJust $ Map.lookup f fm))) sets
      defPat x =
        case Map.lookup x fm of
          Nothing   -> VarPat x
          Just    c -> ConsturctorPat (x, map (defPat . fst) (sel2 c))
      defTuple (f, (x, c, e)) =
        (TuplePat [ConsturctorPat (f, map (defPat . fst) c), VarPat x], e)
      defs  = map (map defTuple) bodys
      defs' = map (map (\(pat, e) -> (pat, translate2 (tm, fm) e))) defs
  in  zip funs defs'

-- if (phi = empty set), it means that the function is never applied,
-- and we can dispose of it
used :: ATp [F] -> Bool
used (ANat         ) = True
used (AArrow _ [] _) = False
used (AArrow f _  g) = used f && used g

translate2 :: (TpMap, FunMap) -> E1 (ATp Phi) -> E2 Tp2
translate2 m (EVar1  f t)      =
  case Map.lookup f (snd m) of
    Nothing -> EVar2 f $ datatype t -- x was a variable name (let-bound)
    Just  (x, _, e) ->              -- x was a function name (fun-bound)
      translate2 m (EFun1 f x e t)  -- we already handled this elsewhere.
translate2 _ (ENat1  n _)      = ENat2  n                 nat
translate2 m (ESucc1 e _)      = ESucc2 (translate2 m e)  nat
translate2 m (EPred1 e _)      = EPred2 (translate2 m e)  nat
translate2 m (EIf1 e0 e1 e2 t) =
  let tr = translate2 m in EIf2 (tr e0) (tr e1) (tr e2) $ datatype t
translate2 m (ELet1 x e0 e1 t) =
  let tr = translate2 m in ELet2 x      (tr e0) (tr e1) $ datatype t
translate2 m (EFun1 f _ _ t)   =
  let (c, t') = unzip $ sel2 $ fromJust $ Map.lookup f $ snd m
      params  = map (translate2 m) $ zipWith EVar1 c $ t'
  in  EDataCon2 (f, params) $ datatype t
translate2 m (EApp1 e0 e1 t)   =
  let tr                 = translate2 m
      (AArrow t0 phi t1) = annotation1 e0
      tp                 = fo_pair (datatype t0) (datatype t1)
      f                  = (fname $ sort $ nub $ fromJust $ evalPhi phi $ fst m)
  in case f of
       "app'" -> EDataCon2 ("dead_code", []) $ TSimple $ TData2 "lam"
       _      -> EApp2 f (ETuple2 [tr e0, tr e1] tp) $ datatype t

defunctionalizeCFA :: L1 a -> L2 Tp2
defunctionalizeCFA p =
  let (p', _)       = infere_types_in p
      (p'', tm, fm) = refine p'
  in Program ([ddCFA tm fm], fdCFA tm fm, translate2 (tm, fm) p'')

---------------------------------------------------
-- Type inferrence for Language 1
---------------------------------------------------

-- We introduce an open type \hat\tau for L1.
data TpO = Tau1 Tp1 | OpenArrow TpO TpO | Hole I deriving (Show, Eq)

-- We then collect type constraints, AND a collection of target types
-- Which will needed after the translation.
data TpInfo =
    DotEq TpO TpO -- t0 must equal t1.
  | LamT TpO      -- lambda i must have type t.
  deriving (Show)

-- The Constraint monad:
type I      = Int                    -- [i] for the "hole" in open types.
type Gamma  = X -> TpO               -- Open typing environment.
type CM a   = RWS Gamma [TpInfo] I a

-- Returns the set of unification variables from an open type.
uv :: TpO -> [I]
uv (Tau1 _         ) = []
uv (OpenArrow t0 t1) = uv t0 ++ uv t1
uv (Hole i         ) = [i]

-- Basic utility functions:
hole :: CM TpO
hole = Hole <$> (get >>= \i -> put (i + 1) >> return i)

fun :: TpO -> CM ()
fun t = tell [LamT t]

bind :: X -> TpO -> Gamma -> Gamma
bind x t s = \y -> if x == y then t else s y

dotEqET :: L1 TpO -> TpO -> CM ()
dotEqET e t = tell [DotEq (annotation1 e) t]

dotEqEE :: L1 TpO -> L1 TpO -> CM ()
dotEqEE e0 e1 = tell [DotEq (annotation1 e0) (annotation1 e1)]

-- This function annotates untyped programs in L1 with open types.
-- Additionally it collects type constraints.
annotate :: L1 a -> CM (L1 TpO)
annotate (EVar1  x _) = ask >>= \s -> return $ EVar1 x $ s x
annotate (ENat1  n _) = return $ ENat1  n $ Tau1 TNat1
annotate (ESucc1 e _) =
  do et <- annotate e
     dotEqET et         (Tau1 TNat1)
     return $ ESucc1 et (Tau1 TNat1)
annotate (EPred1 e _) =
  do et <- annotate e
     dotEqET et         (Tau1 TNat1)
     return $ EPred1 et (Tau1 TNat1)
annotate (EIf1 e0 e1 e2 _) =
  do et0    <- annotate e0
     et1    <- annotate e1
     et2    <- annotate e2
     dotEqET et0 (Tau1 TNat1)
     dotEqEE et1 et2
     return $ EIf1 et0 et1 et2 (annotation1 et1)
annotate (ELet1 x e0 e1 _) =
  do et0 <- annotate e0
     et1 <- local (bind x (annotation1 et0)) $ annotate e1
     return $ ELet1 x et0 et1 (annotation1 et1)
annotate (EFun1 f x e _) =
  do t1 <- hole
     t2 <- hole
     ft <- return $ OpenArrow t1 t2
     et <- local (bind f ft) $ local (bind x t1) $ annotate e
     dotEqET et t2
     fun ft
     return $ EFun1 f x et ft
annotate (EApp1 e0 e1 _) =
  do t   <- hole
     et0 <- annotate e0
     et1 <- annotate e1
     dotEqET et0 (OpenArrow (annotation1 et1) t)
     return $ EApp1 et0 et1 t

-- Solves type constraints, as described in lecture 10 of SaT.
solveT1 :: [TpInfo] -> Maybe ([(I, TpO)], [TpO])
solveT1 [] = Just ([], [])
solveT1 ((DotEq t0 t1) : info) =
  case (t0, t1) of
    (Tau1 _, OpenArrow _ _) -> Nothing
    (OpenArrow _ _, Tau1 _) -> Nothing
    (Tau1 t0, Tau1 t1)      -> if   t0 == t1
                                then solveT1 info
                                else Nothing
    (OpenArrow t0 t1, OpenArrow t0' t1') ->
      solveT1 ((DotEq t0 t0') : (DotEq t1 t1') : info)
    (Hole i, t0) -> if   i `elem` (uv t0)
                    then (if   (Hole i) /= t0
                          then Nothing
                          else solveT1 info)
                    else do (c', ti) <- solveT1 (substT1 t0 i info)
                            return $ (c' ++ [(i, t0)], ti)
    (t0, Hole i) -> if   i `elem` (uv t0)
                    then (if   (Hole i) /= t0
                          then Nothing
                          else solveT1 info)
                    else do (c', ti) <- solveT1 (substT1 t0 i info)
                            return $ ((i, t0) : c', ti)
solveT1 ((LamT t) : info) =
  do (c, ti) <- solveT1 info
     return $ if t `elem` ti then (c, ti) else (c, t : ti)

-- Substitutes (hole i) with t when remaining type-constraints
substT1 :: TpO -> I -> [TpInfo] -> [TpInfo]
substT1 _ _ []                   = []
substT1 t i ((DotEq t0 t1) : ti) =
  (DotEq (subst1 t i t0) (subst1 t i t1)) : (substT1 t i ti)
substT1 t i (t0 : ti) = t0 : (substT1 t i ti)

-- Substitutes [i] with t.
subst1 :: TpO -> I -> TpO -> TpO
subst1 t i (Hole j)          = if i == j then t else Hole j
subst1 t i (OpenArrow t0 t1) = OpenArrow (subst1 t i t0) (subst1 t i t1)
subst1 _ _ t0                = t0

-- Substitutes open types with types from language 1
subst :: (I -> TpO) -> TpO -> Tp1
subst _ (Tau1 t) = t
subst s (Hole i) = subst s (s i)
subst s (OpenArrow t0 t1) = TArrow1 (subst s t0) (subst s t1)

-- Fold a substitution from a list of holes.
substitution :: [(I, TpO)] -> I -> TpO
substitution =
  foldl (\f (i, t) -> \j -> if i == j then t else f j) (const $ Tau1 TNat1)

-- Main type inferens function for programs in L1:
--   If the input program is not typable, then this throws an error.
--   Otherwise it returns an anotated program,
--   together with a list of possible function-types (for the defunctionalization).
infere_types_in :: L1 a -> (L1 Tp1, [Tp1])
infere_types_in program =
  let gamma0 x             = error $ x ++ " is unbound!"
      (pt, _, info)        = runRWS (annotate program) gamma0 0
      (bindings, funTypes) =
        case solveT1 info of
          Nothing          -> error "untypeable program"
          Just    solution -> solution
      s                    = subst $ substitution bindings
      typedProgram         = fmap s pt
  in (typedProgram, nub $ map s funTypes)

---------------------------------------------------
-- Parser for L1.
---------------------------------------------------

whitespace :: Parser ()
whitespace = skipMany space

lexeme :: Parser a -> Parser a
lexeme p = p >>= \x -> whitespace >> return x

symbol :: String -> Parser ()
symbol s = void $ lexeme $ string s

parens :: Parser a -> Parser a
parens p = between (symbol "(") (symbol ")") p

pre, post :: String -> Parser a -> Parser a
pre  s p = symbol s >> p
post s p = p >>= \x -> symbol s >> return x

rws1 :: [String] -- reserved keywords for language 1
rws1 = [ "succ", "pred", "if", "then", "else", "let", "in", "fun" ]

pId :: [String] -> Parser String
pId rws = try $
  do x <- lexeme $ (:) <$> letter <*> many (choice [letter, digit, char '_'])
     guard $ x `notElem` rws
     return x

pNat :: Parser Nat
pNat = lexeme $ read <$> many1 digit

pL1 :: Parser (L1 ())
pL1 = choice
  [ chainl1 simple (return $ eApp1)
  , pre "succ" $ eSucc1 <$> parens pL1
  , pre "pred" $ ePred1 <$> parens pL1
  , eIfz1 <$> (pre "if" pL1) <*> (pre "then" pL1) <*> (pre "else" pL1)
  , eFun  <$> (pre "fun" $ pId rws1) <*> pId rws1 <*> (pre "=" pL1)
  , eFun  <$> (pre "\\" $ return "fn'") <*> pId rws1 <*> (pre "->" pL1)
  , eLet  <$> (pre "let" $ pId rws1) <*> (pre "=" pL1) <*> (pre "in" pL1)
  ] <?> "expression"
  where
    simple = choice $
      [ (eVar1 <$> pId rws1) <?> "identifier"
      , (eNat1 <$> pNat    ) <?> "natural number"
      , parens pL1
      ]

---------------------------------------------------
-- Interpreter
---------------------------------------------------

is_value1 :: E1 a -> Bool
is_value1 (ENat1 _ _    ) = True
is_value1 (EFun1 _ _ _ _) = True
is_value1 _               = False

subst_e1 :: X -> E1 a -> E1 a -> E1 a
subst_e1 x v (EVar1 x' a) = if x == x' then v else (EVar1 x' a)
subst_e1 _ _ (ENat1 n  a) = (ENat1 n  a)
subst_e1 x v (ESucc1 e a) = (ESucc1 (subst_e1 x v e) a)
subst_e1 x v (EPred1 e a) = (EPred1 (subst_e1 x v e) a)
subst_e1 x v (EIf1 e0 e1 e2 a) =
  EIf1 (subst_e1 x v e0) (subst_e1 x v e1) (subst_e1 x v e2) a
subst_e1 x v (ELet1 x' e0 e1 a) =
  if   x == x'
  then (ELet1 x' (subst_e1 x v e0)               e1  a)
  else (ELet1 x' (subst_e1 x v e0) (subst_e1 x v e1) a)
subst_e1 x v (EFun1 f x' e a) =
  if   x == f || x == x'
  then (EFun1 f x' e a)
  else (EFun1 f x' (subst_e1 x v e) a)
subst_e1 x v (EApp1 e0 e1 a) = EApp1 (subst_e1 x v e0) (subst_e1 x v e1) a

step :: E1 () -> E1 ()
step (ESucc1 (ENat1 n _) _) = ENat1 (n + 1) ()
step (ESucc1 e _) = (ESucc1 (step e) ())
step (EPred1 (ENat1 0 _) _) = ENat1 0 ()
step (EPred1 (ENat1 n _) _) = ENat1 (n - 1) ()
step (EPred1 e _) = (EPred1 (step e) ())
step (EIf1 (ENat1 n _) e1 e2 _) = if n /= 0 then e1 else e2
step (EIf1 e0 e1 e2 _) = (EIf1 (step e0) e1 e2 ())
step (ELet1 x e0 e1 _) =
  if   is_value1 e0
  then subst_e1 x e0 e1
  else ELet1 x (step e0) e1 ()
step (EApp1 (EFun1 f x e0 a) e1 _) =
  if   is_value1 e1
  then subst_e1 f (EFun1 f x e0 a) $ subst_e1 x e1 $ e0
  else EApp1 (EFun1 f x e0 a) (step e1) ()
step (EApp1 e0 e1 _) = EApp1 (step e0) e1 ()
step _ = error "ups, this term is stuck !!"

eval :: E1 () -> E1 ()
eval e = if is_value1 e then e else eval (step e)

---------------------------------------------------
-- Simple Utility Functions
---------------------------------------------------
-- This collection of simple functions have been
-- moved towards the bottom of the program,
-- not to clutter the remaining program with
-- unnessesary details.
---------------------------------------------------

fromLeft'  (Left a)  = a
fromLeft'  _         = error "unexpected Right!"
fromRight' (Right a) = a
fromRight' _         = error "unexpected Left!"

-- Expressions annotated with void in L1.
eVar1  x     = EVar1 x      ()
eNat1  n     = ENat1 n      ()
eSucc1 e     = ESucc1 e     ()
ePred1 e     = EPred1 e     ()
eIfz1 p c a  = EIf1 p c a   ()
eLet  x e e' = ELet1 x e e' ()
eFun  f x e  = EFun1 f x e  ()
eApp1 f x    = EApp1 f x    ()

-- Simpler type constructors for L2.
nat                               = TSimple $ TNat2
fo_fun (TSimple t0) (TSimple t1)  = TArrowFO2 t0 t1
fo_fun  _            _            =
  error "first order functions do not compose like that!"
fo_pair (TSimple t0) (TSimple t1) = TSimple $ TTuple2 [t0, t1]
fo_pair _            _            =
    error "first order do not belong in pairs compose like that!"
datacon                           = TSimple . TData2

---------------------------------------------------
-- A Pretty Printing Monad {^o^}
---------------------------------------------------

type PPIndent a = RWS I [Char] (I, I) a

get_indent, get_pos, tab_size :: PPIndent I
get_indent = get >>= return . fst
get_pos    = get >>= return . snd
tab_size   = ask

set_indent, set_pos :: I -> PPIndent ()
set_indent i = get >>= \(_, j) -> put (i, j)
set_pos    j = get >>= \(i, _) -> put (i, j)

write_char :: Char -> PPIndent ()
write_char c =
  do tell [c]
     case c of
       '\n' -> set_pos 0
       _    -> get_pos >>= set_pos . (+1)

write_string :: String -> PPIndent ()
write_string (c : s) = write_char c >> write_string s
write_string _       = return ()

inc_indent :: PPIndent ()
inc_indent =
  do i <- tab_size
     x <- get_indent
     set_indent $ x + i

dec_indent :: PPIndent ()
dec_indent =
  do i <- tab_size
     x <- get_indent
     set_indent $ x - i

nl :: PPIndent ()
nl = do i <- get_indent ; write_string $ '\n' : replicate i ' '

block :: PPIndent a -> PPIndent a
block p =
  do inc_indent
     nl
     x <- p
     dec_indent
     return x

pprint :: PPIndent () -> IO ()
pprint pp = putStr $ (\(_, _, x) -> x) $ runRWS pp 2 (0, 0)

---------------------------------------------------
-- Additional Instances For 'Show'.
---------------------------------------------------

instance Show Tp1 where
  show (TNat1        ) = "nat"
  show (TArrow1 t0 t1) = "(" ++ show t0 ++ "->" ++ show t1 ++ ")"

instance Show Tp2' where
  show (TNat2    ) = "nat"
  show (TData2  d) = d
  show (TTuple2 p) = "(" ++ intercalate " * " (map show p) ++ ")"

instance Show a => Show (ATp a) where
  show (ANat          ) = "nat"
  show (AArrow t0 a t1) =
    "(" ++ show t0 ++ "-{" ++ show a ++ show "}->" ++ show t1 ++ ")"

instance Show Tp2 where
  show (TSimple t      ) = show t
  show (TArrowFO2 t0 t1) = show t0 ++ " -> " ++ show t1

show' :: Show a => a -> String
show' x = if showTypes then " : " ++ show x else ""

instance Show a => Show (E1 a) where
  show e = (\(_, _, x) -> x) $ runRWS (ppe1 show' e) 2 (0, 0)

ppe1 :: Show a => (a -> String) -> E1 a -> PPIndent ()
ppe1 s (EVar1  x a) = write_string $ x      ++ s a
ppe1 s (ENat1  n a) = write_string $ show n ++ s a
ppe1 s (ESucc1 e a) = do write_string "succ("
                         ppe1 s e
                         write_string $ ")" ++ s a
ppe1 s (EPred1 e a) = do write_string "pred("
                         ppe1 s e
                         write_string $ ")" ++ s a
ppe1 s (EIf1 e0 e1 e2 a) =
  do write_string "(ifz  "
     ppe1 s e0
     nl >> write_string " then " >> ppe1 s e1
     nl >> write_string " else " >> ppe1 s e2
     nl >> (write_string $ ")" ++ s a)
ppe1 s (ELet1 f e0 e1 a) =
  do write_string $ "let " ++ f ++ s a ++ " ="
     block $ ppe1 s e0
     nl
     write_string "in"
     block $ ppe1 s e1
ppe1 s (EFun1 f x e a) =
  do write_string $ "(fun " ++ f ++ " " ++ x ++ " ="
     block $ ppe1 s e
     write_string $ ")" ++ s a
ppe1 s (EApp1 e0 e1 a) =
  do write_string "(" >> ppe1 s e0 >> write_string " " >> ppe1 s e1
     write_string $ ")" ++ s a

-- --------------------------------------------------------
-- -- SML Backend
-- --------------------------------------------------------

e2ToSML :: E2 a -> PPIndent ()
e2ToSML (EVar2  x _) = write_string x
e2ToSML (ENat2  n _) = write_string $ show n
e2ToSML (ESucc2 e _) =
  do write_string "(succ("
     e2ToSML e
     write_string $ "))"
e2ToSML (EPred2 e _) =
  do write_string "(pred("
     e2ToSML e
     write_string $ "))"
e2ToSML(EIf2 e0 e1 e2 _) =
  do write_string "(if  ("
     e2ToSML e0
     write_string ") <> 0"
     nl >> write_string " then " >> e2ToSML e1
     nl >> write_string " else " >> e2ToSML e2
     nl >> write_string ")"
e2ToSML(ELet2 f e0 e1 _) =
  do write_string $ "let val " ++ f ++ " ="
     block $ e2ToSML e0
     nl
     write_string "in"
     block $ e2ToSML e1
     nl
     write_string "end"
e2ToSML(EApp2 f e _) = write_string f >> e2ToSML e
e2ToSML(EDataCon2 (x, es) _) =
  do write_string $ x
     case es of
       [] -> return ()
       _  -> parensSML $ separated "," e2ToSML es
e2ToSML(ETuple2 es _) =
  do write_string "("
     separated "," e2ToSML es
     write_string ")"

parensSML e =
  do write_string "("
     e
     write_string ")"

separated _ _ []       = return ()
separated _ p [x]      = p x
separated d p (x : xs) =
  do p x
     write_string $ d ++ " "
     separated d p xs

tp2ToSML :: Tp2 -> PPIndent ()
tp2ToSML (TSimple TNat2)      = write_string "nat"
tp2ToSML (TSimple (TData2 d)) = write_string d
tp2ToSML _ = error "sml : this should not have been a function!"

c2SML (c, tps) =
  do write_string $ c
     case tps of
       [] ->    return ()
       _  -> do write_string " of ("
                separated " *" tp2ToSML tps
                write_string ")"

ddSML :: Bool -> DD -> PPIndent ()
ddSML b (d, c2) =
  do write_string $ (if b then "datatype " else "and      ") ++ d ++ " ="
     block $ write_string "  " >> write_constructors c2
     nl
  where
    write_constructors []       = error "no type constructors !!"
    write_constructors [c]      = c2SML c
    write_constructors (c : cs) =
      do c2SML c
         nl
         write_string "| "
         write_constructors cs

fdSML :: Show a => (Bool, Bool) -> FD a -> PPIndent ()
fdSML _     (_,    []) = return ()
fdSML flags (f, (p, e) : cs) =
  do case flags of
       (True, True) -> write_string "fun "
       (_   , True) -> write_string "and "
       _            -> write_string "  | "
     write_string  $ f ++ " "
     write_pattern $ fst $ StateM.runState (safePattern p) []
     write_string " ="
     set_indent 5
     nl
     e2ToSML e
     set_indent 0
     nl
     fdSML (False, False) (f, cs)

write_pattern (VarPat   x ) = write_string x
write_pattern (TuplePat ps) =
  do write_string "("
     write_patterns ps
     write_string ")"
write_pattern (ConsturctorPat (c, ps)) =
  do write_string c
     case ps of
       [] ->    return ()
       _  -> do write_string "("
                write_patterns ps
                write_string ")"
write_patterns []  = return ()
write_patterns [x] = write_pattern x
write_patterns (x : xs) =
  do write_pattern  x
     write_string   ", "
     write_patterns xs

type SafePM = StateM.State [X]

is_known :: X -> SafePM Bool
is_known x =
  do known <- StateM.get
     return $ x `elem` known

i_know_this :: X -> SafePM ()
i_know_this x = StateM.get >>= StateM.put . (x:)

safePattern :: Pattern -> SafePM Pattern
safePattern (VarPat x) =
  do b <- is_known x
     i_know_this x
     if b
       then return $ VarPat "_"
       else return $ VarPat x
safePattern (ConsturctorPat (f, c)) =
  do c' <- mapM safePattern c
     return $ ConsturctorPat (f, c')
safePattern (TuplePat t) =
  do t' <- mapM safePattern t
     return $ TuplePat t'


writeSML :: Show a => Show b => L1 a -> L2 b -> IO ()
writeSML p (Program (typedefs, fundefs, p')) =
    do putStrLn "(* **************************************************** *)"
       putStrLn "(*               Original program                       *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       putStrLn "(*"
       putStrLn $ show p
       putStrLn "*)"
       putStrLn ""
       putStrLn "(* **************************************************** *)"
       putStrLn "(*               Evaluated to                           *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       putStr   "(* "
       putStr   $ show $ eval (fmap (const ()) p)
       putStrLn " *)"
       putStrLn ""
       putStrLn "(* **************************************************** *)"
       putStrLn "(*        Basic operations on natural numbers           *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       putStrLn "type nat     = int"
       putStrLn "fun  pred(n) = if n <> 0 then n - 1 else 0"
       putStrLn "fun  succ(n) = n + 1"
       putStrLn ""
       putStrLn "(* **************************************************** *)"
       putStrLn "(*             Type constructors                        *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       if        length typedefs >= 1
         then do pprint $ ddSML True  $ head typedefs
                 pprint nl
         else    return ()
       if        length typedefs >  1
         then do mapM_ (\x -> (pprint $ ddSML False x) >> pprint nl) $
                   tail typedefs
         else    return ()
       putStrLn "(* **************************************************** *)"
       putStrLn "(*             Apply functions                          *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       if        length fundefs >= 1
         then do pprint $ fdSML (True, True)  $ head fundefs
                 pprint nl
         else    return ()
       if        length fundefs >  1
         then do mapM_ (\x -> (pprint $ fdSML (False, True) x) >> pprint nl) $
                   tail fundefs
         else    return ()
       putStrLn "(* **************************************************** *)"
       putStrLn "(*             Tranformed expression                    *)"
       putStrLn "(* **************************************************** *)"
       putStrLn ""
       putStr   "val result' =" >> (pprint $ block $ e2ToSML p')
       putStrLn "\n"
       putStrLn "(* **************************************************** *)"
       putStrLn "(*             End of transformation                    *)"
       putStrLn "(* **************************************************** *)"

l2SMLNaive :: Show a => L1 a -> IO ()
l2SMLNaive program =
  let p1 = fst $ infere_types_in program
      p2 = defunctionalizeNaive p1
  in writeSML p1 p2

l2SMLCFA :: Show a => L1 a -> IO()
l2SMLCFA program =
  let p1 = fst $ infere_types_in program
      p2 = defunctionalizeCFA p1
  in writeSML p1 p2

main :: IO ()
main =
  do args <- getArgs
     if length args /= 2
       then fail "this program takes a flag and filename as argument."
       else return ()
     program <- parseFromFile (whitespace >> pL1) $ head $ tail args
     case (program, head args) of
       (Left e,  _)  -> fail $ show e
       (Right p, "-naive")      -> l2SMLNaive p
       (Right p, "-cfa")        -> l2SMLCFA p
       _                        -> fail "unknown command !"
