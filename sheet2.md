## Parser library: Tests
{: .spec }
    -- We import the first naive implementation as the specification.
    import qualified Parser1 as Spec (P, symbol, (+++), pfail, parse)
    -- | We want to generate and show arbitrary parsers. To do this
    --   we restrict ourselves to parsers of type P Bool Bool and build
    --   a datatype to model these.
    data ParsBB
      = Plus ParsBB ParsBB
      | Fail | Return Bool | Symbol | Bind ParsBB B2ParsBB
    -- | Instead of arbitrary functions (which quickCheck can generate but
    -- not check equality of or print) we build a datatype modelling a few
    -- interesting functions.
    data B2ParsBB
      = K ParsBB          -- \_ -> p
      | If ParsBB ParsBB  -- \x -> if x then p1 else p2
    -- Applying a function to an argument.
    apply :: B2ParsBB -> Bool -> ParsBB
    apply (K p)      _ = p
    apply (If p1 p2) x = if x then p1 else p2
    -- | We can show elements in our model, but not the parsers from the
    --   implementation.
    instance Show ParsBB where
      showsPrec n p = case p of
        Fail   -> showString "pfail"
        Symbol -> showString "symbol"
        Return x -> showParen (n > 2) $ showString "return " . shows x
        Plus p q -> showParen (n > 0) $ showsPrec 1 p
                                      . showString " +++ "
                                      . showsPrec 1 q
        Bind p f -> showParen (n > 1) $ showsPrec 2 p
                                      . showString " >>= "
                                      . shows f
    -- and we can show our functions. That would have been harder if
    -- we had used real functions.
    instance Show B2ParsBB where
      show (K p)      = "\\_ -> " ++ show p
      show (If p1 p2) = "\\x -> if x then " ++ show p1 ++
                                   " else " ++ show p2
    -- | Generating an arbitrary parser. Parameterised by a size argument
    --   to ensure that we don't generate infinite parsers.
    genParsBB :: Int -> Gen ParsBB
    genParsBB 0 = oneof [ return Fail
                        , Return <$> arbitrary
                        , return Symbol ]
    genParsBB n =
      frequency $
        [ (1, genParsBB 0)
        , (3, Plus <$> gen2 <*> gen2)
        , (5, Bind <$> gen2 <*> genFun2)
        ]
      where
        gen2    = genParsBB (n `div` 2)
        genFun2 = genFun (n `div` 2)
    -- | Generating arbitrary functions.
    genFun :: Int -> Gen B2ParsBB
    genFun n = oneof $
      [ K  <$> genParsBB n
      , If <$> gen2 <*> gen2 ]
      where gen2 = genParsBB (n `div` 2)
    instance Arbitrary ParsBB where
      arbitrary = sized genParsBB
      -- Shrinking is used to get minimal counter examples and is very
      -- handy.  The shrink function returns a list of things that are
      -- smaller (in some way) than the argument.
      shrink (Plus p1 p2) = p1 : p2 :
        [ Plus p1' p2 | p1' <- shrink p1 ] ++
        [ Plus p1 p2' | p2' <- shrink p2 ]
      shrink Fail         = [ Return False ]
      shrink (Return x)   = []
      shrink Symbol       = [ Return False ]
      shrink (Bind p k)   = p : apply k False : apply k True :
        [ Bind p' k | p' <- shrink p ] ++
        [ Bind p k' | k' <- shrink k ]
    instance Arbitrary B2ParsBB where
      arbitrary = sized genFun
      shrink (K p)      = [ K p | p <- shrink p ]
      shrink (If p1 p2) = K p1 : K p2 :
        [ If p1 p2 | p1 <- shrink p1 ] ++
        [ If p1 p2 | p2 <- shrink p2 ]
    -- | We can turn a parser in our model into its specification...
    spec :: ParsBB -> Spec.P Bool Bool
    spec Symbol        = Spec.symbol
    spec (Return x)    = return x
    spec (Plus p1 p2)  = spec p1   Spec.+++   spec p2
    spec Fail          = Spec.pfail
    spec (Bind p k)    = spec p >>= \x -> spec (apply k x)
    -- | ... or we can compile to a parser from the implementation we're
    --   testing.
    compile :: ParsBB -> P Bool Bool
    compile Symbol        = symbol
    compile (Return x)    = return x
    compile (Plus p1 p2)  = compile p1 +++ compile p2
    compile Fail          = pfail
    compile (Bind p k)    = compile p >>= compileFun k
    compileFun :: B2ParsBB -> (Bool -> P Bool Bool)
    compileFun k = \x -> compile (apply k x)
    -- Tests
    infix 0 =~=
    -- | When are two parsers equal? Remember that we don't care
    --   about the order of results so we sort the result lists
    --   before comparing.
    -- (=~=) :: P Bool Bool -> P Bool Bool -> Property
    p =~= q = -- forAllShrink arbitrary shrinkNothing $ 
              \s -> parse p s  `bagEq`  parse q s
    bagEq :: Ord a => [a] -> [a] -> Bool
    bagEq xs ys = sort xs == sort ys
    -- We can turn all the laws we had into properties.
    -- Exercise: check all the laws L1 .. L10.
    law1' x f =   return x >>= f   =~=   f x
    law1 x f0 =   return x >>= f   =~=   f x
      where f = compileFun f0
    law2 p0 =     p >>= return   =~=   p
      where p = compile p0
    law3 p0 f0 g0 =  (p >>= f) >>= g  =~=  p >>= (\x -> f x >>= g)
      where p = compile p0
            f = compileFun f0
            g = compileFun g0
    law5 p0 q0 f0 =   (p +++ q) >>= f  =~=  (p >>= f) +++ (q >>= f)
      where p = compile p0
            q = compile q0
            f = compileFun f0
    law9 p0 q0 =      p +++ q  =~=  q +++ p
      where p = compile p0
            q = compile q0
    -- | We can also check that the implementation behaves as the
    --   specification.
    prop_spec p s  = whenFail debug $ lhs  `bagEq`  rhs
      where
        lhs = parse    (compile p) s
        rhs = Spec.parse (spec p)  s
        debug = do putStrLn ("parse    (compile p) s = " ++ show lhs)
                   putStrLn ("Spec.parse (spec p)  s = " ++ show rhs)

## Agda: Prelude
{: .types }
    module Prelude where
    -- Equality
    -- Equality. Note that this definition is very similar to the one
    -- given in AFP 2012 Lecture 7 in Typed.hs.
    infix 4 _≡_
    data _≡_ {A : Set} (x : A) : A → Set where
      refl : x ≡ x
    -- Symmetry. Agda checks [*] that all cases are covered, and that the
    -- function is terminating/productive, because otherwise one could
    -- prove anything.
    -- [*] Unless the Agda implementation is buggy.
    sym : ∀ {A} {x y : A}  →  x ≡ y  →  y ≡ x
    sym refl = refl
    -- Transitivity.
    trans : ∀ {A} {x y z : A}  →  x ≡ y  →  y ≡ z  →  x ≡ z
    trans refl refl = refl
    -- Equality is a congruence: every function preserves equality.
    cong : ∀ {A B} (f : A → B) {x y}  →  x ≡ y  →  f x ≡ f y
    cong f refl  =  refl
    cong₂ : ∀ {A B C} (f : A → B → C) {x y u v} →
            x ≡ y  →  u ≡ v  →  f x u ≡ f y v
    cong₂ f refl refl  =  refl
    -- The unit type
    data Unit : Set where
      unit : Unit
    -- The Maybe type
    data Maybe (A : Set) : Set where
      just     :  A → Maybe A
      nothing  :  Maybe A
    -- Applicative functor application.
    infixl 4  _<$>_   _⊛_
    _⊛_ : ∀ {A B} → Maybe (A → B) → Maybe A → Maybe B
    just f  ⊛ just x   =  just (f x)
    just f  ⊛ nothing  =  nothing
    nothing ⊛ _        =  nothing
    -- Map.
    _<$>_ : ∀ {A B} → (A → B) → Maybe A → Maybe B
    f <$> mx  =  just f  ⊛  mx
    -- A safe variant of fromJust. If the value is nothing, then the
    -- return type is the unit type.
    FromJust : ∀ A → Maybe A → Set
    FromJust A (just _) = A
    FromJust A nothing  = Unit
    fromJust : ∀ {A} (x : Maybe A) → FromJust A x
    fromJust (just x) = x
    fromJust nothing  = unit
    -- Numbers
    -- Unary natural numbers
    data ℕ : Set where -- Agda input mode \bn (bold nat) yields ℕ
      zero : ℕ
      suc  : ℕ → ℕ
    -- Support for natural number literals.
    {-# BUILTIN NATURAL ℕ    #-}
    {-# BUILTIN ZERO    zero #-}
    {-# BUILTIN SUC     suc  #-}
    -- Bounded natural numbers. A value of type Fin n is smaller than n.
    -- Note that there are two ways of creating a number in Fin (suc n)
    -- but no way to create a number in Fin zero.
    data Fin : ℕ → Set where
      zero : ∀ {n} →          Fin (suc n)
      suc  : ∀ {n} → Fin n →  Fin (suc n)
    -- A decision procedure for equality. If the two numbers are equal,
    -- then a proof is returned (just as in Lecture 7 where it was used to
    -- check equality of type codes).
    infix 5 _≟-Fin_
    _≟-Fin_ : ∀ {n} (i j : Fin n) → Maybe (i ≡ j)
    zero   ≟-Fin  zero    =  just refl
    suc i  ≟-Fin  suc j   =  cong suc  <$>  i ≟-Fin j  -- recursive call
    _      ≟-Fin  _       =  nothing
    ----------------------------------------------------------------------
    -- Lists and vectors
    -- Finite lists.
    infixr 5 _∷_
    data List (A : Set) : Set where
      []  : List A
      _∷_ : A → List A → List A
    -- Append.
    infixr 5 _++_
    _++_ : ∀ {A} → List A → List A → List A
    []       ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
    -- Vectors. A vector of type Vec A n has length n.
    data Vec (A : Set) : ℕ → Set where
      []  : Vec A zero
      _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
    -- Safe lookup.
    lookup : ∀ {A n} → Fin n → Vec A n → A
    lookup zero    (x ∷ xs) = x
    lookup (suc i) (x ∷ xs) = lookup i xs

## Agda: Theorem proving by reflection
{: .types }
    -- A very simple theorem prover, using the technique of proof by
    -- reflection
    open import Prelude
    module Proof-by-reflection
      -- The module is parametrised by a monoid; a type and some
      -- operations satisfying certain properties.
      {A              : Set}
      (identity       : A)
      (_∙_            : A → A → A)
      (left-identity  : ∀ x → (identity ∙ x) ≡ x)
      (right-identity : ∀ x → (x ∙ identity) ≡ x)
      (assoc          : ∀ x y z → (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z))
      -- Some elements of the type, only used in examples.
      (x y            : A)
      where
    -- The goal is to automatically prove equality of monoid expressions.
    ----------------------------------------------------------------------
    -- Monoid expressions
    -- There is one constructor for every operation, plus one for
    -- variables; there may be at most n variables.
    data Expr (n : ℕ) : Set where
      var : Fin n → Expr n
      id  : Expr n
      _⊕_ : Expr n → Expr n → Expr n
    -- An environment contains one value for every variable.
    Env : ℕ → Set
    Env n = Vec A n
    -- The semantics of an expression is a map from an environment to a
    -- value.
    ⟦_⟧ : ∀ {n} → Expr n → Env n → A
    ⟦ var x   ⟧ ρ = lookup x ρ
    ⟦ id      ⟧ ρ = identity
    ⟦ e₁ ⊕ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ
    -- Examples.
    e₁ : Expr 2
    e₁ = (var zero ⊕ id) ⊕ var (suc zero)
    e₂ : Expr 2
    e₂ = id ⊕ (var zero ⊕ (var (suc zero) ⊕ id))
    ρ : Vec A 2
    ρ = x ∷ y ∷ []
    ex₁ = ⟦ e₁ ⟧ ρ
    -- Normal forms
    -- A normal form is a list of variables.
    Normal : ℕ → Set
    Normal n = List (Fin n)
    -- The semantics of a normal form.
    ⟦_⟧′ : ∀ {n} → Normal n → Env n → A
    ⟦ []     ⟧′ ρ = identity
    ⟦ x ∷ nf ⟧′ ρ = lookup x ρ ∙ ⟦ nf ⟧′ ρ
    -- A normaliser.
    normalise : ∀ {n} → Expr n → Normal n
    normalise (var x)   = x ∷ []
    normalise id        = []
    normalise (e₁ ⊕ e₂) = normalise e₁ ++ normalise e₂
    -- The normaliser is homomorphic with respect to _++_/_∙_.
    homomorphic : ∀ {n} (nf₁ nf₂ : Normal n) (ρ : Env n) →
                  ⟦ nf₁ ++ nf₂ ⟧′ ρ ≡ (⟦ nf₁ ⟧′ ρ ∙ ⟦ nf₂ ⟧′ ρ)
    homomorphic []        nf₂ ρ = sym (left-identity (⟦ nf₂ ⟧′ ρ))
    homomorphic (x ∷ nf₁) nf₂ ρ =
      trans (cong (λ y → lookup x ρ ∙ y) (homomorphic nf₁ nf₂ ρ))
            (assoc (lookup x ρ) (⟦ nf₁ ⟧′ ρ) (⟦ nf₂ ⟧′ ρ))
    -- The normaliser preserves the semantics of the expression.
    normalise-correct :
      ∀ {n} (e : Expr n) (ρ : Env n) → ⟦ normalise e ⟧′ ρ ≡ ⟦ e ⟧ ρ
    normalise-correct (var x)   ρ = right-identity (lookup x ρ)
    normalise-correct id        ρ = refl
    normalise-correct (e₁ ⊕ e₂) ρ =
      trans (homomorphic (normalise e₁) (normalise e₂) ρ)
            (cong₂ _∙_ (normalise-correct e₁ ρ) (normalise-correct e₂ ρ))
    -- Thus one can prove that two expressions are equal by proving that
    -- their normal forms are equal.
    normalisation-theorem :
      ∀ {n} (e₁ e₂ : Expr n) (ρ : Env n) →
      ⟦ normalise e₁ ⟧′ ρ ≡ ⟦ normalise e₂ ⟧′ ρ →
      ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
    normalisation-theorem e₁ e₂ ρ eq =
      trans (sym (normalise-correct e₁ ρ)) (
      trans eq
            (normalise-correct e₂ ρ))
    ex₂ = normalisation-theorem e₁ e₂ ρ refl
    -- The prover
    -- We can decide if two normal forms are equal.
    infix 5 _≟_
    _≟_ : ∀ {n} (nf₁ nf₂ : Normal n) → Maybe (nf₁ ≡ nf₂)
    []         ≟ []         = just refl
    (x₁ ∷ nf₁) ≟ (x₂ ∷ nf₂) = cong₂ _∷_ <$> x₁ ≟-Fin x₂ ⊛ nf₁ ≟ nf₂
    _          ≟ _          = nothing
    -- We can also implement a procedure that potentially proves that two
    -- expressions have the same semantics.
    -- Note that this procedure must be /sound/, because it returns a
    -- proof. However, we have not proved that it is /complete/. Proving
    -- this, or finding a counterexample, is left as an exercise.
    prove : ∀ {n} (e₁ e₂ : Expr n) → Maybe (∀ ρ → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ)
    prove e₁ e₂ =
      (λ eq ρ →
         normalisation-theorem e₁ e₂ ρ (cong (λ nf → ⟦ nf ⟧′ ρ) eq))
      <$> normalise e₁ ≟ normalise e₂
    ex₃ = prove e₁ e₂
    -- We can also prove things "at compile time".
    ex₄ : (x ∙ identity) ∙ y ≡ identity ∙ (x ∙ (y ∙ identity))
    ex₄ = fromJust (prove e₁ e₂) ρ
    -- The following definition does not, and should not, type check.
    -- ex₅ : (x ∙ identity) ∙ y ≡ identity
    -- ex₅ = fromJust (prove e₁ id) ρ

## RWMonad
{: .types }
    {-# LANGUAGE GeneralizedNewtypeDeriving #-}
    {-# LANGUAGE FlexibleInstances #-}
    module RWMonad where
    import Data.Monoid
    import Test.QuickCheck
    instance Monoid w => Monad (RW e w) where
      return = returnRW
      (>>=)  = bindRW
    newtype RW e w a = RW {unRW :: e -> (a, w)} deriving (Arbitrary)
    returnRW :: Monoid w => a -> (RW e w) a
    bindRW   :: Monoid w => (RW e w) a -> (a -> (RW e w) b) -> 
                                                (RW e w) b
    askRW    :: Monoid w => (RW e w) e
    --localRW  :: (e -> e) -> (RW e w) a -> (RW e w) a
    tellRW   :: w -> (RW e w) ()
    listenRW :: (RW e w) a -> (RW e w) (a, w)
    askRW = RW (\e -> (e, mempty))
    localRW e2e (RW e2aw) = RW $ \ e -> e2aw (e2e e) -- :: (a, w)
      -- e2e :: e -> e
      -- e2aw :: e -> (a, w)
    returnRW a = RW $ \e-> (a, mempty)
    bindRW (RW e2aw) a2m = RW $ \e -> let (a, w1) = e2aw e
                                          (b, w2) = unRW (a2m a) e
                                      in (b, w1 `mappend` w2)
    -- askRW = RW $ \e -> (e, mempty)
    -- localRW f (RW e2aw) = RW $ \e -> e2aw (f e)
    tellRW w = RW $ \e -> ((), w)
    listenRW (RW e2aw) = RW $ \e -> let (a, w) = e2aw e
                                    in ((a, w), w)

## Monad laws: Proving
{: .spec }
    -- State and prove the three Monad laws
    lawReturnBind :: (Eq (m b), Monad m) => a -> (a -> m b) -> Bool
    lawReturnBind x f  =  (return x >>= f)  ==  f x
    lawBindReturn :: (Eq (m b), Monad m) => m b -> Bool
    lawBindReturn m    =  (m >>= return)    ==  m
    lawBindBind ::
      (Eq (m c), Monad m) => m a -> (a -> m b) -> (b -> m c) -> Bool
    lawBindBind m f g  = ((m >>= f) >>= g) ==  (m >>= (\x-> f x >>= g))

## RWMonad: Proofs
{: .spec }
    -- Straw-man proofs in Haskell (just a list of supposedly equal expr.)
    newtype AllEq a = AllEq [a] deriving (Arbitrary)
    proofReturnBind :: (Monoid w) => a -> (a -> RW e w b) -> AllEq (RW e w b)
    proofReturnBind x f = AllEq 
      [ (return x >>= f)
      , -- Monad instance for RW
        (returnRW x `bindRW` f)
      , {- def. returnRW -}
        ((RW $ \e->(x, mempty)) `bindRW` f)
      , {- def. bindRW -}
        let e2aw = \e->(x, mempty) 
            a2m = f
        in RW $ \e -> let (a, w1) = e2aw e
                          (b, w2) = unRW (a2m a) e
                      in (b, w1 `mappend` w2)
      , {- inlining -}
        RW $ \e -> let (a, w1) = (\e->(x, mempty)) e
                       (b, w2) = unRW (f a) e
                   in (b, w1 `mappend` w2)
      , {- beta-red.  -}
        RW $ \e -> let (a, w1) = (x, mempty)
                       (b, w2) = unRW (f a) e
                   in (b, w1 `mappend` w2)
      , {- inlining a, w1 -}
        RW $ \e -> let (b, w2) = unRW (f x) e
                   in (b, mempty `mappend` w2)
      , {- Monoid law -}
        RW $ \e -> let (b, w2) = unRW (f x) e
                   in (b, w2)
      , {- inlining -}
        RW $ \e -> unRW (f x) e
      , {- eta-reduction -}
        RW $ unRW (f x)
      , {- RW . unRW == id -}
        f x ]
    proofBindReturn m = AllEq
      [ m >>= return 
      , {- type instance -}
        m `bindRW` returnRW
      , {- def. of bindRW -}
        let e2aw = unRW m
            a2m  = returnRW
        in RW $ \e -> let (a, w1) = e2aw e
                          (b, w2) = unRW (a2m a) e
                      in (b, w1 `mappend` w2)
      , {- inlining -}
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = unRW (returnRW a) e
                   in (b, w1 `mappend` w2)
      , {- def. returnRW -}
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = unRW (RW $ \e->(a, mempty)) e
                   in (b, w1 `mappend` w2)
      , {- unRW . RW == id, beta-red. -}
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = (a, mempty)
                   in (b, w1 `mappend` w2)
      , {- inlining -}
        RW $ \e -> let (a, w1) = unRW m e
                   in (a, w1 `mappend` mempty)
      , {- Monoid law -}
        RW $ \e -> let (a, w1) = unRW m e
                   in (a, w1)
      , {- inlining -}
        RW $ \e -> unRW m e
      , {- eta-contraction, unRW . RW == id -}
        m ]
    proofBindBind m f g  = AllEq
      [ (m >>= f) >>= g
      , {- Monad instance-}  
        (m `bindRW` f) `bindRW` g
      , -- def. bindRW
        let e2aw = unRW (m `bindRW` f)
            a2m  = g
        in RW $ \e -> let (a, w1) = e2aw e
                          (b, w2) = unRW (a2m a) e
                      in (b, w1 `mappend` w2)
      , -- inlining
        RW $ \e -> let (a, w1) = unRW (m `bindRW` f) e
                       (b, w2) = unRW (g a) e
                   in (b, w1 `mappend` w2)
      , -- def. bindRW (again) + inline + prime, unRW . RW == id, beta
        RW $ \e -> let (a, w1) = let (a', w1') = unRW m e
                                     (b', w2') = unRW (f a') e
                                 in (b', w1' `mappend` w2')
                       (b, w2) = unRW (g a) e
                   in (b, w1 `mappend` w2)
      , -- let-float
        RW $ \e -> let (a', w1') = unRW m e     
                       (b', w2') = unRW (f a') e
                       (a, w1) = (b', w1' `mappend` w2')
                       (b, w2) = unRW (g a) e
                   in (b, w1 `mappend` w2)
      , -- substitute
        RW $ \e -> let (a', w1') = unRW m e     
                       (b', w2') = unRW (f a') e
                       (b, w2)   = unRW (g b') e
                   in (b, (w1' `mappend` w2') `mappend` w2)
      ,  -- rename + Monoid append associativity
        RW $ \e -> let (a, w1)   = unRW m e     
                       (b, w2)   = unRW (f a) e
                       (c, w3)   = unRW (g b) e
                   in (c, w1 `mappend` (w2 `mappend` w3))
        RW $ \e -> let (a, w1)   = unRW m e
                       (a', w1') = unRW (f a) e
                       (b', w2') = unRW (g a') e
                   in (b', w1 `mappend` (w1' `mappend` w2'))
      ,  -- substitute
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = let (a', w1') = unRW (f a) e
                                     (b', w2') = unRW (g a') e
                                 in (b', w1' `mappend` w2')
                   in (b, w1 `mappend` w2)
      ,  -- inline (+add primes), unRW . RW == id, beta red.
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = unRW (
                         let e2aw = unRW (f a)
                             a2m  = g
                         in RW $ \e -> let (a, w1) = e2aw e
                                           (b, w2) = unRW (a2m a) e
                                       in (b, w1 `mappend` w2)
                         ) e
                   in (b, w1 `mappend` w2)
      ,  -- def. of bindRW (again)
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = unRW (f a `bindRW` g) e
                   in (b, w1 `mappend` w2)
      ,  -- beta-red.
        RW $ \e -> let (a, w1) = unRW m e
                       (b, w2) = unRW ((\x-> f x `bindRW` g) a) e
                   in (b, w1 `mappend` w2)
      ,  -- inlining
        let e2aw = unRW m
            a2m  = (\x-> f x `bindRW` g)
        in RW $ \e -> let (a, w1) = e2aw e
                          (b, w2) = unRW (a2m a) e
                      in (b, w1 `mappend` w2)
      , -- def. bindRW
        (m `bindRW` (\x-> f x `bindRW` g))
      , {- Monad instance-}  
        (m >>= (\x-> f x >>= g)) ]
    mytest (AllEq ms) = forAll arbitrary $ \e -> 
                        allEq $ map (flip unRW e) ms
    allEq []      =  True
    allEq (x:xs)  =  all (x==) xs
    instance (Eq a, Eq w, Show b, Arbitrary b) => 
             Testable (AllEq (RW b w a)) where 
      property = mytest
    proofReturnBind' :: Bool -> Blind (Bool -> RW Int String Char) -> 
                        AllEq (RW Int String Char)
    proofReturnBind' x (Blind f) = proofReturnBind x f
    proofBindReturn' :: Blind (RW Int String Char) -> 
                        AllEq (RW Int String Char)
    proofBindReturn' (Blind m) = proofBindReturn m
    type RWIS = RW Int String
    proofBindBind' :: Blind (RWIS Bool) -> 
                      Blind (Bool -> RWIS Char) -> 
                      Blind (Char -> RWIS Int) -> 
                      AllEq (RWIS Int)
    proofBindBind' (Blind m) (Blind f) (Blind g) = proofBindBind m f g
      main = do 
      quickCheck proofBindBind'
      quickCheck proofBindReturn'
      quickCheck proofReturnBind'
    {- instance Eq a => Testable (AllEq a) where
      property = propertyAllEq 
    propertyAllEq :: Eq a => AllEq a -> Property
    propertyAllEq (AllEq xs) = QC.property $ QC.liftBool $ allEq xs -}
    {- instance (Arbitrary e, Show e, Testable prop) => 
             Testable (RW e w a) where
      property f = forAllShrink arbitrary shrink f -}

## MaybeT: Deep
{: .types }
    {-# LANGUAGE GADTs #-}
    module MaybeT.Deep where
    import qualified Control.Monad.Trans as CMT
    import qualified Control.Monad       as CM
    -- Maybe Monad Transformer
    instance Monad m => Monad (MaybeT m) where
      return = returnMT
      (>>=)  = bindMT
      fail   = failMT
    instance CMT.MonadTrans MaybeT where
      lift = liftMT
    returnMT :: Monad m => a ->  MaybeT m a
    bindMT   :: Monad m => MaybeT m a -> (a -> MaybeT m b) -> 
    failMT   :: Monad m => t -> MaybeT m a
    liftMT   :: Monad m => m a -> MaybeT m a
    runMaybeT:: Monad m => MaybeT m a -> m (Maybe a)
    data MaybeT m a where
      Return :: a -> MaybeT m a
      (:>>=) :: MaybeT m a -> (a -> MaybeT m b) -> MaybeT m b
      Fail   :: MaybeT m a
      Lift   :: m a -> MaybeT m a
    returnMT = Return
    bindMT   = (:>>=)
    failMT _ = Fail
    liftMT   = Lift
    runMaybeT (Return x) = return (Just x)
    runMaybeT (Lift m)   = CM.liftM Just m
    runMaybeT Fail       = return Nothing
    runMaybeT (m :>>= f) = do
      r <- runMaybeT m
      case r of
        Nothing -> return Nothing
        Just x  -> runMaybeT (f x)

## MaybeT: Shallow
{: .types }
    {-# LANGUAGE GADTs #-}
    module MaybeT.Shallow where
    import qualified Control.Monad.Trans as CMT
    import qualified Control.Monad       as CM
    -- Monad Transformers
    -- Shallow embedding (nicer)
    {- A general pattern for defining a monad transformer is
        newtype SomeT pars m a = SomeT
          { runSomeT :: args -> m (something wrapping a) }
    That is, a computation in the transformed monad is a computation
    in the underlying monad with a more interesting result type,
    possibly with some additional arguments.
       From the libraries:
         --        args        "something wrapping a"
         StateT:   s ->      m (a, s)
         ReaderT:  e ->      m a
         WriterT:            m (a, w)
         ErrorT:             m (Either e a)
       -- Reader, Writer and State all at once:
         RWST:     e -> s -> m (a, s, w) -}
    -- For our case: no args and "Maybe" wrapping a
    newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }
    instance Monad m => Monad (MaybeT m) where
      return = returnMT
      (>>=)  = bindMT
      fail   = failMT
    returnMT :: Monad m => a ->  MaybeT m  a
    returnMT x = MaybeT $ return (Just x)
    bindMT :: Monad m => MaybeT m a -> (a -> MaybeT m b) -> MaybeT m b
    bindMT m f = MaybeT $ do -- in the Monad m
      r <- runMaybeT m
      case r of
        Nothing -> return Nothing
        Just x  -> runMaybeT (f x)
    failMT :: Monad m => t -> MaybeT m a
    failMT _ = MaybeT (return Nothing)
    instance CMT.MonadTrans MaybeT where
      lift = liftMT
    liftMT :: Monad m => m a -> MaybeT m a
    liftMT m = MaybeT (CM.liftM Just m)

## FFI
    {-# LANGUAGE ForeignFunctionInterface #-}
    import Control.Applicative
    import Foreign (Storable(..), Ptr, alloca)
    import Foreign.C (CInt(..), CString, withCString, peekCString)
    import System.IO.Unsafe(unsafePerformIO)
    import Text.Printf (printf)
    -- For simple types like integers and strings, the Foreign.C
    -- library contains the C versions of the types and functions
    -- for converting back and forth.
    -- We can import foreign functions as pure functions, but we are
    -- responsible for making sure that they don't have unpleasant
    -- side effects.
    foreign import ccall "inc" c_inc :: CInt -> CInt
    inc :: Int -> Int
    inc n = fromIntegral $ c_inc (fromIntegral n)
    -- If a function isn't pure, we import it with IO type.
    foreign import ccall "encrypt" c_encrypt :: CString -> IO ()
    -- Since the side effects are local (creating a string and doing
    -- things to it) we can safely pretend that our wrapper is side
    -- effect free.
    encrypt :: String -> String
    encrypt s = unsafePerformIO $ withCString s $ \cs -> do
      c_encrypt cs
      peekCString cs
    -- For more complex foreign types we give an instance of the
    -- Storable class to explain how to read and write them from
    -- memory. In this example the type on the C side is
    --   struct { int x, y; }
    -- First declare the corresponding Haskell type.
    data Point = Pt Int Int
      deriving Show
    -- Import functions to read and write the components.
    foreign import ccall "init_pt"   c_init_pt :: Ptr Point -> 
    foreign import ccall "get_x"     c_get_x   :: Ptr Point -> IO CInt
    foreign import ccall "get_y"     c_get_y   :: Ptr Point -> IO CInt
    foreign import ccall "sqdist"    c_sqdist  :: Ptr Point -> CInt
    foreign import ccall "sizeof_pt" c_sizeof_pt :: CInt  
     -- still needs to be a function on the C side
    -- Give the storable instance. For portability we should use
    -- foreign functions to manipulate the structure.
    instance Storable Point where
      sizeOf _    = fromIntegral c_sizeof_pt
      alignment _ = 4
      peek p = do
        x <- c_get_x p
        y <- c_get_y p
        return $ Pt (fromIntegral x) (fromIntegral y)
      poke p (Pt x y) = c_init_pt p (fromIntegral x) (fromIntegral y)
    createPt :: Int -> Int -> Point
    createPt x y = unsafePerformIO $ alloca $ \p -> do
      c_init_pt p (fromIntegral x) (fromIntegral y)
      peek p
    sqDist :: Point -> Int
    sqDist pt = unsafePerformIO $ alloca $ \p -> do
      poke p pt
      return $ fromIntegral $ c_sqdist p
    test1 :: Int
    test1 = inc 1737
    test2 :: (String, String)
    test2 = (encrypted, encrypt encrypted)
      where encrypted = encrypt "Patrik"
    test3 :: Int
    test3 = sqDist (Pt 3 4)
    main :: IO ()
    main = do print test1
              uncurry (printf "(%s,%s)\n") test2
              print test3

## Continuation Monad
{: .types }
    {-# LANGUAGE GeneralizedNewtypeDeriving #-}
    -- RankNTypes, 
    import Control.Monad
    import Control.Monad.Trans
    -- A computation in the continuation monad gets its continuation
    -- (what to do after it's done) as an argument.
    newtype Cont r a = Cont { unCont :: (a -> r) -> r }
                       --   continuation ^^^^^^
    instance Monad (Cont r) where
      return x  =  Cont $ \k -> k x
      m >>= f   =  Cont $ \k -> unCont m $ \x -> unCont (f x) k
    -- running is to continue by doing nothing (id)
    runCont :: Cont a a -> a
    runCont m = unCont m id
    class Monad m => MonadCont m where
      -- callCC gives a computation access to its continuation. This
      -- continuation can be used to abort the computation (see
      -- example below).
      callCC :: ((a -> m b) -> m a) -> m a
    instance MonadCont (Cont r) where
      -- callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
      callCC f = Cont $ \k -> unCont (f (liftK k)) k
        where
          -- Lift the internal continuation to a computation.
          liftK :: (a -> r) -> a -> Cont r b
          liftK k x = Cont $ \_ -> k x
    -- Example
    example :: MonadCont m => Int -> m Int
    example n = do
      x <- callCC $ \k -> do
             when (even n) (k 0) -- if n is even jump straight out of
                                 -- callCC with x = 0
             return (n + 1)
      return x
    -- The transformer version
    -- Note that m doesn't have to be a monad for ContT r m to be a
    -- monad.
    newtype ContT r m a = ContT { unContT :: Cont (m r) a }
      deriving (Monad, MonadCont)
    runContT :: Monad m => ContT a m a -> m a
    runContT m = unCont (unContT m) return
    instance MonadTrans (ContT r) where
      lift m = ContT $ Cont $ \k -> m >>= k
    instance MonadIO m => MonadIO (ContT r m) where
      liftIO = lift . liftIO


## Memoization
{: .types }
    import Data.Map (Map)
    import qualified Data.Map as Map
    import Data.List  (unfoldr)
    import Data.Maybe (fromJust)
    import System.IO.Unsafe (unsafePerformIO)
    import Data.IORef (newIORef, readIORef, writeIORef)
    -- First the non-recursive core of the fibonacci function
    fibcore :: (Eq t, Num t, Num a) => (t -> a) -> t -> a
    fibcore cont = \n -> case n of
      0 -> 0
      1 -> 1
      n -> cont (n - 1) + cont (n - 2)
    -- then a pure "memoizer":
    memoPure :: (Enum a, Num a) => (a -> b) -> Int -> b
    memoPure f = let fs = map f [0..]
                 in (fs!!)
    fibPure :: Int -> Integer
    fibPure = memoPure $ fibcore fibPure
    -- A completely different "hand-optimized" fib based on 
    --   unfoldr :: (b -> Maybe (a, b)) -> b -> [a] 	
    -- defined in Data.List
    fibUnfoldr :: (Num t) => Int -> t
    fibUnfoldr = 
      let fiblist = unfoldr (\(f1,f2) -> Just (f1,(f2,f1+f2))) (0,1)
      in (fiblist !!)
    -- Start of impure part
    -- memo keeps a local cache of all the previous calls
    memo :: Ord a => (a -> b) -> a -> b
    memo f = unsafePerformIO $ do
      history <- newIORef Map.empty
      return (f' history)
      where
        f' history x = unsafePerformIO $ do
          tbl <- readIORef history
          case Map.lookup x tbl of
            Just y  -> return y
            Nothing -> do
              let y = f x
              writeIORef history (Map.insert x y tbl)
              return y
    -- By memoizing the naive implementation of the Fibonacci
    -- numbers we get an efficient version.
    fib :: Int -> Integer
    fib = memo $ fibcore fib
    -- You need to be a little careful with sharing to make sure
    -- that you get a single memo structure and not one for each
    -- call. For instance, the following doesn't work, since memo
    -- won't be applied until there is an argument to badfib.
    badfib n = memo (fibcore badfib) n
    badfib' n = memoPure (fibcore badfib') n

## Generics: Free expression variables
{: .types }
    {-# LANGUAGE DeriveDataTypeable #-}
    import Data.Generics
    import Data.Set (Set)
    import qualified Data.Set as Set
    data Expr = Var Name | App Expr Expr | Lam Name Expr
      deriving (Show, Data, Typeable)
    type Name = String
    -- All the boring cases (just one in this example) can be taken
    -- care of at once. But gmapQr etc. are complicated and often
    -- inefficient.  See NoGenerics for a nicer way to do it.
    freeVars :: Expr -> Set Name
    freeVars (Var x)   = Set.singleton x
    freeVars (Lam x e) = Set.delete x $ freeVars e
    freeVars e         = gmapQr Set.union Set.empty 
                                (mkQ Set.empty freeVars) e
    -- Examples
    e1, e2, e3 :: Expr
    e1 = Lam "x" $ Var "x"
    e2 = Lam "unused" $ Var "C"
    e3 = Lam "x" $ Lam "y" $ Lam "z" $ 
         App (Var "x") (Var "z") `App` 
         App (Var "y") (Var "z")

## No Generics: Free expression variables
{: .types }
    {-# LANGUAGE TypeSynonymInstances, OverlappingInstances, FlexibleContexts #-}
    import Control.Applicative  (Applicative, pure, (<*>), (<$>))
    import qualified Control.Monad.Reader 
                  as CMR        (MonadReader, runReader, ask, local)
    import Data.Traversable     (Traversable, traverse)
    import Data.Foldable        (Foldable, foldMap)
    import Data.Monoid          (mempty, mappend)
    import Data.Set (Set)
    import qualified Data.Set as Set
    import Data.Map (Map)
    import qualified Data.Map as Map
    import Text.Printf (printf)
    -- We split our datatype into the top-level structure (Expr')
    -- and the recursive knot-tying (Expr)
    type Name = String
    data Expr' e = Var Name | App e e | Lam Name e
    newtype Expr = Expr { unExpr :: Expr' Expr }
    -- Expr' has all kinds of nice properties it is in 
    --   Functor, Foldable, Traversable
    -- For freeVars we only need Foldable (and Monoid (Set a)).
    -- foldMap :: (Foldable t, Monoid m) => 
    --            (a -> m) -> t a -> m
    instance Foldable Expr' where
      foldMap f (Var _)     = mempty
      foldMap f (App e1 e2) = f e1  `mappend`  f e2
      foldMap f (Lam _ e)   = f e
    -- Once we get the instances out of the way we can define
    -- @freeVars@ quite elegantly.
    freeVars :: Expr -> Set Name
    freeVars (Expr e) = case e of
      Var x   -> Set.singleton x
      Lam x e -> Set.delete x (freeVars e)
      _       -> foldMap freeVars e
    -- Another more interesting example: alphaRename
    instance Functor Expr' where
      fmap f (Var x)     = Var x
      fmap f (App e1 e2) = App   (f e1) (f e2)
      fmap f (Lam x e)   = Lam x (f e)
    -- traverse :: (Traversable t, Applicative f) => 
    --             (a -> f b) -> t a -> f (t b)
    instance Traversable Expr' where
      traverse f (Var x)     = pure (Var x)
      traverse f (App e1 e2) = App    <$>  f e1  <*>  f e2
      traverse f (Lam x e)   = Lam x  <$>  f e
    type Supply = [Name]
    names :: Supply
    names = [ s ++ [c] | s <- "":names, c <- ['a'..'z'] ]
    type Renaming = Map Name Name
    type Env = (Supply, Renaming)
    alphaRename :: Expr -> Expr
    alphaRename e = CMR.runReader (alpha e) (names, Map.empty)
    -- alpha :: CMR.MonadReader Env m => Expr -> m Expr    
    alpha :: (CMR.MonadReader Env m, Applicative m) =>
             Expr -> m Expr
    alpha (Expr e) = Expr <$> case e of
      Var x   -> Var <$> rename x
      Lam x e -> fresh x $ \y -> Lam y <$> alpha e
      _       -> traverse alpha e
    rename :: (CMR.MonadReader (s, Map n n) m, Ord n) => n -> m n
    rename x = do
      (_supply, ren) <- CMR.ask
      return $ maybe x id $ Map.lookup x ren
    fresh :: (CMR.MonadReader ([t], Map k t) m, Ord k) => 
             k -> (t -> m b) -> m b
    fresh x f = do
      (y:names, ren) <- CMR.ask
      f y   `inEnv`  (names, Map.insert x y ren) 
    inEnv :: CMR.MonadReader b m => m a -> b -> m a
    mx `inEnv` env = CMR.local (const env) mx
    {-
    -- This was earlier missing from the Haskell libraries. Not
    -- needed with ghc 6.12 or later
    instance Applicative (Reader e) where
      pure  = return
      (<*>) = ap
    -}
    -- Examples
    lam :: Name -> Expr -> Expr
    lam x e   = Expr (Lam x e)
    app :: Expr -> Expr -> Expr
    app e1 e2 = Expr (App e1 e2)
    var :: Name -> Expr
    var x     = Expr (Var x)
    e1, e2, e3 :: Expr
    e1 = lam "x" $ var "x"
    e2 = lam "unused" $ var "C"
    e3 = lam "x" $ lam "y" $ lam "z" $ 
         app (var "x") (var "z") `app` 
         app (var "y") (var "z")
    instance Show Expr where
      showsPrec p (Expr e) = showsPrec p e
    instance Show e => Show (Expr' e) where
      showsPrec p (Var x) = showString x
      showsPrec p (App e1 e2) = showParen (p>1) $
        showsPrec 1 e1 . showString " " . showsPrec 2 e2
      showsPrec p (Lam x e) = showParen (p>0) $
        showString ("\\" ++ x ++ "-> ") . shows e
    test :: Expr -> IO ()
    test e = do printf "e=%s; free(e)=%s; Î±(e)=%s\n" 
                  (show e) 
                  (show $ Set.toList $ freeVars e) 
                  (show $ alphaRename e)
    main :: IO ()
    main = do test e1
              test e2
              test e3

## Maybe Monad
{: .types }
    data  Maybe a  =  Nothing | Just a
      deriving (Eq, Ord)
    instance  Functor Maybe  where
        fmap _ Nothing       = Nothing
        fmap f (Just a)      = Just (f a)
    instance  Monad Maybe  where
        (Just x) >>= k      = k x
        Nothing  >>= _      = Nothing
        (Just _) >>  k      = k
        Nothing  >>  _      = Nothing
        return              = Just
        fail _              = Nothing
    -- Functions over Maybe
    maybe :: b -> (a -> b) -> Maybe a -> b
    maybe n _ Nothing  = n
    maybe _ f (Just x) = f x
    catMaybes ls = [x | Just x <- ls]
    mapMaybe          :: (a -> Maybe b) -> [a] -> [b]
    mapMaybe _ []     = []
    mapMaybe f (x:xs) =
     let rs = mapMaybe f xs in
     case f x of
      Nothing -> rs
      Just r  -> r:rs

## Reader Monad
{: .types }
    instance MonadReader r ((->) r) where
        ask       = id
        local f m = m . f
    {- | The parameterizable reader monad.
    The @return@ function creates a @Reader@ that ignores the environment,
    and produces the given value.
    The binding operator @>>=@ produces a @Reader@ that uses the environment
    to extract the value its left-hand side,
    and then applies the bound function to that value in the same environment. -}
    newtype Reader r a = Reader {
        {- | Runs @Reader@ and extracts the final value from it.
        To extract the value apply @(runReader reader)@ to an environment value.  
        Parameters:
        * A @Reader@ to run.
        * An initial environment.  -}
        runReader :: r -> a }
    mapReader :: (a -> b) -> Reader r a -> Reader r b
    mapReader f m = Reader $ f . runReader m
    -- | A more general version of 'local'.
    withReader :: (r' -> r) -> Reader r a -> Reader r' a
    withReader f m = Reader $ runReader m . f
    instance Functor (Reader r) where
        fmap f m = Reader $ \r -> f (runReader m r)
    instance Monad (Reader r) where
        return a = Reader $ \_ -> a
        m >>= k  = Reader $ \r -> runReader (k (runReader m r)) r
    instance MonadFix (Reader r) where
        mfix f = Reader $ \r -> let a = runReader (f a) r in a
    instance MonadReader r (Reader r) where
        ask       = Reader id
        local f m = Reader $ runReader m . f
    {- | The reader monad transformer.
    Can be used to add environment reading functionality to other monads. -}
    newtype ReaderT r m a = ReaderT { runReaderT :: r -> m a }
    mapReaderT :: (m a -> n b) -> ReaderT w m a -> ReaderT w n b
    mapReaderT f m = ReaderT $ f . runReaderT m
    withReaderT :: (r' -> r) -> ReaderT r m a -> ReaderT r' m a
    withReaderT f m = ReaderT $ runReaderT m . f
    instance (Monad m) => Functor (ReaderT r m) where
        fmap f m = ReaderT $ \r -> do
            a <- runReaderT m r
            return (f a)
    instance (Monad m) => Monad (ReaderT r m) where
        return a = ReaderT $ \_ -> return a
        m >>= k  = ReaderT $ \r -> do
            a <- runReaderT m r
            runReaderT (k a) r
        fail msg = ReaderT $ \_ -> fail msg
    instance (MonadPlus m) => MonadPlus (ReaderT r m) where
        mzero       = ReaderT $ \_ -> mzero
        m `mplus` n = ReaderT $ \r -> runReaderT m r `mplus` runReaderT n r
    instance (MonadFix m) => MonadFix (ReaderT r m) where
        mfix f = ReaderT $ \r -> mfix $ \a -> runReaderT (f a) r
    instance (Monad m) => MonadReader r (ReaderT r m) where
        ask       = ReaderT return
        local f m = ReaderT $ \r -> runReaderT m (f r)
    -- Instances for other mtl transformers
    instance MonadTrans (ReaderT r) where
        lift m = ReaderT $ \_ -> m
    instance (MonadIO m) => MonadIO (ReaderT r m) where
        liftIO = lift . liftIO
    instance (MonadCont m) => MonadCont (ReaderT r m) where
        callCC f = ReaderT $ \r ->
            callCC $ \c ->
            runReaderT (f (\a -> ReaderT $ \_ -> c a)) r
    instance (MonadError e m) => MonadError e (ReaderT r m) where
        throwError       = lift . throwError
        m `catchError` h = ReaderT $ \r -> runReaderT m r
            `catchError` \e -> runReaderT (h e) r
    -- Needs -fallow-undecidable-instances
    instance (MonadState s m) => MonadState s (ReaderT r m) where
        get = lift get
        put = lift . put
    -- This instance needs -fallow-undecidable-instances, because
    -- it does not satisfy the coverage condition
    instance (MonadWriter w m) => MonadWriter w (ReaderT r m) where
        tell     = lift . tell
        listen m = ReaderT $ \w -> listen (runReaderT m w)
        pass   m = ReaderT $ \w -> pass   (runReaderT m w)

## Writer Monad
{: .types }
    type Writer w = WriterT w Identity
    -- | Construct a writer computation from a (result, output) pair.
    -- (The inverse of 'runWriter'.)
    writer :: (a, w) -> Writer w a
    writer = WriterT . Identity
    -- | Unwrap a writer computation as a (result, output) pair.
    -- (The inverse of 'writer'.)
    runWriter :: Writer w a -> (a, w)
    runWriter = runIdentity . runWriterT
    -- | Extract the output from a writer computation.
    -- * @'execWriter' m = 'snd' ('runWriter' m)@
    execWriter :: Writer w a -> w
    execWriter m = snd (runWriter m)
    -- | Map both the return value and output of a computation using
    -- the given function.
    -- * @'runWriter' ('mapWriter' f m) = f ('runWriter' m@)
    mapWriter :: ((a, w) -> (b, w')) -> Writer w a -> Writer w' b
    mapWriter f = mapWriterT (Identity . f . runIdentity)
    -- | A writer monad parameterized by:
    --   * @w@ - the output to accumulate.
    --   * @m@ - The inner monad.
    -- The 'return' function produces the output 'mempty', while @>>=@
    -- combines the outputs of the subcomputations using 'mappend'.
    newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }
    -- | Extract the output from a writer computation.
    -- * @'execWriterT' m = 'liftM' 'snd' ('runWriterT' m)@
    execWriterT :: Monad m => WriterT w m a -> m w
    execWriterT m = do
        ~(_, w) <- runWriterT m
        return w
    -- | Map both the return value and output of a computation using
    -- the given function.
    -- * @'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m@)
    mapWriterT :: (m (a, w) -> n (b, w')) -> WriterT w m a -> WriterT w' n b
    mapWriterT f m = WriterT $ f (runWriterT m)
    instance (Functor m) => Functor (WriterT w m) where
        fmap f = mapWriterT $ fmap $ \ ~(a, w) -> (f a, w)
    instance (Monoid w, Applicative m) => Applicative (WriterT w m) where
        pure a  = WriterT $ pure (a, mempty)
        f <*> v = WriterT $ liftA2 k (runWriterT f) (runWriterT v)
          where k ~(a, w) ~(b, w') = (a b, w `mappend` w')
    instance (Monoid w, Alternative m) => Alternative (WriterT w m) where
        empty   = WriterT empty
        m <|> n = WriterT $ runWriterT m <|> runWriterT n
    instance (Monoid w, Monad m) => Monad (WriterT w m) where
        return a = WriterT $ return (a, mempty)
        m >>= k  = WriterT $ do
            ~(a, w)  <- runWriterT m
            ~(b, w') <- runWriterT (k a)
            return (b, w `mappend` w')
        fail msg = WriterT $ fail msg
    instance (Monoid w, MonadPlus m) => MonadPlus (WriterT w m) where
        mzero       = WriterT mzero
        m `mplus` n = WriterT $ runWriterT m `mplus` runWriterT n
    instance (Monoid w, MonadFix m) => MonadFix (WriterT w m) where
        mfix m = WriterT $ mfix $ \ ~(a, _) -> runWriterT (m a)
    instance (Monoid w) => MonadTrans (WriterT w) where
        lift m = WriterT $ do
            a <- m
            return (a, mempty)
    instance (Monoid w, MonadIO m) => MonadIO (WriterT w m) where
        liftIO = lift . liftIO
    -- | @'tell' w@ is an action that produces the output @w@.
    tell :: (Monoid w, Monad m) => w -> WriterT w m ()
    tell w = WriterT $ return ((), w)
    -- | @'listen' m@ is an action that executes the action @m@ and adds its
    -- output to the value of the computation.
    -- * @'runWriterT' ('listen' m) = 'liftM' (\\(a, w) -> ((a, w), w)) ('runWriterT' m)@
    listen :: (Monoid w, Monad m) => WriterT w m a -> WriterT w m (a, w)
    listen m = WriterT $ do
        ~(a, w) <- runWriterT m
        return ((a, w), w)
    -- | @'listens' f m@ is an action that executes the action @m@ and adds
    -- the result of applying @f@ to the output to the value of the computation.
    -- * @'listens' f m = 'liftM' (id *** f) ('listen' m)@
    -- * @'runWriterT' ('listens' f m) = 'liftM' (\\(a, w) -> ((a, f w), w)) ('runWriterT' m)@
    listens :: (Monoid w, Monad m) => (w -> b) -> WriterT w m a -> WriterT w m (a, b)
    listens f m = do
        ~(a, w) <- listen m
        return (a, f w)
    -- | @'pass' m@ is an action that executes the action @m@, which returns
    -- a value and a function, and returns the value, applying the function
    -- to the output.
    -- * @'runWriterT' ('pass' m) = 'liftM' (\\((a, f), w) -> (a, f w)) ('runWriterT' m)@
    pass :: (Monoid w, Monad m) => WriterT w m (a, w -> w) -> WriterT w m a
    pass m = WriterT $ do
        ~((a, f), w) <- runWriterT m
        return (a, f w)
    -- | @'censor' f m@ is an action that executes the action @m@ and
    -- applies the function @f@ to its output, leaving the return value
    -- unchanged.
    -- * @'censor' f m = 'pass' ('liftM' (\\x -> (x,f)) m)@
    -- * @'runWriterT' ('censor' f m) = 'liftM' (\\(a, w) -> (a, f w)) ('runWriterT' m)@
    censor :: (Monoid w, Monad m) => (w -> w) -> WriterT w m a -> WriterT w m a
    censor f m = pass $ do
        a <- m
        return (a, f)
    -- | Lift a @callCC@ operation to the new monad.
    liftCallCC :: (Monoid w) => ((((a,w) -> m (b,w)) -> m (a,w)) -> m (a,w)) ->
        ((a -> WriterT w m b) -> WriterT w m a) -> WriterT w m a
    liftCallCC callCC f = WriterT $
        callCC $ \c ->
        runWriterT (f (\a -> WriterT $ c (a, mempty)))
    -- | Lift a @catchError@ operation to the new monad.
    liftCatch :: (m (a,w) -> (e -> m (a,w)) -> m (a,w)) ->
        WriterT w m a -> (e -> WriterT w m a) -> WriterT w m a
    liftCatch catchError m h =
        WriterT $ runWriterT m `catchError` \e -> runWriterT (h e)

## State Monad
{: .types }
    -- | A parameterizable state monad where /s/ is the type of the state
    -- to carry and /a/ is the type of the /return value/.
    newtype State s a = State { runState :: s -> (a, s) }
    -- |Evaluate this state monad with the given initial state,throwing
    -- away the final state.  Very much like @fst@ composed with
    -- @runstate@.
    evalState :: State s a -- ^The state to evaluate
              -> s         -- ^An initial value
              -> a         -- ^The return value of the state application
    evalState m s = fst (runState m s)
    -- |Execute this state and return the new state, throwing away the
    -- return value.  Very much like @snd@ composed with
    -- @runstate@.
    execState :: State s a -- ^The state to evaluate
              -> s         -- ^An initial value
              -> s         -- ^The new state
    execState m s = snd (runState m s)
    -- |Map a stateful computation from one (return value, state) pair to
    -- another.  For instance, to convert numberTree from a function that
    -- returns a tree to a function that returns the sum of the numbered
    -- tree (see the Examples section for numberTree and sumTree) you may
    -- write:
    -- > sumNumberedTree :: (Eq a) => Tree a -> State (Table a) Int
    -- > sumNumberedTree = mapState (\ (t, tab) -> (sumTree t, tab))  . numberTree
    mapState :: ((a, s) -> (b, s)) -> State s a -> State s b
    mapState f m = State $ f . runState m
    -- |Apply this function to this state and return the resulting state.
    withState :: (s -> s) -> State s a -> State s a
    withState f m = State $ runState m . f
    instance Functor (State s) where
        fmap f m = State $ \s -> let
            (a, s') = runState m s
            in (f a, s')
    instance Monad (State s) where
        return a = State $ \s -> (a, s)
        m >>= k  = State $ \s -> let
            (a, s') = runState m s
            in runState (k a) s'
    instance MonadFix (State s) where
        mfix f = State $ \s -> let (a, s') = runState (f a) s in (a, s')
    instance MonadState s (State s) where
        get   = State $ \s -> (s, s)
        put s = State $ \_ -> ((), s)
    -- | A parameterizable state monad for encapsulating an inner
    -- monad.
    -- The StateT Monad structure is parameterized over two things:
    --   * s - The state.
    --   * m - The inner monad.
    -- Here are some examples of use:
    -- (Parser from ParseLib with Hugs)
    -- >  type Parser a = StateT String [] a
    -- >     ==> StateT (String -> [(a,String)])
    -- For example, item can be written as:
    -- >   item = do (x:xs) <- get
    -- >          put xs
    -- >          return x
    -- >   type BoringState s a = StateT s Indentity a
    -- >        ==> StateT (s -> Identity (a,s))
    -- >   type StateWithIO s a = StateT s IO a
    -- >        ==> StateT (s -> IO (a,s))
    -- >   type StateWithErr s a = StateT s Maybe a
    -- >        ==> StateT (s -> Maybe (a,s))
    newtype StateT s m a = StateT { runStateT :: s -> m (a,s) }
    -- |Similar to 'evalState'
    evalStateT :: (Monad m) => StateT s m a -> s -> m a
    evalStateT m s = do
        ~(a, _) <- runStateT m s
        return a
    -- |Similar to 'execState'
    execStateT :: (Monad m) => StateT s m a -> s -> m s
    execStateT m s = do
        ~(_, s') <- runStateT m s
        return s'
    -- |Similar to 'mapState'
    mapStateT :: (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
    mapStateT f m = StateT $ f . runStateT m
    -- |Similar to 'withState'
    withStateT :: (s -> s) -> StateT s m a -> StateT s m a
    withStateT f m = StateT $ runStateT m . f
    instance (Monad m) => Functor (StateT s m) where
        fmap f m = StateT $ \s -> do
            ~(x, s') <- runStateT m s
            return (f x, s')
    instance (Monad m) => Monad (StateT s m) where
        return a = StateT $ \s -> return (a, s)
        m >>= k  = StateT $ \s -> do
            ~(a, s') <- runStateT m s
            runStateT (k a) s'
        fail str = StateT $ \_ -> fail str
    instance (MonadPlus m) => MonadPlus (StateT s m) where
        mzero       = StateT $ \_ -> mzero
        m `mplus` n = StateT $ \s -> runStateT m s `mplus` runStateT n s
    instance (MonadFix m) => MonadFix (StateT s m) where
        mfix f = StateT $ \s -> mfix $ \ ~(a, _) -> runStateT (f a) s
    instance (Monad m) => MonadState s (StateT s m) where
        get   = StateT $ \s -> return (s, s)
        put s = StateT $ \_ -> return ((), s)
    -- Instances for other mtl transformers
    instance MonadTrans (StateT s) where
        lift m = StateT $ \s -> do
            a <- m
            return (a, s)
    instance (MonadIO m) => MonadIO (StateT s m) where
        liftIO = lift . liftIO
    instance (MonadCont m) => MonadCont (StateT s m) where
        callCC f = StateT $ \s ->
            callCC $ \c ->
            runStateT (f (\a -> StateT $ \s' -> c (a, s'))) s
    instance (MonadError e m) => MonadError e (StateT s m) where
        throwError       = lift . throwError
        m `catchError` h = StateT $ \s -> runStateT m s
            `catchError` \e -> runStateT (h e) s
    -- Needs -fallow-undecidable-instances
    instance (MonadReader r m) => MonadReader r (StateT s m) where
        ask       = lift ask
        local f m = StateT $ \s -> local f (runStateT m s)
    -- Needs -fallow-undecidable-instances
    instance (MonadWriter w m) => MonadWriter w (StateT s m) where
        tell     = lift . tell
        listen m = StateT $ \s -> do
            ~((a, s'), w) <- listen (runStateT m s)
            return ((a, w), s')
        pass   m = StateT $ \s -> pass $ do
            ~((a, f), s') <- runStateT m s
            return ((a, s'), f)

## Cont Monad
{: .types }
    {- | Runs a CPS computation, returns its result after applying
    the final continuation to it.
    Parameters:
    * a continuation computation (@Cont@).
    * the final continuation, which produces the final result (often @id@).
    -}
    newtype Cont r a = Cont { runCont :: (a -> r) -> r }
    mapCont :: (r -> r) -> Cont r a -> Cont r a
    mapCont f m = Cont $ f . runCont m
    withCont :: ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
    withCont f m = Cont $ runCont m . f
    instance Functor (Cont r) where
        fmap f m = Cont $ \c -> runCont m (c . f)
    instance Monad (Cont r) where
        return a = Cont ($ a)
        m >>= k  = Cont $ \c -> runCont m $ \a -> runCont (k a) c
    instance MonadCont (Cont r) where
        callCC f = Cont $ \c -> runCont (f (\a -> Cont $ \_ -> c a)) c
    {- | The continuation monad transformer.
    Can be used to add continuation handling to other monads.  -}
    newtype ContT r m a = ContT { runContT :: (a -> m r) -> m r }
    mapContT :: (m r -> m r) -> ContT r m a -> ContT r m a
    mapContT f m = ContT $ f . runContT m
    withContT :: ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
    withContT f m = ContT $ runContT m . f
    instance (Monad m) => Functor (ContT r m) where
        fmap f m = ContT $ \c -> runContT m (c . f)
    instance (Monad m) => Monad (ContT r m) where
        return a = ContT ($ a)
        m >>= k  = ContT $ \c -> runContT m (\a -> runContT (k a) c)
    instance (Monad m) => MonadCont (ContT r m) where
        callCC f = ContT $ \c -> runContT (f (\a -> ContT $ \_ -> c a)) c
    -- Instances for other mtl transformers
    instance MonadTrans (ContT r) where
        lift m = ContT (m >>=)
    instance (MonadIO m) => MonadIO (ContT r m) where
        liftIO = lift . liftIO
    -- Needs -fallow-undecidable-instances
    instance (MonadReader r' m) => MonadReader r' (ContT r m) where
        ask       = lift ask
        local f m = ContT $ \c -> do
            r <- ask
            local f (runContT m (local (const r) . c))
    -- Needs -fallow-undecidable-instances
    instance (MonadState s m) => MonadState s (ContT r m) where
        get = lift get
        put = lift . put
