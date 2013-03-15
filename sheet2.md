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

## MaybeT: Writer instance
    instance (Monoid w, MonadWriter w m) => MonadWriter w (MaybeT m) where
      tell    =  tellMT
      listen  =  listenMT
    tellMT   :: MonadWriter w m => w -> MaybeT m ()
    tellMT w = MaybeT $ tellMT1 w
    tellMT1  :: MonadWriter w m => w -> m (Maybe ())
    tellMT1 w = tell w >> return (Just ())
    listenMT :: MonadWriter w m => MaybeT m a -> MaybeT m (a, w)
    listenMT (MaybeT mMa) = MaybeT $ listenMT1 mMa
    listenMT1 :: MonadWriter w m => m (Maybe a) -> m (Maybe (a, w))
    listenMT1 mma = do (ma, w) <- listen mma
                       return $ case ma of
                         Nothing -> Nothing
                         Just a  -> Just (a, w)

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

## Maybe Monad
{: .types }
    data  Maybe a  =  Nothing | Just a
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
    newtype Reader r a = Reader { runReader :: r -> a }
        {- | Runs @Reader@ and extracts the final value from it.
        To extract the value apply @(runReader reader)@ to an environment value.  
        Parameters: * A @Reader@ to run.  * An initial environment.  -}
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
    execWriter :: Writer w a -> w
    execWriter m = snd (runWriter m)
    -- | Map both the return value and output of a computation using
    -- the given function.
    mapWriter :: ((a, w) -> (b, w')) -> Writer w a -> Writer w' b
    mapWriter f = mapWriterT (Identity . f . runIdentity)
    newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }
    -- | Extract the output from a writer computation.
    execWriterT :: Monad m => WriterT w m a -> m w
    execWriterT m = do
        ~(_, w) <- runWriterT m
        return w
    -- | Map both the return value and output of a computation using
    -- the given function.
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
    tell :: (Monoid w, Monad m) => w -> WriterT w m ()
    tell w = WriterT $ return ((), w)
    -- output to the value of the computation.
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
    liftCallCC :: (Monoid w) => ((((a,w) -> m (b,w)) -> m (a,w)) -> m (a,w)) ->
        ((a -> WriterT w m b) -> WriterT w m a) -> WriterT w m a
    liftCallCC callCC f = WriterT $
        callCC $ \c ->
        runWriterT (f (\a -> WriterT $ c (a, mempty)))
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
    -- The StateT Monad structure is parameterized over two things:
    --   * s - The state.
    --   * m - The inner monad.
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

## Properties: Vector API
{: .spec }
    prop_law1 xs  = D.length (D.fromList xs) == P.length xs
    prop_law2 x   = D.head (D.fromList [x]) == x
    prop_law3 n   = Q.forAll (Q.choose (0,n-1)) $ \i ->
                    D.index (D.fromFun n id) i == i
    -- For most interesting laws an equality check is needed for vectors
    --  import Problem1.Deep_Instances
    prop_law4 v w = D.length (v  D.++  w) == D.length v   +   D.length w
    prop_law5 v = Q.forAll (Q.choose (0,n)) $ \i ->
                  D.take n v   D.++  D.drop n v   ==   v
      where n = D.length v

## Generator: Vector API
{: .spec }
    instance Q.Arbitrary a => Q.Arbitrary (D a) where
      arbitrary = Q.sized arbitraryD
    arbitraryD :: Q.Arbitrary a => Int -> Q.Gen (D a)
    arbitraryD n 
      | n <= 1 = Q.oneof [ CM.liftM single1 Q.arbitrary
                         , CM.liftM single2 Q.arbitrary ]
      | otherwise = do left <- Q.choose (1,n-1)
         CM.liftM2 (:++) (arbitraryD left) 
                         (arbitraryD (n-left))
    single1 :: a -> D a
    single1 a = FromList [a]
    single2 :: a -> D a
    single2 a = FromV (V.V 1 (P.const a))
    -- Not part of the exam question: run some tests
    q :: Q.Testable p => p -> IO ()
    q = Q.quickCheck
    main = do q (prop_law1 :: [()] -> Bool)
              q (prop_law2 :: Int -> Bool)
              q (prop_law3 :: Int -> Q.Property)
              q (prop_law4 :: Vector () -> Vector () -> Bool)
              q (prop_law5 :: Vector Int -> Q.Property)

## Product Monad
{: .types }
    newtype Prod m n a = Prod {unProd :: (m a, n a)}
    fstP :: Prod m n a -> m a
    fstP = fst . unProd
    sndP :: Prod m n a -> n a
    sndP = snd . unProd
    instance (Monad m, Monad n) => Monad (Prod m n) where
      return  =  returnProd
      (>>=)   =  bindProd
      fail    =  failProd
    returnProd :: (Monad m, Monad n) => a -> Prod m n a
    returnProd   x  =  Prod (return x, return x)
    bindProd :: (Monad m, Monad n) =>
      Prod m n a -> (a -> Prod m n b) -> Prod m n b
    bindProd mnx f  =  Prod ( fstP mnx >>= (fstP . f)
                            , sndP mnx >>= (sndP . f) )
    failProd :: (Monad m, Monad n) => String -> Prod m n a
    failProd s = Prod (fail s, fail s)

## Pair Monad: Proofs
{: .spec }
    proof_LeftId a f =
      [ return a >>= (\x -> f x)
      , -- def. of return
        Prod (return a, return a) >>= (\x -> f x)
      , -- def. of (>>=)
        Prod ( return a >>= (fstP . f)
             , return a >>= (sndP . f) )
      , -- LeftId law for m and for n
        Prod ( (fstP . f) a
             , (sndP . f) a )
      , -- def. of composition
        Prod ( fstP (f a)
             , sndP (f a) )
      , -- SurjectivePairing
        Prod ( unProd (f a) )
      , -- Inverses
        f a ]
    proof_RightId mx =
      [ mx >>= return
      , -- inverses
        Prod (unProd mx) >>= return
      , -- surjectivePairing
        Prod (fstP mx, sndP mx) >>= return
      , -- def. of (>>=), return
    {- -- commented out due to ambiguous type variables
        Prod ( fstP mx >>= (fstP . returnProd)
             , sndP mx >>= (sndP . returnProd) )
      , -- fstP_return and sndP_return -}
        Prod ( fstP mx >>= return
             , sndP mx >>= return )
      , -- RightId law for m and for n
        Prod ( fstP mx
             , sndP mx )
      , -- surjectivePairing
        Prod (unProd mx)
      , -- Inverses
        mx ]
    fstP_return x =
      [ (fstP . returnProd) x
      , -- def. of (.)
        fst (unProd (returnProd x))
      , -- def. of returnProd
        fst (unProd (Prod (return x, return x)))
      , -- Inverses
        fst (return x, return x)
      , -- def. of fst
        return x ]
    sndP_return x =
      [ (sndP . returnProd) x
      , -- as in fstP_return
        return x ]
    proof_Assoc mx f g  =
     [ (mx >>= f) >>= g
     , -- Inverses, surjectivePairing
       (Prod (fstP mx, sndP mx) >>= f) >>= g
     , -- Def. of (>>=)
       (Prod ( fstP mx >>= (fstP . f)
             , sndP mx >>= (sndP . f) ) ) >>= g
     , -- Def. of (>>=)
       Prod ( (fstP mx >>= (fstP . f)) >>= (fstP . g)
            , (sndP mx >>= (sndP . f)) >>= (sndP . g))
     , -- Assoc. law for the underlying monads m and n
       Prod ( fstP mx >>= \x -> (fstP . f) x >>= (fstP . g)
            , sndP mx >>= \y -> (sndP . f) y >>= (sndP . g) )
     , -- Def. of (.)
       Prod ( fstP mx >>= \x -> fstP (f x) >>= (fstP . g)
            , sndP mx >>= \y -> sndP (f y) >>= (sndP . g) )
     , -- fstP_distributes and sndP_distributes
       Prod ( fstP mx >>= \x -> fstP (f x >>= g)
            , sndP mx >>= \y -> sndP (f y >>= g) )
     , -- Def. of (.) + alpha renaming
       Prod ( fstP mx >>= (fstP . (\x -> f x >>= g))
            , sndP mx >>= (sndP . (\x -> f x >>= g)) )
     , -- def. of (>>=)
       Prod (fstP mx, sndP mx) >>= (\x -> f x >>= g)
     , -- def. of return
       Prod (fstP mx, sndP mx) >>= (\x -> f x >>= g)
     , -- expand mx
       mx >>= (\x -> f x >>= g) ]
    fstP_distributes f g x =
     [ fstP (f x) >>= (fstP . g)
     , -- Def. of fstP
       fst (unProd (f x)) >>= (fstP . g)
     , -- Def. of fst
       fst ( fst (unProd (f x)) >>= (fstP . g)
           , snd (unProd (f x)) >>= (sndP . g) )
     , -- Inverses
       fst (unProd (Prod ( fst (unProd (f x)) >>= (fstP . g)
                         , snd (unProd (f x)) >>= (sndP . g) )))
     , -- def. of (>>=), fstP
       fstP (Prod (fst (unProd (f x)), snd (unProd (f x))) >>= g)
     , -- expand (f x)
       fstP (f x >>= g) ]

## Pair Monad: False Properties
{: .spec }
    -- Surjective pairing does not hold, examples are p1 and p2
    p1, p2 :: (a, b)
    p1 = undefined
    p2 = (fst p1, snd p1)
    -- They can be distinguished using seq (or pattern matching)
    -- Eta-expansion does not hold, examples are f1 and f2
    f1, f2 :: a->b
    f1 = undefined
    f2 = \x -> f1 x
    -- They can be distinguished (only) using seq
    test1 x = CE.catch (x `seq` return False) $ return . constTrue
      where constTrue :: SomeException -> Bool
            constTrue _ = True
    test2 x y = do x_bot <- test1 x
                   y_bot <- test1 y
                   print (x_bot == y_bot)
    main = do putStr "Surjective pairing is "; test2 p1 p2
              putStr "Eta expansion is      "; test2 f1 f2

## Monad Stacking: Expanding
{: .types }
    {- newtype Eval1 a = Eval1{ unEval1 :: 
        CMS.StateT Store (CME.ErrorT Err CMI.Identity) a }
    ~= Store -> (CME.ErrorT Err CMI.Identity) (a, Store)
    ~= Store -> CMI.Identity (Either Err (a, Store))
    ~= Store -> Either Err (a, Store) -}
    {- newtype Eval2 a = Eval2{ unEval2 :: 
    CME.ErrorT Err (CMS.StateT Store CMI.Identity) a }
    ~= CME.ErrorT Err (CMS.StateT Store CMI.Identity) a
    ~= (CMS.StateT Store CMI.Identity) (Either Err a)
    ~= Store -> CMI.Identity (Either Err a, Store)
    ~= Store -> (Either Err a, Store) -}

## Monad Stacking: Unwinding run function
{: .types }
    type Env = String -- just a dummy - it could be anything
    newtype Eval3 a = Eval3{ unEval3 :: 
        CMR.ReaderT Env (CMS.StateT Store (CME.ErrorT Err
                            CMI.Identity)) a }
      deriving (Monad, CMS.MonadState Store, CME.MonadError Err,
                CMR.MonadReader Env)
    runEval3 :: Eval3 a -> Either Err a
    runEval3 = CMI.runIdentity
             . CME.runErrorT
             . startStateFrom  emptyStore
             . startEnvIn myEnv
             . unEval3
    startEnvIn :: Monad m => env -> CMR.ReaderT env m a -> m a
    startEnvIn = flip CMR.runReaderT
    -- Types: (done using where to check them)
    runEval3' :: Eval3 a -> Either Err a
    runEval3' (mx0 :: Eval3 a) = mx5
      where mx5 :: Either Err a
            mx5 = CMI.runIdentity mx4
            mx4 :: CMI.Identity (Either Err a)
            mx4 = CME.runErrorT mx3
            mx3 :: CME.ErrorT Err CMI.Identity a
            mx3 = startStateFrom  emptyStore mx2
            mx2 :: CMS.StateT Store (CME.ErrorT Err CMI.Identity) a
            mx2 = startEnvIn myEnv mx1
            mx1 :: CMR.ReaderT Env (CMS.StateT Store (CME.ErrorT Err CMI.Identity)) a
            mx1 = unEval3 mx0

## Calc
{: .edsl }
    type Calc = C Value
    data C a = CBin BOp (C a) (C a) | CUn  UOp (C a) | CNull NullOp | Num a
    data BOp    = Add | Sub | Mul | Div deriving (Eq, Show)
    data UOp    = Inv | Neg   | M | MP  deriving (Eq, Show)
    data NullOp = MR | MC               deriving (Eq, Show)
    -- eval :: Calc -> CalcM Value
    eval :: (CMS.MonadState v m, Fractional v) => C v -> m v
    eval (CBin op e1 e2) = do
      v1 <- eval e1
      v2 <- eval e2
      evalBOp op v1 v2
    eval (CUn op e) = do
      v <- eval e
      evalUOp op v
    eval (CNull op) = do
      evalNullOp op
    eval (Num n)    = return n
    --  return (fromInteger n) was used before the generalisation
    -- evalBOp :: BOp -> Value -> Value -> CalcM Value
    evalBOp :: (Fractional v, Monad m) => BOp -> (v->v->m v)
    evalBOp Div v1 0 = fail "DivZ"
    evalBOp op v1 v2 = return $ evalBOpPure op v1 v2
    -- evalBOpPure :: BOp -> Value -> Value -> Value
    evalBOpPure :: Fractional v => BOp -> (v->v->v)
    evalBOpPure Div = (/)
    evalBOpPure Mul = (*)
    evalBOpPure Add = (+)
    evalBOpPure Sub = (-)
    -- evalUOp :: UOp -> v -> CM v v
    evalUOp :: (Fractional v, CMS.MonadState v m) => UOp -> (v->m v)
    evalUOp Inv 0 = fail "InvZ"
    evalUOp M   v = do
      putMem v
    evalUOp MP  v = do
      m <- getMem
      putMem (v+m)
    evalUOp op  v = return $ evalUOpPure op v
    -- evalUOpPure :: UOp -> Value -> Value
    evalUOpPure :: Fractional v => UOp -> (v->v)
    evalUOpPure Inv = (1/)
    evalUOpPure Neg = negate
    -- evalNullOp :: NullOp -> CalcM Value
    evalNullOp :: (Num v, CMS.MonadState v m) => NullOp -> m v
    evalNullOp MR = getMem
    evalNullOp MC = putMem 0
    -- getMem :: CalcM Value
    getMem :: CMS.MonadState v m => m v
    getMem    = CMS.get
    -- putMem :: Value -> CalcM Value
    putMem :: CMS.MonadState v m => v -> m v
    putMem m = do
      CMS.put m
      return m

## Monad laws: Actually testing
{: .spec }
    -- Polymorphic:
    leftId :: (Monad m, Eq (m b)) => a -> (a->m b) -> Bool
    leftId a f   =  (return a >>= \x -> f x) == f a
    rightId :: (Monad m, Eq (m a)) => m a -> Bool
    rightId m    =  (m >>= \x-> return x) == m
    assoc :: (Monad m, Eq (m c)) => m a -> (a->m b) -> (b-> m c) -> Bool
    assoc m f g  =  ((m >>= f) >>= g)  ==   (m >>= (\x-> f x >>= g))
    -- For CalcM:
    leftIdCM ::  (Arbitrary a, Arbitrary (CalcM a), Eq (CalcM b)) => 
                 a -> (a->CalcM b) -> Bool
    leftIdCM  =  leftId
    rightIdCM :: (Arbitrary (CalcM a), Eq (CalcM a)) => CalcM a -> Bool
    rightIdCM  = rightId
    assocCM ::   (Arbitrary a, Arbitrary (CalcM a), Arbitrary (CalcM b), Eq (CalcM c)) =>
                 CalcM a -> (a->CalcM b) -> (b-> CalcM c) -> Bool
    assocCM  =  assoc
    {- You would also need to 
    * fix monomorphic types for a, b, c
    * define generators for CalcM a
    * define equality checks for CalcM a values
    Equality checking of arbitrary functions is undecidable. This can be
    solved by letting QuickCheck generate random start-states and test
    equality after running the CalcM monad. -}

## Functors
{: .spec }
    fmapE f  (Left e)   =  Left e
    fmapE f  (Right a)  =  Right (f a)
    fmapP f  (e, a)     =  (e, f a)
    fmapF f  g          =  f . g
    fmapId :: (Functor f, Eq (f a)) => f a -> Bool
    fmapId        =  fmap id === id
    fmapComp f g  =  (fmap f) . (fmap g)  ===  fmap (f . g)
    infix 4 ===
    (===) :: Eq a => (t -> a) -> (t -> a) -> t -> Bool
    (f === g) x  =  f x == g x
    fmapId_E x = 
        [ fmapE id x
        , case x of
            Left e  -> Left e
            Right a -> Right (id a)
        , case x of
            Left e  -> Left e
            Right a -> Right a    
        , x ]
    fmapId_P (e, a) = 
        [ fmapP id (e, a)
        , (e, id a)
        , (e, a) ]
    fmapId_F f =    
      [ fmapF id f
      , id . f
      , \x -> id (f x)
      , \x -> f x ]

## ListT
{: .types }
    -- /Note:/ this does not yield a monad unless the argument monad is commutative.
    newtype ListT m a = ListT { runListT :: m [a] }
    mapListT :: (m [a] -> n [b]) -> ListT m a -> ListT n b
    mapListT f m = ListT $ f (runListT m)
    instance (Functor m) => Functor (ListT m) where
        fmap f = mapListT $ fmap $ map f
    instance (Applicative m) => Applicative (ListT m) where
        pure a  = ListT $ pure [a]
        f <*> v = ListT $ (<*>) <$> runListT f <*> runListT v
    instance (Applicative m) => Alternative (ListT m) where
        empty   = ListT $ pure []
        m <|> n = ListT $ (++) <$> runListT m <*> runListT n
    instance (Monad m) => Monad (ListT m) where
        return a = ListT $ return [a]
        m >>= k  = ListT $ do
            a <- runListT m
            b <- mapM (runListT . k) a
            return (concat b)
        fail _ = ListT $ return []
    instance (Monad m) => MonadPlus (ListT m) where
        mzero       = ListT $ return []
        m `mplus` n = ListT $ do
            a <- runListT m
            b <- runListT n
            return (a ++ b)
    instance MonadTrans ListT where
        lift m = ListT $ do
            a <- m
            return [a]
    instance (MonadIO m) => MonadIO (ListT m) where
        liftIO = lift . liftIO
    liftCallCC :: ((([a] -> m [b]) -> m [a]) -> m [a]) ->
        ((a -> ListT m b) -> ListT m a) -> ListT m a
    liftCallCC callCC f = ListT $
        callCC $ \c ->
        runListT (f (\a -> ListT $ c [a]))
    liftCatch :: (m [a] -> (e -> m [a]) -> m [a]) ->
        ListT m a -> (e -> ListT m a) -> ListT m a
    liftCatch catchError m h = ListT $ runListT m
        `catchError` \e -> runListT (h e)

## Monad commutativity
{: .spec }
    type Equal a = [a]
    (===) :: a -> a -> Equal a
    a === b = [a, b]
    commutative :: (Monad m) => m a -> m b -> (a -> b -> m c) -> Equal (m c)
    commutative m1 m2 f = lhs === rhs
      where  lhs =  do  a1 <- m1
                        a2 <- m2
                        f a1 a2 
             rhs =  do  a2 <- m2
                        a1 <- m1
                        f a1 a2 
    spec_comm_Either = commutative
    -- Monomorphic types
    type E = String
    type A = Int
    type B = Bool
    type C = Char
    spec_comm_Either_mono :: (Either E A) -> (Either E B) -> (A -> B -> Either E C) -> Equal (Either E C)
    spec_comm_Either_mono = spec_comm_Either
    -- the Blind modifier is not required on the exam
    test_E = quickCheck (\ma mb (Blind f) -> allEq $ spec_comm_Either_mono ma mb f)
    -- Only one of these three answers is needed for the exam:
    -- (Either e) is not a commutative monad because bind returns the _first_ error only.
    -- ((,) e) is commutative iff the Monoid e is commutative (so, not for
    --   the typical case of the Writer with e = [a])
    -- ((->) e) is commutative: the environment is unchanged along the computation 
    instance (Arbitrary e, Arbitrary a) => Arbitrary (Either e a) where
      arbitrary = do n <- choose (0,10)
                     if n == 0 
                       then  liftM Left   arbitrary
                       else  liftM Right  arbitrary
    spec_comm_Fun_mono = commutative
    bindF :: ((->) e) a -> (a -> ((->) e) b) -> ((->) e) b
    -- bindF :: (e -> a) -> (a -> (e -> b)) -> (e -> b)
    bindF ma f = \e -> f (ma e) e
    commute m1 m2 f = 
      [ do a1 <- m1; a2 <- m2; f a1 a2
      , do a2 <- m2; a1 <- m1; f a1 a2 ]
    commute_F :: (e->a) -> (e->b) -> (a -> b -> (e->c)) -> Equal (e->c)
    commute_F m1 m2 f = 
      [ do a1 <- m1; a2 <- m2; f a1 a2                        -- do sugar
      , m1 >>= \a1 -> do a2 <- m2; f a1 a2                    -- do sugar
      , m1 >>= \a1 -> m2 >>= \a2 -> f a1 a2                   -- (>>=) is bindF
      , bindF m1 (\a1 -> bindF m2 (\a2 -> f a1 a2))           -- Def. of bindF
      , bindF m1 (\a1 -> \e' -> (\a2 -> f a1 a2) (m2 e') e')  -- beta-reduction
      , bindF m1 (\a1 -> \e' -> f a1 (m2 e') e')              -- Def. of bindF 
      , \e -> (\a1 -> \e' -> f a1 (m2 e') e') (m1 e) e        -- beta-red.
      , \e -> (\e' -> f (m1 e) (m2 e') e') e                  -- beta-red.
      , \e -> f (m1 e) (m2 e) e                               -- Proof midpoint
      , \e -> (\e' -> f (m1 e') (m2 e) e') e                  -- ~= same backwards
      , \e -> (\a2 -> \e' -> f (m1 e') a2 e') (m2 e) e
      , bindF m2 (\a2 -> \e' -> f (m1 e') a2 e')
      , bindF m2 (\a2 -> \e' -> (\a1 -> f a1 a2) (m1 e') e')
      , bindF m2 (\a2 -> bindF m1 (\a1 -> f a1 a2))
      , m2 >>= \a2 -> m1 >>= \a1 -> f a1 a2
      , m2 >>= \a2 -> do a1 <- m1; f a1 a2
      , do a2 <- m2; a1 <- m1; f a1 a2 ]
    allEq :: Eq a => [a] -> Bool
    allEq [] = True
    allEq (x:xs) = all (x==) xs
    -- the Blind modifier is not required on the exam
    test3 = quickCheck (\(Blind ma) (Blind mb) (Blind f) e -> 
                         allEq $ map ($e) $ 
                         commute_F (ma :: E->A) (mb :: E->B) 
                                   (f :: A -> B -> (E->C)))

## Error Monad
{: .types }
instance (Error e) => Monad (Either e) where
    return        = Right
    Left  l >>= _ = Left l
    Right r >>= k = k r
    fail msg      = Left (strMsg msg)
instance (Error e) => MonadPlus (Either e) where
    mzero            = Left noMsg
    Left _ `mplus` n = n
    m      `mplus` _ = m
instance (Error e) => MonadFix (Either e) where
    mfix f = let
        a = f $ case a of
            Right r -> r
            _       -> error "empty mfix argument"
        in a
instance (Error e) => MonadError e (Either e) where
    throwError             = Left
    Left  l `catchError` h = h l
    Right r `catchError` _ = Right r
newtype ErrorT e m a = ErrorT { runErrorT :: m (Either e a) }
mapErrorT :: (m (Either e a) -> n (Either e' b))
          -> ErrorT e m a
          -> ErrorT e' n b
mapErrorT f m = ErrorT $ f (runErrorT m)
instance (Monad m) => Functor (ErrorT e m) where
    fmap f m = ErrorT $ do
        a <- runErrorT m
        case a of
            Left  l -> return (Left  l)
            Right r -> return (Right (f r))
instance (Monad m, Error e) => Monad (ErrorT e m) where
    return a = ErrorT $ return (Right a)
    m >>= k  = ErrorT $ do
        a <- runErrorT m
        case a of
            Left  l -> return (Left l)
            Right r -> runErrorT (k r)
    fail msg = ErrorT $ return (Left (strMsg msg))
instance (Monad m, Error e) => MonadPlus (ErrorT e m) where
    mzero       = ErrorT $ return (Left noMsg)
    m `mplus` n = ErrorT $ do
        a <- runErrorT m
        case a of
            Left  _ -> runErrorT n
            Right r -> return (Right r)
instance (MonadFix m, Error e) => MonadFix (ErrorT e m) where
    mfix f = ErrorT $ mfix $ \a -> runErrorT $ f $ case a of
        Right r -> r
        _       -> error "empty mfix argument"
instance (Monad m, Error e) => MonadError e (ErrorT e m) where
    throwError l     = ErrorT $ return (Left l)
    m `catchError` h = ErrorT $ do
        a <- runErrorT m
        case a of
            Left  l -> runErrorT (h l)
            Right r -> return (Right r)
instance (Error e) => MonadTrans (ErrorT e) where
    lift m = ErrorT $ do
        a <- m
        return (Right a)
instance (Error e, MonadIO m) => MonadIO (ErrorT e m) where
    liftIO = lift . liftIO
instance (Error e, MonadCont m) => MonadCont (ErrorT e m) where
    callCC f = ErrorT $
        callCC $ \c ->
        runErrorT (f (\a -> ErrorT $ c (Right a)))
instance (Error e, MonadRWS r w s m) => MonadRWS r w s (ErrorT e m)
instance (Error e, MonadReader r m) => MonadReader r (ErrorT e m) where
    ask       = lift ask
    local f m = ErrorT $ local f (runErrorT m)
instance (Error e, MonadState s m) => MonadState s (ErrorT e m) where
    get = lift get
    put = lift . put
instance (Error e, MonadWriter w m) => MonadWriter w (ErrorT e m) where
    tell     = lift . tell
    listen m = ErrorT $ do
        (a, w) <- listen (runErrorT m)
        case a of
            Left  l -> return $ Left  l
            Right r -> return $ Right (r, w)
    pass   m = ErrorT $ pass $ do
        a <- runErrorT m
        case a of
            Left  l      -> return (Left  l, id)
            Right (r, f) -> return (Right r, f)

# Type Families: Vectors with length type
{: .types }
    data Zero
    data Suc n
    data Vec a n where
      Nil   :: Vec a Zero
      Cons  :: a -> Vec a n -> Vec a (Suc n)
    type family    Add  m        n  :: *
    type instance  Add  Zero     n  =  n     
    type instance  Add  (Suc m)  n  =  Suc (Add m n)
    (+++) :: Vec a m -> Vec a n -> Vec a (Add m n)
    Nil        +++  ys  =  ys
    Cons x xs  +++  ys  =  Cons x (xs +++ ys)
    -- Nil :: Vec a Zero
    -- return type = Vec a (Add Zero n) = Vec a n = the type of ys
    -- Cons x xs :: Vec a (Suc m)
    -- return type = Vec a (Add (Suc m) n) = Vec a (Suc (Add m n)) = type of the RHS
    {- Would it still type check with the alternative definition of
    type-level addition below?  Why/why not?  -}
    type family    Add'  m  n        :: *
    type instance  Add'  m  Zero     =  m     
    type instance  Add'  m  (Suc n)  =  Suc (Add' m n)
    {- No, it would not type check. The case split in the function
    definition must match the case split in the type family, otherwise the
    type unification will fail. It is possible to work around it using a
    family for type equality and a coerce function. -}
    -- Task (b): Implement a GADT |Fin n| for unary numbers below |n| and
    -- a lookup function |(!) :: Vec a n -> Fin n -> a|.
    data Fin n where
      Fzero :: Fin (Suc n)
      Fsuc  :: Fin n -> Fin (Suc n)
    (!) :: Vec a n -> (Fin n -> a)
    Cons x xs  !  Fzero    =  x
    Cons x xs  !  (Fsuc i) =  xs ! i

## List induction
{: .spec }
    {- Pick any |x|.
    Proof by induction on the list |ys| for the predicate
      P ys = length (insert x ys) === 1 + length ys
    Base case |P []|:
         length (insert x [])
    ==  {- Def. |ins.0| -}
         length [x]
    ==  {- Def. |len.0| -}
         1 + length []
    Case |P (y:ys)|:
    Induction hypothesis |P ys| is 
      |length (insert x ys) === 1 + length ys|.
    subcase |x <= y|:
         length (insert x (y:ys))
    ==  {- Def. |ins.1a| -}
         length (x : y : ys)
    ==  {- Def. |len.1| -}
         1 + length (y:ys) 
    subcase |x > y|:
         length (insert x (y:ys))
    ==  {- Def. |ins.1b| -}
         length (y : insert x ys)
    ==  {- Def. |len.1| -}
         1 + length (insert x ys) 
    ==  {- Induction hypothesis -}
         1 + (1 + length ys)
    ==  {- Def. |len.1| -}
         1 + length (y:ys) -}

## EDSL explanations
{: .edsl }
    {- Question text: Explain briefly the following EDSL terminology in
    general: deep embedding, shallow embedding, constructors, combinators
    and run function.  Exemplify by referring to or contrasting with your
    implementation.  
    Possible answers:
    * Deep embedding:
    A DSL implemented near the syntax, deep down from the sematics of the
    domain, is called a "deep embedding". The code above is an example -
    the |DateSet| datatype directly captures the abstract syntax of the
    domain, not the semantics.
    * Shallow embedding:
    A DSL implemented near the semantics is called a "shallow
    embedding". Often it can be constructed by tupling up suitable
    run-functions. The example above is not done that way (mainly because
    it is a bit tricky to handle the combination of infinite and finite
    lists effectively).
    * constructors
    Functions which build elements of the domain from "other
    data". Examples include |Once|, |Daily|, |Weekly|, |Monthly|,
    |Yearly|, |Start|, |End|.
    * combinators 
    Functions which build elements of the domain from other elements of
    the domain (+perhaps some other data). Examples include |Union|,
    |Intersection|.
    * run functions
    Functions from the domain to some semantics. In our example we have
    |isIn|, |toList| and |upperBound|. -}

## DateSet
{: .edsl }
    type Weekday  = Int
    type Monthday = Int
    type Yearday  = Int
    data DateSet = Once Date | Daily | Weekly  Weekday
     | Monthly Monthday | Yearly  Yearday
     | Union DateSet DateSet | Intersection DateSet DateSet
     | Start Date  | End Date
    between :: Date -> Date -> DateSet
    between start end = Intersection (Start start) (End end)
    -- The constructor |Once| is not necessary
    once :: Date -> DateSet
    once d = between d d
    isIn :: Date -> DateSet -> Bool
    isIn d (Once d')           = d == d'
    isIn d  Daily              = True
    isIn d (Weekly  a)         = weekday  d  == a
    isIn d (Monthly a)         = monthday d  == a
    isIn d (Yearly  a)         = yearday  d  == a
    -- isIn d (Filter p ds)       = p d      && isIn d ds
    isIn d (Union x y)         = isIn d x || isIn d y
    isIn d (Intersection x y)  = isIn d x && isIn d y
    isIn d (Start s)           = s <= d
    isIn d (End   e)           = d <= e
    -- try to locate an upperBound
    upperBound :: DateSet -> Date
    upperBound (Intersection x y) = min (upperBound x) (upperBound y)
    upperBound (Union x y)        = max (upperBound x) (upperBound y)
    upperBound (End   e)          = e
    -- upperBound (Filter p ds)      = upperBound ds
    upperBound (Once d)           = d
    upperBound _                  = maxDate
    maxDate :: Date
    maxDate = readD "9999-12-31"   -- somewhat arbitrary choice
    -- and a lowerBound (not part of exam question)
    lowerBound :: DateSet -> Date
    lowerBound (Intersection x y) = max (lowerBound x) (lowerBound y)
    lowerBound (Union x y)        = min (lowerBound x) (lowerBound y)
    lowerBound (Start   s)        = s
    -- lowerBound (Filter p ds)      = lowerBound ds
    lowerBound (Once d)           = d
    lowerBound _                  = minDate
    minDate :: Date
    minDate = readD "0000-01-01"   -- somewhat arbitrary choice
    toList :: DateSet -> [Date]
    toList ds = filter (`isIn` ds) [lowerBound ds .. upperBound ds]
    test :: DateSet
    test = Intersection (between (readD "2011-08-23") 
                                 (readD "2011-12-20")) 
                        (Weekly 1)
    main = print (toList test)
