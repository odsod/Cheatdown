Monad laws
----------
    return a >>= f == f a
    m >>= return == m
    (m >>= f) >>= g == m >>= (\x -> fx >>= g)

Functor laws
------------
    fmap id = id
    fmap (p . q) = (fmap p) . (pmap q)

Transformer laws
----------------
    (lift .) return = return
    (lift .) (f >=> g) = (lift .) f >=> (lift .) g

Reader monad
------------
    instance MonadReader r ((->) r) where
        ask       = id
        local f m = m . f
    instance (Monad m) => Monad (ReaderT r m) where
        return a = ReaderT $ \_ -> return a
        m >>= k  = ReaderT $ \r -> do
            a <- runReaderT m r
            runReaderT (k a) r
        fail msg = ReaderT $ \_ -> fail msg
    instance (MonadPlus m) => MonadPlus (ReaderT r m) where
        mzero       = ReaderT $ \_ -> mzero
        m `mplus` n = ReaderT $ \r -> runReaderT m r `mplus` runReaderT n r

Writer monad
------------
    instance (Monoid w, Monad m) => Monad (WriterT w m) where
        return a = WriterT $ return (a, mempty)
        m >>= k  = WriterT $ do
            ~(a, w)  <- runWriterT m
            ~(b, w') <- runWriterT (k a)
            return (b, w `mappend` w')

State monad
-----------
    instance (Monad m) => Monad (StateT s m) where
        return a = StateT $ \s -> return (a, s)
        m >>= k  = StateT $ \s -> do
            ~(a, s') <- runStateT m s
            runStateT (k a) s'
        fail str = StateT $ \_ -> fail str

Maybe monad
-----------
    instance (Monad m) => Monad (MaybeT m) where
      fail _ = MaybeT (return Nothing)
      return = lift . return
      x >>= f = MaybeT (runMaybeT x >>= maybe (return Nothing) (runMaybeT . f))

Monoid laws
-----------
    mappend mempty x = x
    mappend x mempty = x
    mappend x (mappend y z) = mappend (mappend x y) z
    mconcat = foldr mappend mempty

Curry-Howard Correspondence
---------------------------
    p :: P          p is a proof of P
    empty type      False
    nonempty type   True
    P -> Q          P implies Q
    (P, Q)          P and Q
    Either P Q      P or Q

# Shape: Shallow
    newtype Shape = Shape { runShape :: Point -> Bool }
    empty :: Shape
    empty = Shape $ \_ -> False
    disc = Shape $ \p -> norm p <= 1
      where norm p = sqrt $ (vecX p)^2 + (vecY p)^2
    scale :: Vec -> Shape -> Shape
    scale v s = Shape $ \p -> inside (p `divide` v) s
    rotate :: Angle -> Shape -> Shape
    rotate a s = Shape $ \p -> inside (rot (-a) p) s
    intersect :: Shape -> Shape -> Shape
    intersect s1 s2 = Shape $ \p -> p `inside` s1 || p `inside` s2
    difference :: Shape -> Shape -> Shape
    difference s1 s2 = Shape $ \p -> p `inside` s1 && not (p `inside` s2)
    inside :: Point -> Shape -> Bool
    inside p s = runShape s p

# Shape: Deep
    inside :: Point -> Shape -> Bool
    inside p Empty = False
    inside p Disc = norm <= 1
      where x = vecX p; y = vecY p; norm p = sqrt $ (x*x) + (y*y)
    inside p Square = isq (vecX p) && isq (vecY p)
      where isq c = c <= 1 && c >= 0
    inside p (Translate v s) = inside (sub p v) s
    inside p (Scale v s) = inside (divide p v) s
    inside p (Rotate a s) = inside (rot -a p) s
    inside p (Union s1 s2) = inside p s1 || inside p s2 
    inside p (Intersect s1 s2) = inside p s1 && inside p s2
    inside p (Difference s1 s2) = inside p s1 && not $ inside p s2

## Functors
    instance Functor (Either e) where
      fmap f (Right x) = Right (f x)
      fmap _ (Left x) = Left x
    instance Functor ((,) e) where
      fmap f (x, y) = (x, f y)
    instance Functor ((->) e) where
      fmap = (.)
    instance Monad (Either e) where
      return x = Right x
      Right x >>= f = f x
      Left err >>= f = Left err

## ListT
    newtype ListT m a = ListT { runListT :: m [a] }
    instance (Monad m) => Monad (ListT m) where
      return = returnLT
      (>>=) = bindLT
    returnLT :: Monad m => a -> ListT m a
    returnLT a = ListT $ return [a]
    returnLT' :: Monad m => a -> ListT m a
    returnLT' = ListT . return . (:[])
    returnLT'' :: Monad m => a -> ListT m a
    returnLT'' = ListT . return . return
    bindLT :: Monad m => (ListT m a) -> (a -> ListT m b) -> (ListT m b)
    bindLT ltm f = ListT mLb
      where mLb = do as <- runListT ltm -- as :: m [a]
                     bss <- mapM (runListT . f) as
                     return (concat bss)

## Signal: Deep
    data Signal a where
      ConstS :: a -> Signal a
      TimeS  :: Signal Time
      MapT   :: (Time -> Time) -> Signal a -> Signal a
      (:$$)  :: Signal (a -> b) -> Signal a -> Signal b
    constS = ConstS
    timeS = TimeS
    fs $$ xs = fs :$$ xs
    mapS f xs = constS f $$ xs
    mapT = MapT
    sample (ConstS x)  = const x
    sample TimeS       = id
    sample (f :$$ s)   = \t -> sample f t $ sample s t
    sample (MapT f s)  = sample s . f

## Signal: Shallow
    newtype Signal a = Sig {unSig :: Time -> a}
    constS x = Sig (const x)
    timeS = Sig id
    fs $$ xs = Sig (\t -> unSig fs t  (unSig xs t))
    mapS f xs = constS f $$ xs
    mapT f xs = Sig (unSig xs . f)
    sample = unSig

## Signal: Examples
    sinS :: Double -> Signal Double
    sinS freq = mapT (freq*) $ mapS sin timeS
    instance Functor Signal where fmap = mapS
    instance Applicative Signal where pure  = constS; (<*>) = ($$)
    averageS :: Fractional a => 
                Signal a -> Signal a -> Signal a
    averageS xs ys = mapS average xs $$ ys
    averageA :: (Fractional a, Applicative f) => 
                 f a -> f a -> f a
    averageA xs ys = average <$> xs <*> ys
    averageA' = liftA2 average

## Shape: Shallow
    newtype Shape = Shape (Point -> Bool)
    empty = Shape $ \_ -> False
    disc = Shape $ \p -> ptX p ^ 2 + ptY p ^ 2 <= 1
    square = Shape $ \p -> abs (ptX p) <= 1 && abs (ptY p) <= 1
    transform m sh = Shape $ \p -> (m' `mul` p) `inside` sh
      where m' = inv m  -- the point is transformed with the inverse matrix
    translate v sh = Shape $ \p -> inside (p `sub` v) sh
    union sh1 sh2 = Shape $ \p -> inside p sh1 || inside p sh2
    intersect sh1 sh2 = Shape $ \p -> inside p sh1 && inside p sh2
    invert sh = Shape $ \p -> not (inside p sh)
    p `inside` Shape sh = sh p

## Shape: Deep
    _ `inside` Empty             = False
    p `inside` Disc              = sqDistance p <= 1
    p `inside` Square            = maxnorm  p <= 1
    p `inside` Translate v sh    = (p `sub` v) `inside` sh
    p `inside` Transform m sh    = (inv m `mul` p) `inside` sh
    p `inside` Union sh1 sh2     = p `inside` sh1 || p `inside` sh2
    p `inside` Intersect sh1 sh2 = p `inside` sh1 && p `inside` sh2
    p `inside` Invert sh         = not (p `inside` sh)
    sqDistance p = x*x+y*y -- proper distance would use sqrt
      where x = ptX p; y = ptY p
    maxnorm p = max (abs x) (abs y)
      where x = ptX p; y = ptY p

## Signal Shape
    animate :: Window -> Time -> Time -> Signal Shape -> IO ()
    animate win t0 t1 ss = mapM_ display frames
      where
        ts     = samples t0 t1 (round $ (t1 - t0) * fps)
        frames = map (sample ss) ts
        display sh = do
          putStr $ ansiClearScreen ++ ansiGoto 1 1 ++ render win sh
          usleep 70000  -- sleeping removes flickering
    rotatingSquare = constS rotate $$ timeS $$ constS square
    rotatingSquare = rotate <$> timeS <*> pure square
    bouncingBall = constS translate $$ pos $$ constS ball
    bouncingBall = translate <$> pos <*> pure ball
      where
        ball = scale (vec 0.5 0.5) disc
        pos  = constS vec $$ bounceX $$ bounceY
        bounceY = mapS (sin . (3*)) timeS
    --    bounceX = constS 0
    --    bounceX = mapS (sin . (2*)) timeS
        bounceX = mapS (0.3*) bounceY
    --example = constS difference $$ rotatingSquare $$ bouncingBall
    example = difference <$> rotatingSquare <*> bouncingBall

## Program: Shallow
    type Input  = String
    type Output = String
    type IOSem a = Input -> (a, Input, Output)
    newtype Program a = P { unP :: IOSem a }
    putC c = P $ \i -> ((), i, [c])
    getC = P $ \i -> case i of
      []     ->  (Nothing,  [],  [])
      c : i' ->  (Just c,   i',  [])
    instance Monad Program where
      return x  =  P $ \i -> (x, i, [])
      p >>= k   =  P $ \i ->
        let  (x,  i1,  o1)  =  unP  p      i
             (y,  i2,  o2)  =  unP  (k x)  i1
        in   (y,  i2,  o1 ++ o2)
    run = unP

## Program: Deep
    run (Put c) i = ((), i, [c])
    run Get [] = (Nothing, [], [])
    run Get (c : i) = (Just c, i, [])
    run (Return x) i = (x, i, [])
    run (p :>>= f) i = (y, i2, o1 ++ o2) 
      where (x, i1, o1) = run p i
            (y, i2, o2) = run (f x) i1

## Program: Derived
    putS = mapM_ putC
    putSLn s = putS (s ++ "\n")
    getLn = do
      mc <- getC
      case mc of
        Nothing   -> return ""
        Just '\n' -> return ""
        Just c    -> do
          s <- getLn
          return $ c : s
    run_ p i = case run p i of
      (x, _, o) -> (x, o)
    runPut p i = do 
      let (x, o) = run_ p i
      putStr o
      return x
    runIO p = getContents >>= runPut p
    runIONonBlocking p = getString >>= runPut p
      where
        getString = whileM (hReady stdin) getChar

## WhileM
    whileM :: Monad m => m Bool -> m a -> m [a]
    whileM cond body = do
      ok <- cond
      if ok then do
          x <- body
          xs <- whileM cond body
          return (x : xs)
        else
          return []

## Parser: Reference
    type Semantics s a = [s] -> [(a,[s])]
    -- Deep
    run' :: Parser1 s a -> Semantics s a
    run' Symbol (c : s) = [(c, s)]
    run' Symbol [] = []
    run' Fail _ = []
    run' (p :+++ q) s = run' p s ++ run' q s
    run' (Return x) s = [(x, s)]
    run' (p :>>= f) s = [(y, s'') 
                         | (x, s')  <- run' p s
                         , (y, s'') <- run' (f x) s']

## Parser laws
    -- L1.  return x >>= f   ==  f x
    -- L2.  p >>= return     ==  p
    -- L3.  (p >>= f) >>= g  ==  p >>= (\x -> f x >>= g)
    -- More laws about >>=, (+++) and fail
    -- L4.  fail >>= f       ==  fail
    -- L5.  (p +++ q) >>= f  ==  (p >>= f) +++ (q >>= f)
    -- Laws about (+++) and fail
    -- L6.  fail +++ q       ==  q
    -- L7.  p +++ fail       ==  p
    -- Laws about (+++)
    -- L8.  (p +++ q) +++ r  ==  p +++ (q +++ r)
    -- L9.  p +++ q          ==  q +++ p           
    -- multisets are important in L9!
    -- Laws about >>=, (+++) and symbol
    -- L10. (symbol >>= f) +++ (symbol >>= g)
    --       ==  symbol >>= (\c -> f c +++ g c)
    -- Here is the proof of L10
    --   [| (symbol >>= f) +++ (symbol >>= g) |] (c:s)         
    --  { semantics of (+++) }
    -- [| symbol >>= f |] (c:s) ++ [| symbol >>= g |] (c:s)  
    --  { semantics of >>= and symbol }
    -- [| f c |] s ++ [| g c |] s                   
    --  { semantics of (+++) }
    -- [| f c +++ g c |] s                                  
    --  { semantics of symbol and >>= }
    -- [| symbol >>= (\x -> f x +++ g x) |] (c:s)

## Parser 2
    data Parser2 s a where
        SymbolBind2  ::  (s -> Parser2 s a) -> Parser2 s a
        -- SymbolBind f  â‰œ  Symbol >>= f
        Return2      ::  a -> Parser2 s a
        (::+++)      ::  Parser2 s a -> Parser2 s a -> Parser2 s a
        Fail2        ::  Parser2 s a
    run2 :: Parser2 s a -> Semantics s a
    run2 (SymbolBind2 f)  []      =  []
    run2 (SymbolBind2 f)  (x:xs)  =  run2 (f x) xs 
                              -- ~=  run (Symbol >>= f) (x:xs)
    run2 (Return2 y)      l       =  [ (y , l) ] 
    run2 (y ::+++ y')     l       =  run2 y l ++ run2 y' l
    run2 Fail2            l       =  []
    run2' :: Parser2 s a -> Semantics s a
    run2' (SymbolBind2 f)  = symbolBind2S (run2 . f)
    run2' (Return2 y)      = returnS y
    run2' (y ::+++ y')     = run2 y  `choiceS`  run2 y'
    run2' Fail2            = failS
    symbolBind2S :: (s -> Semantics s a) -> Semantics s a
    symbolBind2S f []      =  []
    symbolBind2S f (x:xs)  =  f x xs 
    symbolBind2S' :: (s -> Semantics s a) -> Semantics s a
    symbolBind2S' f = symbolS  `bindS`  f

## Translating parsers
    -- It turns out that we can also translate Parser1 into Parser2.
    p12 :: Parser1 s a -> Parser2 s a
    p12 Symbol      =  SymbolBind2 Return2 -- L1
    p12 Fail        =  Fail2
    p12 (y :+++ q)  =  p12 y ::+++ p12 q
    p12 (Return y)  =  Return2 y 
    p12 (Symbol      :>>= q)  =  SymbolBind2 (p12 . q) 
                                -- def of SymbolBind
    p12 (Fail        :>>= q)  =  Fail2 
                                -- Parser law. L4.
    p12 ((y :+++ q)  :>>= y0) =  p12 (y :>>= y0) ::+++ 
                                 p12 (q :>>= y0) 
                                -- Parser law. L5
    p12 (Return y    :>>= q)  =  p12 (q y) 
                                -- monad law, L1
    p12 ((p :>>= k') :>>= k)  =  p12 (p :>>= (\x -> k' x :>>= k)) 
                                -- monad law, L3

## Parser 3
    -- Can we linearize choice as well (+++)?
    data Parser3 s a where
        SymbolBind3    ::  (s -> Parser3 s a) -> Parser3 s a
        ReturnChoice3  ::  a -> Parser3 s a   -> Parser3 s a 
        -- ReturnChoice x p  â‰œ  Return x +++ p
        Fail3          ::  Parser3 s a
    run3 :: Parser3 s a -> Semantics s a
    run3 (SymbolBind3 f)      []        =  []
    run3 (SymbolBind3 f)      (s : ss)  =  run3 (f s) ss
    run3 (ReturnChoice3 x p)  l         =  (x , l) : run3 p l 
                                    -- ~= run (Return x +++ p)
    run3 Fail3                l         =  []

## Translating parsers 2 - 3
    p23 :: Parser2 s a -> Parser3 s a
    p23 (SymbolBind2 f)  =  SymbolBind3 (p23 . f)
    p23 (Return2 x)      =  ReturnChoice3 x Fail3 
                            -- def. of ReturnChoice
    p23 (p ::+++ q)      =  best (p23 p) (p23 q)
    p23 Fail2            =  Fail3
    best :: Parser3 s a -> Parser3 s a -> Parser3 s a
    best (SymbolBind3 f)      (SymbolBind3 g)     -- L10
      = SymbolBind3 (\s -> best (f s) (g s))   
    best p                    (ReturnChoice3 x q) -- L8 (+++ commut)
      = ReturnChoice3 x (best p q)             
    best (ReturnChoice3 x q)  p                   -- L9 (+++ assoc)
      = ReturnChoice3 x (best p q)
    best p Fail3 = p   -- L6
    best Fail3 q = q   -- L7

## Parsers: Efficient implementation
    -- | Efficient implementation for general syntax:
    parse :: P s a -> Semantics s a
    parse = run3 . p23 . p12
    -- we could show formally: 
    -- (x , s) âˆˆ run  p ss  <=>  (x , s) âˆˆ run2 (p12 p) ss
    -- (x , s) âˆˆ run2 p ss  <=>  (x , s) âˆˆ run3 (p23 p) ss
    -- and therefore:
    -- (x , s) âˆˆ run p ss   <=>  (x , s) âˆˆ parse p ss

## Interpreter: Types
    data Expr = Lit Integer | Expr :+ Expr | Var Name | Let Name Expr Expr
              | NewRef Expr | Deref Expr | Expr := Expr | Catch Expr Expr
    type Name   = String
    type Value  = Integer
    type Ptr    = Value
      -- ^ dangerous language: any 'Value' can be used as a 'Ptr'
    type Env = Map Name Value
    emptyEnv = Map.empty
    data Store = Store { nextPtr :: Ptr , heap :: Map Ptr Value }
    emptyStore = Store 0 Map.empty
    data Err = SegmentationFault | UnboundVariable String | OtherError String
    instance CME.Error Err where
      strMsg = OtherError
      noMsg  = CME.strMsg ""

## Interpreter: Monad stack
    newtype Eval a = Eval { unEval :: 
        CMS.StateT Store (CMR.ReaderT Env (CME.ErrorT Err
                            CMI.Identity)) a }
      deriving (Monad, CMS.MonadState  Store,
                       CMR.MonadReader Env,
                       CME.MonadError  Err)
    runEval :: Eval a -> Either Err a
    runEval = CMI.runIdentity . CME.runErrorT
            . startReaderFrom emptyEnv
            . startStateFrom  emptyStore
            . unEval
    startStateFrom :: Monad m => state -> CMS.StateT state m a -> m a
    startStateFrom = flip CMS.evalStateT
    CMS.evalStateT :: Monad m => CMS.StateT state m a -> (state -> m a)
    startReaderFrom :: env -> CMR.ReaderT env m a -> m a
    startReaderFrom = flip CMR.runReaderT
    CMR.runReaderT :: CMR.ReaderT env m a -> (env -> m a)

## Interpreter: State
    lookupVar :: Name -> Eval Value
    lookupVar x = do
      env <- CMR.ask
      case Map.lookup x env of
        Nothing  -> CME.throwError $ UnboundVariable x  -- new
        Just v   -> return v
    extendEnv :: Name -> Value -> Eval a -> Eval a
    extendEnv x v = CMR.local (Map.insert x v)
    newRef :: Value -> Eval Ptr
    newRef v = do
      s <- CMS.get
      let ptr = nextPtr s
          s'  = s { nextPtr = ptr + 1
                  , heap    = Map.insert ptr v (heap s) }
      CMS.put s'
      return ptr
    deref :: Ptr -> Eval Value
    deref p = do
      h <- CMS.gets heap
      case Map.lookup p h of
        Nothing -> CME.throwError SegmentationFault
        Just v  -> return v
    (=:) :: Ptr -> Value -> Eval Value
    p =: v = do
      CMS.modify $ \s -> s { heap = Map.adjust (const v) p (heap s) }
      return v

## Interpreter: Run function
    eval :: Expr -> Eval Value
    eval (Lit n)        = return n
    eval (a :+ b)       = CM.liftM2 (+) (eval a) (eval b)
    eval (Var x)        = lookupVar x
    eval (Let x e1 e2)  = do
      v1 <- eval e1
      extendEnv x v1 (eval e2)
    eval (NewRef e)     = newRef =<< eval e
    eval (Deref e)      = deref =<< eval e
    eval (pe := ve)     = do
      p <- eval pe
      v <- eval ve
      p =: v
    eval (Catch e1 e2)  = eval e1 `CME.catchError` \_ -> 
                          eval e2

## Interpreter: Parsec parser
    data Language e = Lang { 
         lLit    :: Integer -> e
       , lPlus   :: e -> e -> e
       , lLet    :: String -> e -> e -> e
       , lVar    :: String -> e
       , lNewref :: e -> e
       , lDeref  :: e -> e
       , lAssign :: e -> e -> e
       , lCatch  :: e -> e -> e
       }
    tok :: TokenParser st
    tok = makeTokenParser LanguageDef
      { commentStart    = "{-"
      , commentEnd      = "-}"
      , commentLine     = "--"
      , nestedComments  = True
      , identStart      = satisfy (\c -> isAlpha c || c == '_')
      , identLetter     = satisfy (\c -> isAlphaNum c || c == '_')
      , opStart         = satisfy (`elem` "+:=!;")
      , opLetter        = satisfy (`elem` "=")
      , reservedNames   = ["let", "new", "try", "catch"]
      , reservedOpNames = ["+", ":=", "=", "!", ";"]
      , caseSensitive   = True
      }
    parseExpr :: Language e -> String -> Either ParseError e
    parseExpr lang = parse exprP ""
      where
        exprP = do
          e <- expr0
          eof
          return e
        expr0 = choice
          [ do reserved tok "let"
               x <- identifier tok
               reservedOp tok "="
               e1 <- expr2
               reservedOp tok ";"
               e2 <- expr0
               return $ lLet lang x e1 e2
          , do reserved tok "try"
               e1 <- expr0
               reserved tok "catch"
               e2 <- expr0
               return $ lCatch lang e1 e2
          , expr1
          ]
        expr1 = chainr1 expr2 (reservedOp tok ";" >> return (lLet lang "_"))
        expr2 = chainr1 expr3 (reservedOp tok ":=" >> return (lAssign lang))
        expr3 = chainl1 expr4 plusP
        expr4 = choice
          [ atomP
          , do reservedOp tok "!"
               e <- expr4
               return (lDeref lang e)
          , do reserved tok "new"
               e <- expr4
               return (lNewref lang e)
          ]
        atomP = choice
          [ lLit lang <$> integer tok
          , lVar lang <$> identifier tok
          , parens tok expr0
          ]
        plusP = reservedOp tok "+" >> return (lPlus lang)

## Monad stacking order
    {-We add an error monad to our evaluation monad. It matters whether
    we stick the error monad on the outside or the inside of the state
    monad. In this case we stick it on the inside.
    We can understand the interaction between the state monad and the
    error monad by looking at their implementations. With ErrorT on
    the outside, we will represent computations as
      ms (Either err a)   ~=   s -> (Either err a,  s)
    where ms is the underlying monad with state. Since the state is
    hidden inside m it is not affected by whether we return @Right a@
    or @Left err@.  In other words state changes won't be rolled back
    when there's an exception.
    If we turn it around, adding a state monad on top of an error
    monad, computations will be represented as
      s -> me (a, s)      ~=   s -> Either err  (a, s)
    Here it's clear that if a computation fails, we lose any changes
    to the state made by the failing computation since the state is
    just passed as a return value in the underlying monad.-}
