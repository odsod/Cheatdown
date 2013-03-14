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

Shallow Shape
-------------

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

Deep Shape
----------

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

Functors
--------

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

ListT
-----

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
