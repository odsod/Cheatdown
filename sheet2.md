## Signal: Examples
    -- | sinusoidal of given frequency
    sinS :: Double -> Signal Double
    sinS freq = mapT (freq*) $ mapS sin timeS
    test1 :: IO ()
    test1 = magic $ sinS 0.1
    average :: Fractional a =>  a -> a -> a
    average x y = (x + y) / 2.0
    averageS :: Fractional a => Signal a -> Signal a -> Signal a
    averageS xs ys = mapS average xs $$ ys
    -- | It can also be generalised to an arbitray Applicative functor
    averageA :: (Fractional a, Applicative f) => f a -> f a -> f a
    averageA xs ys = average <$> xs <*> ys
    -- | or slightly shorter
    averageA' :: (Fractional a, Applicative f) => f a -> f a -> f a
    averageA' = liftA2 average
    scale :: Num a =>  Signal a -> Signal a
    scale = mapS ((30*) . (1+))
    -- | Discretize a signal
    discretize :: Signal Double -> Signal Int
    discretize = mapS round
    -- | convert to "analog"
    toBars :: Signal Int -> Signal String
    toBars = mapS (`replicate` '#') 
    displayLength = 100
    -- | display the signal at a number of points
    display :: Signal String -> IO ()
    display ss = forM_ [0..displayLength] $ \x ->
       putStrLn (sample ss x)
    -- | The display magic. Note how we take advantage of function composition, 
    -- types defined so far, etc.
    magic :: Signal Double -> IO ()
    magic = display . toBars . discretize . scale
    -- | Signal is an applicative functor
    instance Functor Signal where fmap = mapS
    instance Applicative Signal where pure  = constS; (<*>) = ($$)

## Matrix
    type Angle  = Double
    data Vec    = V { vecX, vecY :: Double }
    type Point  = Vec
    data Matrix = M Vec Vec
    -- | Matrix creation
    matrix :: Double -> Double -> Double -> Double -> Matrix
    matrix a b c d = M (V a b) (V c d)
    vec = V
    point = vec
    cross :: Vec -> Vec -> Double
    cross (V a b) (V c d) = a * c + b * d
    mul :: Matrix -> Vec -> Vec
    mul (M r1 r2) v = V (cross r1 v) (cross r2 v)
    inv :: Matrix -> Matrix
    inv (M (V a b) (V c d)) = matrix (d / k) (-b / k) (-c / k) (a / k)
      where k = a * d - b * c
    sub :: Point -> Vec -> Point
    sub (V x y) (V dx dy) = V (x - dx) (y - dy)
    ptX, ptY :: Point -> Double
    ptX = vecX
    ptY = vecY

## Signal: Shallow
    type Time = Double
    newtype Signal a = Sig {unSig :: Time -> a}
    constS :: a -> Signal a
    constS x = Sig (const x)
    timeS  :: Signal Time
    timeS = Sig id
    -- | Function application lifted to signals.
    ($$)   :: Signal (a -> b) -> Signal a -> Signal b
    fs $$ xs = Sig (\t -> unSig fs t  (unSig xs t))
    -- | Mapping a function over a signal.
    mapS   :: (a -> b)        -> Signal a -> Signal b
    mapS f xs = constS f $$ xs
    -- | Transforming the time.
    mapT   :: (Time -> Time)  -> Signal a -> Signal a
    mapT f xs = Sig (unSig xs . f)
    -- | Sampling a signal at a given time point.
    sample :: Signal a -> Time -> a  
    sample = unSig

## Signal: Deep
    type Time = Double
    data Signal a where
      ConstS :: a -> Signal a
      TimeS  :: Signal Time
      MapT   :: (Time -> Time) -> Signal a -> Signal a
      (:$$)  :: Signal (a -> b) -> Signal a -> Signal b
    sample (ConstS x)  = const x
    sample TimeS       = id
    sample (f :$$ s)   = \t -> sample f t $ sample s t
    sample (MapT f s)  = sample s . f

## Shape: Derived
    -- | Derived combinators
    scale :: Vec -> Shape -> Shape
    scale v = transform (matrix  (vecX v)  0 
                                 0         (vecY v))
    rotate :: Angle -> Shape -> Shape
    rotate d = transform (matrix  c  (-s) 
                                  s  c   )
      where  c = cos d
             s = sin d
    difference :: Shape -> Shape -> Shape
    difference sh1 sh2 = sh1 `intersect` invert sh2

## Shape: Shallow
    newtype Shape = Shape (Point -> Bool)
    empty :: Shape
    empty = Shape $ \_ -> False
    disc :: Shape
    disc = Shape $ \p -> ptX p ^ 2 + ptY p ^ 2 <= 1
    square :: Shape
    square = Shape $ \p -> abs (ptX p) <= 1 && abs (ptY p) <= 1
    -- | Transform a shape with a matrix.
    transform :: Matrix -> Shape -> Shape
    transform m sh = Shape $ \p -> (m' `mul` p) `inside` sh
      where m' = inv m  -- the point is transformed with the inverse matrix
    -- | To represent translations as matrix transformations we would need
    --   to add another dimension to the matrices (excercise).
    translate :: Vec -> Shape -> Shape
    translate v sh = Shape $ \p -> inside (p `sub` v) sh
    union :: Shape -> Shape -> Shape
    union sh1 sh2 = Shape $ \p -> inside p sh1 || inside p sh2
    intersect :: Shape -> Shape -> Shape
    intersect sh1 sh2 = Shape $ \p -> inside p sh1 && inside p sh2
    invert :: Shape -> Shape
    invert sh = Shape $ \p -> not (inside p sh)
    inside :: Point -> Shape -> Bool
    p `inside` Shape sh = sh p

## Shape: Deep
    data Shape where
      Empty   :: Shape
      Disc    :: Shape
      Square  :: Shape
      Translate :: Vec ->   Shape -> Shape
      Transform :: Matrix-> Shape -> Shape
      Union     :: Shape -> Shape -> Shape
      Intersect :: Shape -> Shape -> Shape
      Invert    :: Shape -> Shape
    inside :: Point -> Shape -> Bool
    _  `inside` Empty             = False
    p  `inside` Disc              = sqDistance p <= 1
    p  `inside` Square            = maxnorm  p <= 1
    p  `inside` Translate v sh    = (p `sub` v) `inside` sh
    p  `inside` Transform m sh    = (inv m `mul` p) `inside` sh
    p  `inside` Union sh1 sh2     = p `inside` sh1 || p `inside` sh2
    p  `inside` Intersect sh1 sh2 = p `inside` sh1 && p `inside` sh2
    p  `inside` Invert sh         = not (p `inside` sh)
    sqDistance :: Point -> Double
    sqDistance p = x*x+y*y -- proper distance would use sqrt
      where x = ptX p
            y = ptY p
    maxnorm :: Point -> Double
    maxnorm p = max (abs x) (abs y)
      where x = ptX p
            y = ptY p

## Shape: Render
    -- | A window specifies what part of the world to render and at which
    --   resolution.
    data Window = Window
      { bottomLeft :: Point , topRight :: Point, resolution :: (Int, Int) }
    defaultWindow = Window
      { bottomLeft  = point (-1.5) (-1.5)
      , topRight    = point 1.5 1.5
      , resolution  = (25, 25)
    --  , resolution = (50, 50) -- for larger terminal windows
      }
    -- | Generate a list of evenly spaces samples between two values.
    samples :: Double -> Double -> Int -> [Double]
    samples x0 x1 n = take n $ iterate (+dx) x0
      where dx = (x1 - x0) / fromIntegral (n - 1)
    -- | Generate the matrix of points corresponding to the pixels of a window.
    pixels :: Window -> [[Point]]
    pixels (Window p0 p1 (w,h)) =
      [  [ point x y | x <- samples (ptX p0) (ptX p1) w ]
      |  y <- reverse $ samples (ptY p0) (ptY p1) h ]
    -- | Render a shape in a given window.
    render :: Window -> Shape -> String
    render win sh = unlines $ map (concatMap putPixel) (pixels win)
      where putPixel p  | p `inside` sh = "[]"
                        | otherwise     = "  "

## Shape: Animate
    -- | Combining 'Signal' and 'Shape' to obtain moving objects.
    fps = 10   -- we generate 10 fps
    -- | Animate a shape valued signal.
    animate :: Window -> Time -> Time -> Signal Shape -> IO ()
    animate win t0 t1 ss = mapM_ display frames
      where
        ts     = samples t0 t1 (round $ (t1 - t0) * fps)
        frames = map (sample ss) ts
        display sh = do
          putStr $ ansiClearScreen ++ ansiGoto 1 1 ++ render win sh
          usleep 70000  -- sleeping removes flickering

## Shape: Animation Examples
    -- | A rotating square
    rotatingSquare :: Signal Shape
    rotatingSquare = constS rotate $$ timeS $$ constS square
                  -- Using the Control.Applicative interface:
    -- rotatingSquare = rotate <$> timeS <*> pure square
    -- | A bouncing ball
    bouncingBall :: Signal Shape
    -- bouncingBall = constS translate $$ pos $$ constS ball
    bouncingBall = translate <$> pos <*> pure ball
      where
        ball = scale (vec 0.5 0.5) disc
        pos  = constS vec $$ bounceX $$ bounceY
        bounceY = mapS (sin . (3*)) timeS
    --    bounceX = constS 0
    --    bounceX = mapS (sin . (2*)) timeS
        bounceX = mapS (0.3*) bounceY
    -- | Combining the two
    example :: Signal Shape
    --example = constS difference $$ rotatingSquare $$ bouncingBall
    example = difference <$> rotatingSquare <*> bouncingBall
    {- Illustrate type error and finding the solution
    example2 = difference <$> one <*> two
        where one :: Signal Shape 
              one = example
              two :: Signal Shape
              two = scale (vec (-1) (0.5)) one -}                        
    runExample = animate defaultWindow 0 endTime example where endTime = 15

## Program: Shallow
    {-| A simple embedded language for input/output. Shallow embedding. -}
    type Input  = String
    type Output = String
    -- | Shallow embedding: programs are represented by their semantics.
    --   In this case a program is a function from the input to the 
    --   result, the remaining input and the output.
    type IOSem a = Input -> (a, Input, Output)
    newtype Program a = P { unP :: IOSem a }
    putC :: Char -> Program ()
    putC c = P $ \i -> ((), i, [c])
    getC :: Program (Maybe Char)
    getC = P $ \i -> case i of
      []     ->  (Nothing,  [],  [])
      c : i' ->  (Just c,   i',  [])
    instance Monad Program where
      return x  =  P $ \i -> (x, i, [])
      p >>= k   =  P $ \i ->
        let  (x,  i1,  o1)  =  unP  p      i
             (y,  i2,  o2)  =  unP  (k x)  i1
        in   (y,  i2,  o1 ++ o2)
    -- | Running a program is simply returning its semantics.
    run :: Program a -> IOSem a
    run = unP

## Program: Deep 1
    type Input   =  String
    type Output  =  String
    data Program a where
      Put    :: Char -> Program ()
      Get    :: Program (Maybe Char)
      Return :: a -> Program a
      (:>>=) :: Program a -> (a -> Program b) -> Program b
    type IOSem a = Input -> (a, Input, Output)
    -- | run function: translate syntax to semantics
    run :: Program a -> IOSem a
    run (Put c)     i        =  ((),       i,   [c])
    run Get         []       =  (Nothing,  [],  [])
    run Get         (c : i)  =  (Just c,   i,   [])
    run (Return x)  i        =  (x,        i,   [])
    run (p :>>= f)  i        =  (y,        i2,  o1 ++ o2) 
      where  (x,  i1,  o1)   =  run p i
             (y,  i2,  o2)   =  run (f x) i1

## Program: Deep 2
    import Control.Monad((>=>))
    -- > (>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
    -- > f >=> g   =   \c ->  f c >>= g
    type Input   =  String
    type Output  =  String
    data Program a = PutBind Char (Program a) 
                   | GetBind (Maybe Char -> Program a) | Return a
    -- | It turns out that bind can still be defined!
    instance Monad Program where
      return = Return
      PutBind c p  >>=  k   =  PutBind c (p >>= k)
      GetBind f    >>=  k   =  GetBind (f >=> k)
      Return x     >>=  k   =  k x
    {- I pulled the above out of my hat, but...
       We can *calculate* the correct definition of (>>=) using
       the follwing intuitive meaning of PutBind and GetBind
        @PutBind c p == putC c >> p@
        @GetBind f   == getC >>= f@
     and the monad laws:
        Law 1.  return x >>= f   ==  f x
        Law 2.  m >>= return     ==  m
        Law 3.  (m >>= f) >>= g  ==  m >>= (\x -> f x >>= g)
       For instance,
          GetBind f >>= k             { meaning of GetBind }
      ==  (getC >>= f) >>= k          { third monad law }
      ==  getC >>= (\c -> f c >>= k)  { meaning of GetBind }
      ==  GetBind (\c -> f c >>= k)
      ==  GetBind (f >=> k) -}
    putC :: Char -> Program ()
    putC c = PutBind c $ Return ()
    getC :: Program (Maybe Char)
    getC = GetBind Return
    type IOSem a = Input -> (a, Input, Output)
    run :: Program a -> IOSem a
    run (PutBind c p)  i        =  (x,  i',  c : o)
      where (x, i', o)  =  run p i
    run (GetBind f)    []       =  run (f Nothing)   []
    run (GetBind f)    (c : i)  =  run (f $ Just c)  i
    run (Return x)     i        =  (x,  i,  [])

## Program: Example
    putS :: String -> Program ()
    putS = mapM_ putC
    putSLn :: String -> Program ()
    putSLn s = putS (s ++ "\n")
    getLn :: Program String
    getLn = do
      mc <- getC
      case mc of
        Nothing   -> return ""
        Just '\n' -> return ""
        Just c    -> do
          s <- getLn
          return $ c : s
    -- | Run function which throws away the remaining inputs.
    run_ :: Program a -> Input -> (a, Output)
    run_ p i = case run p i of
      (x, _, o) -> (x, o)
    -- | Run a program p with input i as an IO computation writing to
    --   stdout.
    runPut :: Program b -> Input -> IO b
    runPut p i = do 
      let (x, o) = run_ p i
      putStr o
      return x
    -- | Run a program as an IO computation reading from stdin and
    --   writing to stdout.
    runIO :: Program a -> IO a
    runIO p = getContents >>= runPut p
    -- | Run a program on whatever is available on stdin at the moment.
    --   Useful for writing event driven programs where you don't want
    --   to block the program waiting for the user to press a key.
    runIONonBlocking :: Program a -> IO a
    runIONonBlocking p = getString >>= runPut p
      where
        -- Read as much from stdin as possible without blocking.
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

## Program: Game engine
    -- | A game with state s is a program which given a game state computes the
    --   next state, doing some input/output in the process.
    -- 'Nothing' represents the end of the game.
    type Game s = s -> Program (Maybe s)
    -- | Run a game with a given delay between each states.
    gameLoop :: Float -> Game s -> s -> IO ()
    gameLoop dt step st = do
      r <- runIONonBlocking (step st)
      case r of
        Nothing   -> return ()
        Just st'  -> do
          usleep (round $ dt * 1000000)
          gameLoop dt step st'
    -- | Top-level function for running a game.
    runGame :: Float -> Game s -> s -> IO ()
    runGame dt step st = do
      putStr ansiClearScreen
      hSetBuffering stdin  NoBuffering -- Don't wait for newline when reading from stdin
      hSetBuffering stdout NoBuffering -- Don't wait when writing either
      hSetEcho stdin False             -- Don't echo characters on stdin
      gameLoop dt step st
      hSetEcho stdin True -- Turn echo back on.
      putStr $ ansiGoto 1 30

## Program: Coord
    type Coord = (Int, Int)
    data Dir = North | East | South | West
      deriving (Eq, Show, Enum)
    movePos :: Coord -> Dir -> Coord
    movePos (x, y) d = case d of
      North -> (x,      y - 1)
      East  -> (x + 1,  y)
      South -> (x,      y + 1)
      West  -> (x - 1,  y)
    outOfBounds (x,y) = x<0 || y<0
    -- could also check some maximum x and y

## Program: Snake
    -- | A snake is a list of body coord.s and a dir. of travel.
    data Snake = Snake { pos :: [Coord] , dir :: Dir }
    -- | The starting position of the snake.
    startingSnake = Snake ((11,10) : replicate 20 (10,10)) East
    -- | Check if a snake has collided with itself.
    collision :: Snake -> Bool
    collision g = case pos g of
      []      -> False
      p : ps  -> outOfBounds p  ||  p `elem` ps
    -- | Output a string at a given coordinate (uses some ANSI magic).
    putStrAt :: Coord -> String -> Program ()
    putStrAt p s = putS $ gotoPos p ++ s
      where gotoPos (x, y) = ansiGoto (x * 2 + 1) (y + 1)
    -- | Draw the snake. The last part of the tail is erased.
    drawSnake :: Colour -> String -> Snake -> Program ()
    drawSnake col px s = do
      let ps = pos s
      putStrAt (last ps) "  "                 -- erase previous tail
      putStrAt (head ps) $ ansiColour col px  -- print new head
    -- | The different actions that the player can take.
    data Action = Turn Dir | Exit deriving Show
    -- | Keyboard controls. Binds keys to actions.
    controls :: [(Char, Action)]
    controls = zip "wasd" (map Turn [North, West, South, East]) ++
                  [ ('q', Exit), ('\ESC', Exit) ]
    -- | One step of the actual game
    snake :: Game Snake
    snake g 
      | collision g = putStrAt (5, 7) >> "Game Over!" >> stop
      | otherwise = do
          drawSnake Yellow  "()" g
          putStrAt (0,0) ""
          mc <- getC
          case mc >>= \c -> lookup c controls of  -- Maybe is a monad
            Nothing       -> continue_
            Just (Turn d) -> continue d
            Just Exit     -> stop
      where
        -- Moving the snake means adding a new head and removing 
        -- the last element of the tail.
        move (p:ps) d = movePos p d : p : init ps
        stop          = return Nothing
        continue_     = continue (dir g)
        continue d    = return $ Just $ g { pos = move (pos g) d
                                          , dir = d }

## Parser: Utils
    -- | Parse a symbol satisfying a given predicate.
    sat :: (s -> Bool) -> P s s
    sat p = symbol >>= \x if p x then return x else pfail
    -- | Parse a particular symbol.
    this :: Eq s => s -> P s s
    this x = sat (x ==)
    -- | Parse a digit as a number.
    digitP :: P Char Int
    digitP = sat isDigit >>= \c -> return $ charToInt c
      where charToInt c = fromEnum c - fromEnum '0'
    -- | Parse a left associative operator carefully avoiding left
    -- recursion.
    --    chainLeft Op T ::= E
    --          where E  ::=  E Op T  |  T
    chainLeft :: P s (a -> a -> a)  ->  P s a  ->  P s a
    chainLeft op term = term >>= chain
      where chain e = return e +++ do
            o  <- op
            e' <- term
            chain (e `o` e')

## Parsers: Naive Deep
    data Parser1 s a where
      Symbol  ::  Parser1 s s
      Fail    ::  Parser1 s a
      (:+++)  ::  Parser1 s a -> Parser1 s a -> Parser1 s a
      Return  ::  a -> Parser1 s a
      (:>>=)  ::  Parser1 s a -> (a -> Parser1 s b) -> Parser1 s b
    type Semantics s a = [s] -> [(a,[s])]
    -- | Reference implementation/Semantics.  (It's easy to see that
    --   it's what we want, but maybe inefficient.)
    run :: Parser1 s a -> Semantics s a
    run Symbol      = symbolS
    run Fail        = failS
    run (p :+++ q)  = run p  `choiceS`  run q
    run (Return x)  = returnS x
    run (p :>>= f)  = run p  `bindS`  (run . f)

## Parser: Semantics
    {- Starting point:
    symbolS :: [s] -> [(s, [s])] -- Semantics s s
    symbolS []      = []        -- no parse
    symbolS (s:ss)  = [(s, ss)]  -- exactly one parse resuls
    failS   :: Semantics s a
    failS _ = []
    choiceS :: ([s] -> [(a, [s])]) -> Semantics s a -> ([s] -> [(a,[s])])
    choiceS p q ss = p ss ++ q ss
    returnS :: a -> [s] -> [(a, [s])]
    returnS x ss = [(x, ss)] -- exactly one parse, no input consumed
    -- bindS   :: Semantics s a -> (a -> Semantics s b) -> Semantics s b
    bindS   :: ([s] -> [(a, [s])]) ->         -- ^ the parser p
               (a -> ([s] -> [(b, [s])])) ->  -- ^ the function f
               [s] ->                         -- ^ the input string
               [(b, [s])]
    bindS p f ss = concatMap (uncurry f) (p ss)
    run' :: Parser1 s a -> Semantics s a
    run' Symbol      (c : s)  = [(c, s)]
    run' Symbol      []       = []
    run' Fail        _        = []
    run' (p :+++ q)  s        = run' p s ++ run' q s
    run' (Return x)  s        = [(x, s)]
    run' (p :>>= f)  s        = [(y, s'')  | (x, s')  <- run' p s
    {- symbolS :: Semantics s s
    symbolS (c : s)  =  [(c, s)]
    symbolS []       =  []
    failS :: Semantics s a
    failS _ = []
    choiceS :: Semantics s a -> Semantics s a -> Semantics s a
    choiceS left right = \s -> left s ++ right s
    returnS :: a -> Semantics s a
    returnS x = \s -> [(x, s)]
    bindS :: Semantics s a -> (a -> Semantics s b) -> Semantics s b
    bindS pa a2pb = concatMap (uncurry a2pb) . pa
    bindS' :: Semantics s a -> (a -> Semantics s b) -> Semantics s b
    bindS' pa a2pb = \s   ->  let  pas = pa s -- :: [(a, [s])]
                                   pbss = map (uncurry a2pb) pas
                              in concat pbss     
    bindS'' :: Semantics s a ->(a -> Semantics s b) -> Semantics s b
    bindS'' pa a2pb = \s   ->  [(y, s'')  | (x, s')  <- pa s
                                          , (y, s'') <- a2pb x s'] -}

## Parser: Optimization argument
    {- Using this reference semantics we can prove (exercise) a number
    of useful laws about parsers. We will use these laws later to
    derive an efficient implementation of the library.
      Notation: [| p |] = run p
      For two parsers p and q we define
        p == q  iff  âˆ€ s. [| p |] s == [| q |] s, 
          up to the order of elements in the result 
            (list is interpreted as a multiset).
      Monad Laws
        L1.  return x >>= f   ==  f x
        L2.  p >>= return     ==  p
        L3.  (p >>= f) >>= g  ==  p >>= (\x -> f x >>= g)
      More laws about >>=, (+++) and fail
        L4.  fail >>= f       ==  fail
        L5.  (p +++ q) >>= f  ==  (p >>= f) +++ (q >>= f)
      Laws about (+++) and fail
        L6.  fail +++ q       ==  q
        L7.  p +++ fail       ==  p
      Laws about (+++)
        L8.  (p +++ q) +++ r  ==  p +++ (q +++ r)
        L9.  p +++ q          ==  q +++ p           
             -- multisets are important in L9!
      Laws about >>=, (+++) and symbol
        L10. (symbol >>= f) +++ (symbol >>= g)
               ==  symbol >>= (\c -> f c +++ g c)
      Here is the proof of L10 for the case of a non-empty input
      string:
           [| (symbol >>= f) +++ (symbol >>= g) |] (c:s)         
      ==  { semantics of (+++) }
           [| symbol >>= f |] (c:s) ++ [| symbol >>= g |] (c:s)  
      ==  { semantics of >>= and symbol }
           [| f c |] s ++ [| g c |] s                   
      ==  { semantics of (+++) }
           [| f c +++ g c |] s                                  
      ==  { semantics of symbol and >>= }
          [| symbol >>= (\x -> f x +++ g x) |] (c:s)
      Exercise: prove or test the laws -}

## Parser: Problems
    {- The reference semantics is useful for reasoning, but
       inefficient.  There are three sources of inefficiency that we
       can identify:
       1. The list comprehension builds a lot of intermediate lists
       which might be costly.
       2. List append (++) is linear in its first argument which
       means that left nested appl.s of (+++) get a quadratic
       behaviour.
       3. (+++) is treated in a depth first way, first computing the
       results of the left parser, then computing the results of the
       second parser. This leads to a space leak since we have to
       hang on to the full input string to feed to the second
       parser, while traversing the string with the first parser.
    -}

## Parser: SymbolBind
    -- Can we linearize sequencing (>>=)? (Would help with 1.)
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
    {- symbolS  `bindS`  f  
    = { def. of bindS }
    concatMap (uncurry f) . symbolS
    = { def. of symbolS }
      \cs -> case cs of  []       -> concatMap (uncurry f) []
                         (c : s)  -> concatMap (uncurry f) [(c, s)]
    = { concatMap lemmas  }
      \cs -> case cs of  []       -> []
                         (c : s)  -> uncurry f (c, s)
    = { def. of uncurry }
      \cs -> case cs of  []       -> []
                         (c : s)  -> f c s -}
    -- It turns out that we can also translate Parser1 into Parser2.
    p12 :: Parser1 s a -> Parser2 s a
    p12 Symbol      =  SymbolBind2 Return2 -- L1
    p12 Fail        =  Fail2
    p12 (y :+++ q)  =  p12 y ::+++ p12 q
    p12 (Return y)  =  Return2 y 
    p12 (Symbol      :>>= q)  =  SymbolBind2 (p12 . q) 
                                -- def of SymbolBind
    p12 (Fail        :>>= q)  =  Fail2 -- Parser law. L4.
    p12 ((y :+++ q)  :>>= y0) =  p12 (y :>>= y0) ::+++ 
                                 p12 (q :>>= y0) -- Parser law. L5
    p12 (Return y    :>>= q)  =  p12 (q y) -- monad law, L1
    p12 ((p :>>= k') :>>= k)  =  p12 (p :>>= (\x -> k' x :>>= k)) 
                                 -- monad law, L3

## Parser: ReturnChoice
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
    -- But it turns out that we can translate 2 into 3!
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
    -- | Efficient implementation for general syntax:
    parse :: P s a -> Semantics s a
    parse = run3 . p23 . p12
    -- we could show formally: 
    -- (x , s) âˆˆ run  p ss  <=>  (x , s) âˆˆ run2 (p12 p) ss
    -- (x , s) âˆˆ run2 p ss  <=>  (x , s) âˆˆ run3 (p23 p) ss
    -- and therefore:
    -- (x , s) âˆˆ run p ss   <=>  (x , s) âˆˆ parse p ss

## Parser: Tests
    data Expr = Lit Int | Plus Expr Expr
    -- | A parser for expressions.
    exprP :: P Char Expr
    exprP = chainLeft plusP termP
      where
        -- Parse the plus sign. Returns the 'Plus' function.
        plusP :: P Char (Expr -> Expr -> Expr)
        plusP = this '+' >> return Plus
    termP :: P Char Expr
    termP = liftM Lit digitP +++ do
      this '('
      e <- exprP
      this ')'
      return e
    -- | We test that showing and then parsing is the identity and 
    --   that the parse is unambiguous.
    prop_parse :: Expr -> Bool
    prop_parse e = [e] == parseAll (show e)
      where
        -- Throw away incomplete parses
        parseAll :: String -> [Expr]
        parseAll s = [ x | (x, "") <- parse exprP s ]
    -- Bad:   
    --    parseAll s = [ x | (x, _) <- parse exprP s ]
    runTests = quickCheck prop_parse
    main = runTests
    -- quickCheck (\(Blind f) s -> concatMapSingletonLemma f s)
    -- * Testing infrastructure
    instance Show Expr where
      showsPrec p (Lit n)      = shows n
      showsPrec p (Plus e1 e2) = showParen (p > 0) $
        shows e1 . showString "+" . showsPrec 1 e2
    -- | For reference:
    -- > shows = showsPrec 0
    type Size = Int
    -- | Generating arbitrary expressions.
    instance Arbitrary Expr where
      arbitrary = sized arb
        where
          digit :: Gen Int
          digit = elements [0..9]
          arb :: Size -> Gen Expr
          arb 0 = liftM Lit digit
          arb n = frequency $
              (1, arb 0) :
            [ (4, liftM2 Plus arb2 arb2) | n > 0 ]
            where
              arb2 :: Gen Expr
              arb2 = arb (n `div` 2)

## Interpreter: Types
    data Expr = Lit Integer | Expr :+ Expr | Var Name
              | Let Name Expr Expr | NewRef Expr
              | Deref Expr | Expr := Expr | Catch Expr Expr
    type Name  = String
    type Value = Integer
    type Ptr   = Value
      -- dangerous language: any value can be used as a pointer
    -- | An environment maps variables to values.
    type Env = Map Name Value
    emptyEnv = Map.empty
    -- | We need to keep track of the store containing the values of our
    --   references. We also remember the next unused pointer.
    data Store = Store { nextPtr :: Ptr, heap    :: Map Ptr Value }
    emptyStore = Store 0 Map.empty
    data Err = SegmentationFault
             | UnboundVariable String
             | OtherError String
    instance CME.Error Err where
      strMsg = OtherError
      noMsg  = CME.strMsg ""

## Interpreter: Monad stacking order
    {-| We add an error monad to our evaluation monad. It matters whether
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
        just passed as a return value in the underlying monad.  -}

## Interpreter: Transformer stacks
    newtype Eval1 a = Eval1{ unEval1:: CMS.StateT Store
      (CMR.ReaderT Env (CME.ErrorT Err CMI.Identity)) a }
      deriving (Monad, CMS.MonadState  Store, CMR.MonadReader Env,
                CME.MonadError  Err)
    newtype Eval2 a = Eval2{ unEval2:: CME.ErrorT Err
     (CMS.StateT Store (CMR.ReaderT Env CMI.Identity)) a }
      deriving (Monad, CMS.MonadState  Store, CMR.MonadReader Env,
                CME.MonadError  Err)
    runEval1 :: Eval1 a -> Either Err a
    runEval1 = CMI.runIdentity . CME.runErrorT
             . startReaderFrom emptyEnv
             . startStateFrom  emptyStore . unEval1
    runEval2 :: Eval2 a -> Either Err a
    runEval2 = CMI.runIdentity
             . startReaderFrom emptyEnv
             . startStateFrom  emptyStore
             . CME.runErrorT . unEval2
    startStateFrom :: Monad m => state -> CMS.StateT state m a -> m a
    startStateFrom = flip CMS.evalStateT
    -- CMS.evalStateT :: Monad m => CMS.StateT state m a -> (state -> m a)
    startReaderFrom :: env -> CMR.ReaderT env m a -> m a
    startReaderFrom = flip CMR.runReaderT
      -- CMR.runReaderT :: CMR.ReaderT env m a -> (env -> m a)

## Interpreter: Environment
    -- | Here we just remove the type annotation
    -- lookupVar :: Name -> Eval Value
    lookupVar x = do
      env <- CMR.ask
      case Map.lookup x env of
        Nothing -> CME.throwError $ UnboundVariable x
        Just v  -> return v
    -- extendEnv :: Name -> Value -> Eval a -> Eval a
    extendEnv x v = CMR.local (Map.insert x v)
    -- | Create a new reference containing the given value.
    -- newRef :: Value -> Eval Ptr
    newRef v = do
      s <- CMS.get
      let ptr = nextPtr s
          s'  = s { nextPtr = ptr + 1
                  , heap    = Map.insert ptr v (heap s) }
      CMS.put s'
      return ptr
    -- deref :: Ptr -> Eval Value
    deref p = do
      h <- CMS.gets heap
      case Map.lookup p h of
        Nothing -> CME.throwError SegmentationFault
        Just v  -> return v
    -- (=:) :: Ptr -> Value -> Eval Value
    p =: v = do
      CMS.modify $ \s -> s { heap = Map.adjust (const v) p (heap s) }
      return v

## Interperter: Eval
    -- | The case for 'Catch' simply uses the 'catchError' function from
    --   the error monad.
    -- eval :: Expr -> Eval Value
    eval (Lit n)       = return n
    eval (a :+ b)      = CM.liftM2 (+) (eval a) (eval b)
    eval (Var x)       = lookupVar x
    eval (Let x e1 e2) = do
      v1 <- eval e1
      extendEnv x v1 (eval e2)
    eval (NewRef e)    = newRef =<< eval e
    eval (Deref e)     = deref =<< eval e
    eval (pe := ve)    = do
      p <- eval pe
      v <- eval ve
      p =: v
    eval (Catch e1 e2) = eval e1 `CME.catchError` \_ -> eval e2

## Interpreter: Examples
    testExpr1 = parse "!p+1738"
    testExpr2 = parse "(try !p catch 0)+1738"
    test1 = runEval1 $ eval testExpr1
    test2 = runEval2 $ eval testExpr2
    testExpr3 = parse "let one = new 1; \
                     \ let dummy = (try ((one := 2) + !7) catch 0); \
                     \ !one"
    run :: String -> Either Err Integer
    run s = runEval1 $ eval $ parse s
    examplePrograms :: [String]
    examplePrograms = [ "1700+38" , "let x=1+2; x+x" , 
        "let p=new 1; let q=new 1738; !(p+1)" , "!p+1738"
      , "(try !p catch 0)+1738" , "let one = new 1; \
        \let dummy = (try ((one := 2) + !7) catch 0); !one" ]
    exampleRuns :: [Either Err Integer]
    exampleRuns = map run examplePrograms
    main :: IO ()
    main = mapM_ print exampleRuns
    evalP :: ( CMR.MonadReader Env m , CMS.MonadState  Store m
             , CME.MonadError  Err m) => String -> m Value
    evalP = eval . parse
    run' :: String -> (Either Err Value, Either Err Value)
    run' s = ( runEval1 $ evalP s, runEval2 $ evalP s)

## Interpreter: Parser
    data Language e =
      Lang { lLit :: Integer -> e , lPlus :: e -> e -> e
           , lLet :: String -> e -> e -> e, lVar :: String -> e
           , lNewref :: e -> e , lDeref :: e -> e
           , lAssign :: e -> e -> e , lCatch :: e -> e -> e }
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
      , caseSensitive   = True }
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
          , expr1 ]
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
               return (lNewref lang e) ]
        atomP = choice
          [ lLit lang <$> integer tok
          , lVar lang <$> identifier tok
          , parens tok expr0 ]
        plusP = reservedOp tok "+" >> return (lPlus lang)

## Testing: Insertion sort
    q :: Q.Testable prop => prop -> IO ()
    q = Q.quickCheck
    -- The familiar insert sort function
    insert :: Ord a => a -> [a] -> [a]
    insert x [] = [x]
    insert x (y : xs)
      | x < y     = x : y : xs
      | otherwise = y : insert x xs
    sort :: Ord a => [a] -> [a]
    sort [] = []
    sort (x : xs) = insert x (sort xs)
    -- or equivalently
    -- > sort = foldr insert []
    -- * Properties
    -- | Checking that a list is ordered.
    ordered :: Ord a => [a] -> Bool
    ordered []           = True
    ordered [x]          = True
    ordered (x : y : xs) = x <= y  &&  ordered (y : xs)
    -- | 'sort' should produce ordered results.
    prop_sort :: [Integer] -> Bool
    prop_sort xs = ordered (sort xs)
    -- | 'insert' should preserve orderedness. Bad property!  Why:
    -- it's quite unlikely that a random longish list will be
    -- ordered so we will only test very short lists.  'collect'ing
    -- the lengths of the lists reveal this.
    -- Fix (exercise): write a generator for ordered lists.
    prop_ins :: Integer -> [Integer] -> Q.Property
    prop_ins x xs = ordered xs   Q.==>
                    Q.collect (length xs) (ordered (insert x xs))
    -- How to test properties about how our function treats elements
    -- it thinks are equal? We define a new type El
    -- | 'El's are compared only on their keys when sorting.
    type Key = Integer
    type Value = Integer
    data El = El Key Value
      deriving (Eq, Show)
    instance Ord El where
      compare (El a _) (El b _) = compare a b
      -- note that compare x y == EQ   /=   x==y in general
    instance Q.Arbitrary El where
      arbitrary = CM.liftM2 El Q.arbitrary Q.arbitrary
    -- | Sorting twice is the same as sorting once. Not true for our
    -- insertion sort!
    prop_idem :: [El] -> Bool
    prop_idem xs = sort (sort xs) == sort xs
    -- What is wrong? (spoiler below)
    -- A fixed (stable) version uses (<=) in insert
    insert' :: Ord a => a -> [a] -> [a]
    insert' x [] = [x]
    insert' x (y:xs)
      | x <= y    = x : y : xs
      | otherwise = y : insert' x xs

## GADTs: Expressions
    -- | A simple expression language with integers and booleans.
    -- Contains both well- and ill-typed expressions.
    data Expr where
      LitN  :: Int                           -> Expr
      LitB  :: Bool                          -> Expr
      (:+)  ::         Expr      -> Expr     -> Expr
      (:==) ::         Expr      -> Expr     -> Expr
      If    :: Expr -> Expr      -> Expr     -> Expr
    -- | A value is an integer or a boolean.
    data Value = VInt Int | VBool Bool
    -- | Evaluating expressions. Things are a bit complicated
    -- because we have to check that we get values of the right
    -- types for the operations. Fails if the evaluated expression
    -- isn't well-typed.
    eval :: Expr -> Value
    eval (LitN n)       =  VInt n
    eval (LitB b)       =  VBool b
    eval (e1 :+ e2)     =  plus (eval e1) (eval e2)
      where plus (VInt n) (VInt m) = VInt $ n + m
    eval (e1 :== e2)    =  eq (eval e1) (eval e2)
      where eq (VInt n)  (VInt m)  = VBool $ n == m
            eq (VBool a) (VBool b) = VBool $ a == b
    eval (If e1 e2 e3)  =  case eval e1 of
      VBool True   ->  eval e2
      VBool False  ->  eval e3
    eOK, eBad  :: Expr
    eOK  = If (LitB False) (LitN 1) (LitN 2 :+ LitN 1736)
    eBad = If (LitB False) (LitN 1) (LitN 2 :+ LitB True)
    -- Pretty printing.
    instance Show Expr where
      showsPrec p e = case e of
        LitN n       -> shows n
        LitB b       -> shows b
        e1 :+ e2     -> showParen (p > 2) $
          showsPrec 2 e1 . showString " + " . showsPrec 3 e2
        e1 :== e2    -> showParen (p > 1) $
          showsPrec 2 e1 . showString " == " . showsPrec 2 e2
        If e1 e2 e3  -> showParen (p > 0) $
          showString "if "    . shows e1 .
          showString " then " . shows e2 .
          showString " else " . shows e3
    -- Parsing expressions. Uses a slightly modified version of our
    -- parser library from lecture 4. Also goes crazy with the
    -- operators from "Control.Applicative".  Exercise: check out
    -- these combinators.
    type Token = String
    instance Read Expr where
      readsPrec p s = [ (x, unwords ts) 
                      | (x, ts) <- parse (exprP p) $ tokenize s ]
        where
          tokenize :: String -> [Token]
          tokenize "" = []
          tokenize s  = t : tokenize s'
            where [(t, s')] = lex s
          exprP :: Int -> P Token Expr
          exprP 0 = If <$> (this "if"   *> exprP 0)
                       <*> (this "then" *> exprP 0)
                       <*> (this "else" *> exprP 0)
                <|> exprP 1
          exprP 1 = (:==) <$> exprP 2 <*> (this "==" *> exprP 2)
                <|> exprP 2
          exprP 2 = chainLeft plusP (exprP 3)
            where plusP = (:+) <$ this "+"
          exprP _ = foldr1 (<|>)
            [ LitN . read  <$>  sat (all isDigit)
            , LitB . read  <$>  sat (`elem` ["True", "False"])
            , this "(" *> exprP 0 <* this ")"
            ]

## GADTs: Type checking
    {-# LANGUAGE GADTs, ExistentialQuantification #-}
    infixl 6 :+; infix  4 :==; infix  0 :::
    -- | The type of well-typed expressions. There is no way to
    -- construct an ill-typed expression in this datatype.
    data Expr t where
      LitN  :: Int                           -> Expr Int
      LitB  :: Bool                          -> Expr Bool
      (:+)  ::         Expr Int -> Expr Int  -> Expr Int
      (:==) :: Eq t => Expr t   -> Expr t    -> Expr Bool
      If    :: Expr Bool -> Expr t -> Expr t -> Expr t
    -- | A type-safe evaluator. Much nicer now that we now that
    -- expressions are well-typed. No Value datatype needed, no
    -- extra constructors VInt, VBool.
    eval :: Expr t -> t
    eval (LitN n)      =  n
    eval (LitB b)      =  b
    eval (e1 :+ e2)    =  eval e1 +  eval e2
    eval (e1 :== e2)   =  eval e1 == eval e2
    eval (If e1 e2 e3) =  if eval e1 then eval e2 else eval e3
    eOK :: Expr Int
    eOK  = If (LitB False) (LitN 1) (LitN 2 :+ LitN 1736)
    -- eBad = If (LitB False) (LitN 1) (LitN 2 :+ LitB True)
    -- | We can forget that an expression is typed. For instance, to
    -- be able to reuse the pretty printer we already have.
    forget :: Expr t -> E.Expr
    forget e = case e of
      LitN n      -> E.LitN n
      LitB b      -> E.LitB b
      e1 :+ e2    -> forget e1  E.:+   forget e2
      e1 :== e2   -> forget e1  E.:==  forget e2
      If e1 e2 e3 -> E.If (forget e1) (forget e2) (forget e3)
    instance Show (Expr t) where
      showsPrec p e = showsPrec p (forget e)
    -- How to go the other way, turning an untyped expression into a
    -- typed expression?
    -- Answer: we have to do type checking! Moreover, our type
    -- checker will have to convince the Haskell type checker to
    -- allow us to construct an element of Expr t from an untyped
    -- expression passing our type checker. In other words we are
    -- not writing a type checker for our own benefit, but to
    -- explain to GHC's type checker why a particular untyped term
    -- is really well-typed.
    -- | The types that an expression can have. Indexed by the
    -- corresponding Haskell type.
    data Type t where
      TInt  :: Type Int
      TBool :: Type Bool
    instance Show (Type t) where
      show TInt  = "Int"
      show TBool = "Bool"
    -- | Well-typed expressions of some type are just pairs of
    -- expressions and types which agree on the Haskell type. The
    -- /forall/ builds an existential type (exercise: think about
    -- whether this makes sense).
    data TypedExpr = forall t. Eq t =>   Expr t ::: Type t
    instance Show TypedExpr where
      show (e ::: t) = show e ++ " :: " ++ show t
    -- | When comparing two types it's not enough to just return a
    -- boolean.  Remember that we're trying to convince GHC's type
    -- checker that two types are equal, and just evaluating some
    -- arbitrary function to True isn't going to impress it.
    --   Instead we define a type of proofs that two types @a@ and
    --   @b@ are equal.  The only way to prove two types equal is if
    --   they are in fact the same, and then the proof is
    --   Refl. Evaluating one of these proofs to 'Refl' will
    --   convince GHC's type checker that the two type arguments are
    --   indeed equal (how else could the proof be Refl?).
    data Equal a b where
      Refl :: Equal a a
    -- | The type comparison function returns a proof that the types
    -- we compare are equal in the cases that they are.
    (=?=) :: Type s -> Type t -> Maybe (Equal s t)
    TInt  =?= TInt  = Just Refl
    TBool =?= TBool = Just Refl
    _     =?= _     = Nothing
    -- | Finally the type inference algorithm. We're making heavy
    -- use of the fact that pattern matching on a @Type t@ or an
    -- @Equal s t@ will tell GHC's type checker interesting things
    -- about @s@ and @t@.
    infer :: E.Expr -> Maybe TypedExpr
    infer e = case e of
      E.LitN n -> return (LitN n ::: TInt)
      E.LitB b -> return (LitB b ::: TBool)
      r1 E.:+ r2 -> do
        e1 ::: TInt  <-  infer r1
        e2 ::: TInt  <-  infer r2
        return (e1 :+ e2 ::: TInt)
      r1 E.:== r2 -> do
        e1 ::: t1    <-  infer r1
        e2 ::: t2    <-  infer r2
        Refl         <-  t1 =?= t2
        return (e1 :== e2 ::: TBool)
      E.If r1 r2 r3 -> do
        e1 ::: TBool <-  infer r1
        e2 ::: t2    <-  infer r2
        e3 ::: t3    <-  infer r3
        Refl         <-  t2 =?= t3
        return (If e1 e2 e3 ::: t2)
    -- | We can do type checking by inferring a type and comparing
    -- it to the type we expect.
    check :: E.Expr -> Type t -> Maybe (Expr t)
    check r t = do
      e ::: t' <- infer r
      Refl     <- t' =?= t
      return e
    test1R = read "1+2 == 3"
    test1  = fromJust (infer test1R)

## GADTs: Parser
    type ParseResult s a = [(a, [s])]
    data P s a where
      Fail   :: P s a
      -- ReturnChoice x p = return x +++ p
      ReturnChoice :: a -> P s a -> P s a
      -- SymbolBind f = symbol >>= f
      SymbolBind :: (s -> P s a) -> P s a
    symbol = SymbolBind return
    pfail  = Fail
    SymbolBind f +++ SymbolBind g = SymbolBind (\x -> f x +++ g x)
    Fail +++ q  = q
    p +++ Fail  = p
    ReturnChoice x p +++ q = ReturnChoice x (p +++ q)
    p +++ ReturnChoice x q = ReturnChoice x (p +++ q)
    instance Monad (P s) where
      return x = ReturnChoice x pfail
      Fail             >>= f = Fail
      ReturnChoice x p >>= f = f x +++ (p >>= f)
      SymbolBind k     >>= f = SymbolBind (k >=> f)
    instance Functor (P s) where
      fmap = liftM
    instance Applicative (P s) where
      pure = return
      (<*>) = ap
    instance Alternative (P s) where
      empty = pfail
      (<|>) = (+++)
    parse :: P s a -> [s] -> ParseResult s a
    parse (SymbolBind f) (c : s) = parse (f c) s
    parse (SymbolBind f) []      = []
    parse Fail       _           = []
    parse (ReturnChoice x p) s   = (x, s) : parse p s
    -- Derived combinators
    sat :: (s -> Bool) -> P s s
    sat p = do
      t <- symbol
      if p t then return t
             else pfail
    this :: Eq s => s -> P s s
    this x = sat (x ==)
    chainLeft :: P s (a -> a -> a) -> P s a -> P s a
    chainLeft op term = do
        e <- term
        chain e
      where
        chain e = return e +++ do
          o  <- op
          e' <- term
          chain (e `o` e')
