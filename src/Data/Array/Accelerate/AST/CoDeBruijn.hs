{-# LANGUAGE GADTs #-}
-- McBride's haskell implementation is at https://github.com/pigworker/Saturday/blob/master/src/B.hs, but is completely untyped

module Data.Array.Accelerate.AST.CoDeBruijn where



data Take x xargs args where
  Here  :: Take x (x ->  args)       args
  There :: Take x       xargs        args
        -> Take x (y -> xargs) (y -> args)


-- Every arg occurs in at least one of the two subargs.
data SplitCoEnv args largs rargs where
  Base  :: SplitCoEnv args args ()
  Left  :: Take x xt t
        -> SplitCoEnv  t       l        r
        -> SplitCoEnv xt (x -> l)       r
  Right :: Take x xt t
        -> SplitCoEnv  t       l        r
        -> SplitCoEnv xt       l  (x -> r)
  Both  :: Take x xt t
        -> SplitCoEnv  t       l        r
        -> SplitCoEnv xt (x -> l) (x -> r)

------------------
-- Alternative to SplitCoEnv, you can also use these two:
-- They should be isomorphic, but I don't know which is 
-- easier to use yet.
------------------
data CoIdx xargs args x where
  Take  :: Take x xargs args -> CoIdx xargs  args x
  Leave :: Take x xargs args -> CoIdx xargs xargs x

data GetArgs xsargs args xs where
  None :: GetArgs args args ()
  Some :: CoIdx xxsargs xsargs x
       -> GetArgs  xsargs args       xs
       -> GetArgs xxsargs args (x -> xs)
