{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module TEST where

import Data.Kind

data Dict c where
  Dict :: c => Dict c

instance Show (Dict c) where
  show = const "Dict"

class Foo (c :: Constraint) where
  foo :: Maybe (Dict c)

instance {-# OVERLAPPABLE #-} Foo z where
  foo = Nothing

instance Show a => Foo (Show a) where
  foo = Just $ Dict @(Show a)

