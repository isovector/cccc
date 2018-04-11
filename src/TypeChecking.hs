{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wall          #-}

module TypeChecking where

import           Bound
import           Bound.Scope
import           Control.Applicative ((<|>))
import           Control.Lens ((<&>), makeLenses, view, (%~), (<>~))
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Bifunctor
import           Data.Bool (bool)
import           Data.List (nub, intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>), First (..))
import qualified Data.Set as S
import           Data.Traversable (for)
import           Debug.Trace (trace)
import           Prelude hiding (exp)
import           Types


data TIState = TIState
  { _tiVNames :: Int
  , _tiTNames :: Int
  , _tiSubst  :: Subst
  }

makeLenses ''TIState

type TI = ExceptT String (State TIState)


unify :: Type -> Type -> TI ()
unify t1 t2 = do
  s  <- view tiSubst <$> get
  s' <- mgu (sub s t1) (sub s t2)
  modify $ tiSubst <>~ s'
  pure ()


kind :: Type -> TI Kind
kind (TVar x)  = pure $ tKind x
kind (TCon x)  = pure $ tKind x
kind TInt      = pure KStar
kind TUnit     = pure KStar
kind TVoid     = pure KStar
kind (a :@@ b) = do
  ka <- kind a
  kb <- kind b
  let kerr kk = throwE $ mconcat
        [ "kind mismatch: '"
        , show b
        , " :: "
        , show kb
        , "' vs '"
        , show kk
        , "'\nwhen trying to apply '"
        , show a
        , " :: "
        , show ka
        , "'\n"
        ]
  case ka of
    kal :>> kar -> do
      when (kal /= kb) $ kerr kal
      pure kar
    KStar -> kerr KStar


newVName :: (Int -> a) -> TI a
newVName f = do
  n <- view tiVNames <$> get
  modify $ tiVNames %~ (+1)
  pure $ f n


letters :: [String]
letters = do
  b <- "":letters
  a <- ['a'..'z']
  pure $ a : b


runTI :: TI a -> Either String a
runTI = flip evalState (TIState 0 0 mempty) . runExceptT


newTyVar :: Kind -> TI Type
newTyVar k = do
  n <- view tiTNames <$> get
  modify $ tiTNames %~ (+1)
  pure . TVar . flip TFreshName k $ letters !! n


freshInst :: Scheme -> TI (Qual Type)
freshInst (Scheme vars t) = do
  nvars <- traverse newTyVar $ fmap tKind vars
  let subst = Subst $ M.fromList (zip vars nvars)
  pure $ sub subst t


mgu :: Type -> Type -> TI Subst
mgu (l :@@ r) (l' :@@ r') = do
  s1 <- mgu l l'
  s2 <- mgu (sub s1 r) (sub s1 r')
  pure $ s1 <> s2
mgu (TCon a) (TCon b)
  | a == b  = pure mempty
mgu (TVar u) t  = varBind u t
mgu t (TVar u)  = varBind u t
mgu TInt TInt   = pure mempty
mgu TVoid TVoid = pure mempty
mgu TUnit TUnit = pure mempty
mgu t1 t2       = throwE $
  mconcat
    [ "types don't unify: '"
    , show t1
    , "' vs '"
    , show t2
    , "'"
    ]


varBind :: TName -> Type -> TI Subst
varBind u t
  | t == TVar u = pure mempty
  | S.member u (free t) = throwE
      $ mconcat
        [ "occurs check: '"
        , show u
        , "' vs '"
        , show t
        , "'"
        ]
  | otherwise = do
      k <- kind t
      when (k /= tKind u) $ throwE "kind unification fails"
      pure $ Subst [(u, t)]


splatter :: Monad f => c -> Scope b f c -> f c
splatter = splat pure . const . pure


inferLit :: Lit -> Type
inferLit (LitInt _)  = TInt
inferLit (LitBool _) = TBool
inferLit LitUnit     = TUnit


infer
    :: (Int -> VName)
    -> SymTable VName
    -> Exp VName
    -> TI ([Pred], Type)
infer f env (Assert e t) = do
  (p1, t1) <- infer f env e
  unify t t1
  s <- view tiSubst <$> get
  pure (sub s p1, t)
infer _ (SymTable env) (V a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> do
      (ps :=> x) <- freshInst sigma
      pure (ps, x)
infer f env (Let _ e1 b) = do
  name <- newVName f
  let e2 = splatter name b
  (p1, t1) <- infer f env e1
  let t'   = generalize env $ p1 :=> t1
      env' = SymTable $ M.insert name t' $ unSymTable env
  (p2, t2) <- infer f env' e2
  pure (p2, t2)
infer _ _ (Lit l) = pure (mempty, inferLit l)
infer f env (LInj which a) = do
  t <- newTyVar KStar
  (p1, t1) <- infer f env a
  t2 <- newTyVar KStar
  unify t $ bool id flip which TProd t1 t2
  pure (p1, t)

infer f env (LProd a b) = do
  t <- newTyVar KStar
  (p1, t1) <- infer f env a
  (p2, t2) <- infer f env b
  unify t $ TProd t1 t2
  pure (p1 <> p2, t)

infer f env (Case e ps) = do
  t <- newTyVar KStar
  (p1, te) <- infer f env e
  p2 <- for ps $ \(pat, pexp) -> do
    (as, ts) <- inferPattern env pat
    unify te ts
    let env' = SymTable $ M.fromList (as <&> \(i :>: x) -> (i, x))
                       <> unSymTable env
        pexp' = instantiate V pexp
    (p2, tp) <- infer f env' pexp'
    unify t tp
    pure p2

  pure (p1 <> join p2, t)

infer f (SymTable env) (Lam _ x) = do
  name <- newVName f
  tv <- newTyVar KStar
  let env' = SymTable $ env <> [(name, mkScheme tv)]
      e = splatter name x
  (p1, t1) <- infer f env' e
  pure (p1, TArr tv t1)

-- infer f env (Case e ps) = do
--   tvs <- for ps $ \(pat, pexp) -> do
--     tv <- newTyVar KStar
--     case pat of
--       PWildcard -> _
--     _
--   undefined
--   -- make a type var for each pattern expr
--   -- mgu them all
--   -- >> all branches return the same type

infer f env exp@(e1 :@ e2) =
  do
    tv <- newTyVar KStar
    (p1, t1) <- infer f env e1
    (p2, t2) <- infer f env e2
    unify t1 $ TArr t2 tv
    pure (p1 <> p2, tv)
  `catchE` \e -> throwE $
    mconcat
      [ e
      , "\n in "
      , show exp
      -- , "\n\ncontext: \n"
      -- , foldMap ((<> "\n") . show) . M.assocs $ unSymTable env
      ]


inferPattern :: SymTable VName -> Pat -> TI ([Assump], Type)
inferPattern _ (PLit l) = do
  pure (mempty, inferLit l)
inferPattern _ PWildcard = do
  ty <- newTyVar KStar
  pure (mempty, ty)
inferPattern _ (PVar x) = do
  ty <- newTyVar KStar
  pure (pure $ x :>: mkScheme ty, ty)
inferPattern st (PAs x p) = do
  (as, t) <- inferPattern st p
  pure (x :>: mkScheme t : as, t)
inferPattern st (PCon c ps) = do
  t <- newTyVar KStar
  (as, ts) <- first join . unzip <$> for ps (inferPattern st)
  -- this is gross! there is a bug here if the type constructor has constraints
  -- on it
  (_, ct) <- infer (error "unused") st $ V c
  unify ct $ foldr (:->) t ts
  pure (as, t)


typeInference :: ClassEnv -> Map VName Scheme -> Exp VName -> TI (Qual Type)
typeInference cenv env e = do
  (ps, t) <- infer (VName . ("!!!v" <>) . show) (SymTable env) e
  s <- view tiSubst <$> get
  zs <- traverse (discharge cenv) $ sub (flatten s) ps
  let (s', ps') = mconcat zs
      s'' = flatten $ s <> s'
      (ps'' :=> t') = sub s'' $ ps' :=> t
  errorAmbiguous $ nub ps'' :=> t'


showTrace :: Show b => b -> b
showTrace = trace =<< show


flatten :: Subst -> Subst
flatten (Subst x) = fix $ \(Subst final) ->
  Subst $ M.fromList $ M.assocs x <&> \(a, b) -> (a,) $
    sub (Subst final) $ case b of
      TVar n -> maybe (TVar n) id $ M.lookup n final
      z      -> z


generalize :: SymTable a -> Qual Type -> Scheme
generalize env t =
  Scheme (S.toList $ free t S.\\ free env) t


normalizeType :: Qual Type -> Qual Type
normalizeType = schemeType . normalize . Scheme mempty


normalize :: Scheme -> Scheme
normalize (Scheme _ body) =
    Scheme (fmap snd ord) $ normqual body
  where
    ord = zip (nub . S.toList $ free body) letters <&> \(old, l) ->
      (old, TName l $ tKind old)
    normqual (xs :=> zs) =
      fmap (\(IsInst c t) -> IsInst c $ normtype t) xs :=> normtype zs

    normtype (TCon a)    = TCon a
    normtype (a :@@ b)   = normtype a :@@ normtype b
    normtype TInt        = TInt
    normtype TBool       = TBool
    normtype TUnit       = TUnit
    normtype TVoid       = TVoid
    normtype (TVar a)    =
      case lookup a ord of
        Just x  -> TVar $ TName (unTName x) (tKind x)
        Nothing -> error "type variable not in signature"


test :: Exp VName -> IO ()
test x =
  case test' x of
    Left e  -> putStrLn e
    Right t -> putStrLn $ show t


test' :: Exp VName -> Either String (Qual Type)
test' = second normalizeType
      . runTI
      . typeInference classEnv stdLib


discharge :: ClassEnv -> Pred -> TI (Subst, [Pred])
discharge c@(ClassEnv cenv) p = do
  x <- for (S.elems cenv) $ \(a :=> b) -> do
    s <- (fmap (a,) <$> match' b p) <|> pure Nothing
    pure $ First s
  case getFirst $ mconcat x of
    Just (ps, s) ->
      fmap mconcat $ traverse (discharge c) $ sub s $ ps
    Nothing -> pure $ (mempty, pure p)


errorAmbiguous :: Qual Type -> TI (Qual Type)
errorAmbiguous (t@(a :=> b)) = do
  let amb = S.toList $ free a S.\\ free b
  when (amb /= mempty) . throwE $ mconcat
    [ "the type variable"
    , bool "" "s" $ null amb
    , " '"
    , intercalate "', '" $ fmap show amb
    , "' "
    , bool "is" "are" $ null amb
    , " ambiguous\n"
    , "in the type '"
    , show t
    , "'\n"
    ]
  pure t


-- | Unlike 'unify', the order of the paremeters here matters.
match :: Type -> Type -> TI Subst
match (l :@@ r) (l' :@@ r') = do
  sl <- match l l'
  sr <- match r r'
  pure . Subst $ unSubst sl <> unSubst sr
match (TVar u) t  = pure $ Subst [(u, t)]
match TInt TInt   = pure mempty
match TVoid TVoid = pure mempty
match TUnit TUnit = pure mempty
match (TCon tc1) (TCon tc2)
  | tc1 == tc2    = pure mempty
match t1 t2       = throwE $ mconcat
  [ "types do not match: '"
  , show t1
  , "' vs '"
  , show t2
  , "'\n"
  ]

match' :: Pred -> Pred -> TI (Maybe Subst)
match' (IsInst a b) (IsInst a' b')
  | a /= a'   = pure Nothing
  | otherwise = Just <$> match b b'


classEnv :: ClassEnv
classEnv = ClassEnv
  [ [] :=> IsInst "Eq" TInt
  , [] :=> IsInst "Eq" TUnit
  , [] :=> IsInst "Eq" TVoid
  , [IsInst "Eq" "a", IsInst "Eq" "b"] :=> IsInst "Eq" (TProd "a" "b")
  , [IsInst "Eq" "a", IsInst "Eq" "b"] :=> IsInst "Eq" (TSum "a" "b")

  , [] :=> IsInst "Category"  TArrCon
  , [] :=> IsInst "Category"  (TCon (TName "Deriv" K2))
  , [] :=> IsInst "Cartesian" TArrCon
  , [] :=> IsInst "Terminal"  TArrCon  -- const
  , [] :=> IsInst "Closed"    TArrCon
  ]


stdLib :: Map VName Scheme
stdLib = fmap (generalize $ SymTable @VName mempty) $ fmap fst stdLib'


stdLib' :: Map VName (Qual Type, Exp VName)
stdLib' =
  [ ("fst",
      ( [] :=> TProd "a" "b" :-> "a"
      , undefined
      ))
  , ("snd",
      ( [] :=> TProd "a" "b" :-> "b"
      , undefined
      ))
  , ("swap",
      ( [] :=> TProd "a" "b" :-> TProd "b" "a"
      , lam "z" $ LProd ("snd" :@ "z") ("fst" :@ "z")
      ))
  , ("shouldInline",
      ( [IsInst "ToInline" "a"] :=> "a" :-> "a"
      , "id"
      ))
  , ("inl",
      ( [] :=> "a" :-> TSum "a" "b"
      , lam "x" $ LInj False "x"
      ))
  , ("inr",
      ( [] :=> "b" :-> TSum "a" "b"
      , lam "x" $ LInj True "x"
      ))
  , ("proj",
      ( []
          :=> ("a" :-> "c")
          :-> ("b" :-> "c")
          :-> TSum "a" "b"
          :-> "c"
      , undefined
      ))
  , ("fromLeft",
      ( [] :=> TSum "a" "b" :-> "a"
      , undefined
      ))
  , (".",
      ( [CCat "k"]
          :=> TCat "k" "b" "c"
          :-> TCat "k" "a" "b"
          :-> TCat "k" "a" "c"
      , lam "g" . lam "f" . lam "x" $ "g" :@ ("f" :@ "x")
      ))
  , ("apply",
      ( [CCat "k"]
          :=> (TCat "k" (TProd ("a" :-> "b") "a") "b")
      , undefined
      ))
  , ("curry",
      ( [CCat "k"]
          :=> TCat "k" (TProd "a" "b") "c"
          :-> TCat "k" "a" ("b" :-> "c")
      , undefined
      ))
  , ("fork",
      ( [CCat "k"]
          :=> TCat "k" "a" "c"
          :-> TCat "k" "a" "d"
          :-> TCat "k" "a" (TProd "c" "d")
      , undefined
      ))
  , ("unit",
      ( [] :=> TUnit
      , LUnit
      ))
  , ("==",
      ( [IsInst "Eq" "a"] :=> "a" :-> "a" :-> TBool
      , undefined
      ))
  , (",",
      ( [] :=> "a" :-> "b" :-> TProd "a" "b"
      , lam "a" $ lam "b" $ LProd "a" "b"
      ))
  , ("bool",
      ( [] :=> "a" :-> "a" :-> TBool :-> "a"
      , undefined
      ))
  , ("id",
      ( [CCat "k"] :=> TCat "k" "a" "a"
      , lam "x" "x"
      ))
  , ("const",
      ( [CCat "k"]
          :=> "b"
          :-> TCat "k" "a" "b"
      , lam "x" "x"
      ))
  , ("ccc",
      ( [CCat "k"]
          :=> ("a" :-> "b") :-> TSum (TCat "k" "a" "b") TUnit
      , undefined
      ))
  , ("undefined",
      ( [] :=> "a"
      , undefined
      ))
  , ("getDerivation",
      ( [] :=> TCon (TName "Deriv" K2) :@@ "a" :@@ "b"
           :-> "a"
           :-> "b"
      , undefined
      ))
  ]

