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
import           Control.Lens ((<&>), view, (%~), (<>~))
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Bifunctor
import           Data.Bool (bool)
import           Data.Foldable (for_)
import           Data.List (nub, intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>), First (..))
import qualified Data.Set as S
import           Data.Traversable (for)
import           Prelude hiding (exp)
import           Types
import           Utils


type Placeholder = Reader (Pred -> Exp VName)


unify :: Type -> Type -> TI ()
unify t1 t2 = do
  s  <- view tiSubst <$> get
  s' <- mgu (sub s t1) (sub s t2)
  modify $ tiSubst <>~ s'
  pure ()


newVName :: String -> TI VName
newVName f = do
  n <- view tiVNames <$> get
  modify $ tiVNames %~ (+1)
  pure $ VName $ f <> show n


newTyVar :: Kind -> TI Type
newTyVar k = do
  n <- view tiTNames <$> get
  modify $ tiTNames %~ (+1)
  pure . TVar . flip TFreshName k $ letters !! n


freshInst
    :: VName
    -> Scheme
    -> TI (Qual Type, Placeholder (Exp VName))
freshInst n (Scheme vars t) = do
  nvars <- traverse newTyVar $ fmap tKind vars
  let subst = Subst $ M.fromList (zip vars nvars)
      t'@(qs :=> _) = sub subst t
  pure (t', liftPlaceholders n qs)


liftPlaceholders
    :: VName
    -> [Pred]
    -> Placeholder (Exp VName)
liftPlaceholders name ps = do
  f <- ask
  let dicts = fmap f ps
  pure $ case length dicts of
    0 -> V name
    _ -> foldl (:@) (V $ VName $ "@" <> unVName name) dicts


mgu :: Type -> Type -> TI Subst
mgu (l :@@ r) (l' :@@ r') = do
  s1 <- mgu l l'
  s2 <- mgu (sub s1 r) (sub s1 r')
  pure $ s1 <> s2
mgu (TCon a) (TCon b)
  | a == b  = pure mempty
mgu (TVar u) t  = varBind u t
mgu t (TVar u)  = varBind u t
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
inferLit (LitInt _)      = TInt
inferLit (LitString _)   = TString
inferLit (LitNative _ t) = t


infer
    :: SymTable VName
    -> Exp VName
    -> TI ([Pred], Type, Placeholder (Exp VName))
infer env (Assert e t) = do
  (p1, t1, h1) <- infer env e
  unify t t1
  s <- view tiSubst <$> get
  pure (sub s p1, t, Assert <$> h1 <*> pure t)

infer (SymTable env) (V a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> do
      (ps :=> x, h) <- freshInst a sigma
      pure (ps, x, h)

infer (SymTable env) z@(LCon a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> do
      (ps :=> x, _) <- freshInst a sigma
      pure (ps, x, pure z)

infer env (Let n e1 b) = do
  name <- newVName "v"
  let e2 = splatter name b
  (p1, t1, h1) <- infer env e1
  let t'   = generalize env $ p1 :=> t1
      env' = SymTable $ M.insert name t' $ unSymTable env
  (p2, t2, h2) <- infer env' e2
  pure (p2, t2, let_ <$> pure n <*> h1 <*> h2)
infer _ h@(Lit l) = pure (mempty, inferLit l, pure h)

infer env (Case e ps) = do
  t <- newTyVar KStar
  (p1, te, h1) <- infer env e
  (p2, tps, h2) <- fmap unzip3 $ for ps $ \(pat, pexp) -> do
    (as, ts) <- inferPattern env pat
    unify te ts
    let env' = SymTable $ M.fromList (as <&> \(i :>: x) -> (i, x))
                       <> unSymTable env
        pexp' = instantiate V pexp
    (p2, tp, h2) <- infer env' pexp'
    unify t tp
    pure (p2, tp, (,) <$> pure pat <*> h2)

  for_ (zip tps $ tail tps) $ uncurry $ flip unify

  pure (p1 <> join p2, t, case_ <$> h1 <*> sequence h2)

infer (SymTable env) (Lam name x) = do
  tv <- newTyVar KStar
  let env' = SymTable $ env <> [(name, mkScheme tv)]
      e = splatter name x
  (p1, t1, h1) <- infer env' e
  pure (p1, TArr tv t1, lam <$> pure name <*> h1)

infer env exp@(e1 :@ e2) =
  do
    tv <- newTyVar KStar
    (p1, t1, h1) <- infer env e1
    (p2, t2, h2) <- infer env e2
    unify t1 $ TArr t2 tv
    pure (p1 <> p2, tv, (:@) <$> h1 <*> h2)
  `catchE` \e -> throwE $
    mconcat
      [ e
      , "\n in "
      , show exp
      -- , "\n\ncontext: \n"
      -- , foldMap ((<> "\n") . show) . M.assocs $ unSymTable env
      ]


inferPattern :: SymTable VName -> Pat -> TI ([Assump Scheme], Type)
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
  (_, ct, _) <- infer st $ V c
  unify ct $ foldr (:->) t ts
  pure (as, t)


typeInference
    :: ClassEnv
    -> SymTable VName
    -> Exp VName
    -> TI ((Qual Type, Type), Exp VName)
typeInference cenv sym e = do
  (ps, t, h) <- infer sym e
  s <- view tiSubst <$> get
  zs <- traverse (discharge cenv) $ sub (flatten s) ps
  let (s', ps', m, as, _) = mconcat zs
      s'' = flatten $ s <> s'
      (ps'' :=> t') = sub s'' $ ps' :=> t
      t'' = nub ps'' :=> t'
      m'  = M.mapKeys (sub s'') m
      h'  = runReader h $ (M.!) m' . sub s''
      e'  = foldr lam h' $ fmap assumpName as
      te' = foldr (:->) (unqualType t'') $ fmap assumpVal as
  _ <- errorAmbiguous t''
  pure ((t'', te'), e')
  `catchE` \err -> throwE $
    mconcat
      [ err
      , "\n in "
      , show e
      ]


flatten :: Subst -> Subst
flatten (Subst x) = fix $ \(Subst final) ->
  Subst $ M.fromList $ M.assocs x <&> \(a, b) -> (a,) $
    sub (Subst final) $ case b of
      TVar n -> maybe (TVar n) id $ M.lookup n final
      z      -> z


generalize :: SymTable a -> Qual Type -> Scheme
generalize env t =
  Scheme (S.toList $ free t S.\\ free env) t


discharge
    :: ClassEnv
    -> Pred
    -> TI ( Subst
          , [Pred]
          , Map Pred (Exp VName)
          , [Assump Type]
          , [Exp VName]
          )
discharge cenv p = do
  x <- for (getQuals cenv) $ \(a :=> b) -> do
    s <- (fmap (a, b,) <$> match' b p) <|> pure Nothing
    pure $ First s
  case getFirst $ mconcat x of
    Just (ps, b, s) -> do
      (s', ps', mp, as, ds) <- fmap mconcat
                         . traverse (discharge cenv)
                         $ sub s ps
      let d = V . VName $ getDict b
          e = foldl (:@) d ds
      pure $ (s', ps', mp <> M.singleton p e, as, pure e)
    Nothing -> do
      param <- newVName "d"
      pure ( mempty
           , pure p
           , M.singleton p $ V param
           , pure $ param :>: getDictTypeForPred p
           , pure $ V param
           )
  `catchE` \e -> throwE $
    mconcat
      [ e
      , "\n when discharging "
      , show p
      ]


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

