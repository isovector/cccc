{-# LANGUAGE OverloadedLists            #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -Wall                   #-}

module TypeChecking where

import           Bound hiding (instantiate)
import           Bound.Scope hiding (instantiate)
import           Control.Arrow (first, second)
import           Control.Lens ((<&>))
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Bool (bool)
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid ((<>))
import qualified Data.Set as S
import           Prelude hiding (exp)
import           Types


type TI = ExceptT String (State (Int, Int))


newVName :: (Int -> a) -> TI a
newVName f = do
  n <- snd <$> get
  modify $ second (+1)
  pure $ f n


letters :: [String]
letters = do
  b <- "":letters
  a <- ['a'..'z']
  pure $ a : b


runTI :: TI a -> Either String a
runTI = flip evalState (0, 0) . runExceptT


newTyVar :: TI Type
newTyVar = do
  n <- fst <$> get
  modify $ first (+1)
  pure . TVar . TName $ letters !! n


instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- traverse (const newTyVar) vars
  pure $ apply (Subst $ M.fromList (zip vars nvars)) t


unify :: Type -> Type -> TI Subst
unify (l :@@ r) (l' :@@ r') = do
  s1 <- unify l l'
  s2 <- unify (apply s1 r) (apply s1 r')
  pure $ s1 <> s2
unify (TCon a) (TCon b)
  | a == b  = pure mempty
unify (TVar u) t  = varBind u t
unify t (TVar u)  = varBind u t
unify TInt TInt   = pure mempty
unify t1 t2       = throwE $
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
  | otherwise = pure $ Subst [(u, t)]


splatter :: Monad f => c -> Scope b f c -> f c
splatter = splat pure . const . pure


infer
    :: (Int -> VName)
    -> SymTable VName
    -> Exp VName
    -> TI (Subst, Type)
infer f env (Assert e t) = do
  (s1, t1) <- infer f env e
  s2       <- unify t t1
  pure (s1 <> s2, t)
infer _ (SymTable env) (V a) =
  case M.lookup a env of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> (,) <$> pure mempty <*> instantiate sigma
infer f env (Let bs b) = do
  name <- newVName f
  let e1 = splatter name bs
      e2 = splatter name b
  (s1, t1) <- infer f env e1
  let t' = generalize (apply s1 env) t1
      env' = SymTable $ M.insert name t' $ unSymTable env
  (s2, t2) <- infer f (apply s1 env') e2
  pure (s1 <> s2, t2)
infer _ _ (LInt _)  = pure (mempty, TInt)
infer _ _ (LBool _) = pure (mempty, TBool)
infer _ _ (LUnit)   = pure (mempty, TUnit)
infer f env (LInj which a) = do
  t <- newTyVar
  (s1, t1) <- infer f env a
  t2 <- newTyVar
  s2 <- unify t . apply s1 $ bool id flip which TProd t1 t2
  pure (s1 <> s2 , t)
infer f env (LProd a b) = do
  t <- newTyVar
  (s1, t1) <- infer f env a
  -- TODO(sandy): maybe too many applys? it seems to work without
  (s2, t2) <- infer f (apply s1 env) b
  s3 <- unify t . apply (s1 <> s2) $ TProd t1 t2
  pure (s1 <> s2 <> s3, t)

infer f (SymTable env) (Lam x) = do
  name <- newVName f
  tv <- newTyVar
  let env' = SymTable $ env <> [(name, Scheme [] tv)]
      e = splatter name x
  (s1, t1) <- infer f env' e
  pure (s1, TArr (apply s1 tv) t1)

infer f env exp@(e1 :@ e2) =
  do
    tv <- newTyVar
    (s1, t1) <- infer f env e1
    (s2, t2) <- infer f (apply s1 env) e2
    s3 <- unify (apply s2 t1) (TArr t2 tv)
    pure (s1 <> s2 <> s3, apply s3 tv)
  `catchE` \e -> throwE $
    mconcat
      [ e
      , "\n in "
      , show exp
      , "\n\ncontext: \n"
      , foldMap ((<> "\n") . show) . M.assocs $ unSymTable env
      ]


typeInference :: Map VName Scheme -> Exp VName -> TI Type
typeInference env e = do
  (s, t) <- infer (VName . ("!!!v" <>) . show) (SymTable env) e
  pure $ apply s t


flatten :: Subst -> Subst
flatten (Subst x) = fix $ \(Subst final) ->
  Subst $ M.fromList $ M.assocs x <&> \(a, b) -> (a,) $
    apply (Subst final) $ case b of
      TVar n -> maybe (TVar n) id $ M.lookup n final
      z      -> z


generalize :: SymTable a -> Type -> Scheme
generalize env t =
  Scheme (S.toList $ free t S.\\ free env) t


normalizeType :: Type -> Type
normalizeType = schemeType . normalize . Scheme mempty


normalize :: Scheme -> Scheme
normalize (Scheme _ body) = Scheme (map snd ord) (normtype body)
  where
    ord = zip (nub $ S.toList $ free body) (fmap TName letters)

    normtype (TCon a)    = TCon a
    normtype (a :@@ b)   = normtype a :@@ normtype b
    normtype TInt        = TInt
    normtype TBool       = TBool
    normtype TUnit       = TUnit
    normtype TVoid       = TVoid
    normtype (TVar a)    =
      case Prelude.lookup a ord of
        Just x -> TVar x
        Nothing -> error "type variable not in signature"


test :: Exp VName -> IO ()
test x =
  case runTI $ typeInference stdLib x of
    Left e -> putStrLn e
    Right t -> putStrLn $ show $ normalizeType t


stdLib :: Map VName Scheme
stdLib = fmap (generalize $ SymTable @VName mempty) $ fmap fst stdLib'


stdLib' :: Map VName (Type, Exp VName)
stdLib' =
  [ ("fst",
      ( TProd "a" "b" :-> "a"
      , undefined
      ))
  , ("snd",
      ( TProd "a" "b" :-> "b"
      , undefined
      ))
  , ("inl",
      ( "a" :-> TSum "a" "b"
      , lam "x" $ LInj False "x"
      ))
  , ("inr",
      ( "b" :-> TSum "a" "b"
      , lam "x" $ LInj True "x"
      ))
  , ("proj",
      ( ("a" :-> "c") :-> ("b" :-> "c") :-> TSum "a" "b" :-> "c"
      , undefined
      ))
  , (".",
      ( ("b" :-> "c") :-> ("a" :-> "b") :-> "a" :-> "c"
      , lam "g" . lam "f" . lam "x" $ "g" :@ ("f" :@ "x")
      ))
  , ("unit",
      ( TUnit
      , LUnit
      ))
  , ("==",
      ( "a" :-> "a" :-> TBool
      , undefined
      ))
  , (",",
      ( "a" :-> "b" :-> TProd "a" "b"
      , lam "a" $ lam "b" $ LProd "a" "b"
      ))
  , ("bool",
      ( "a" :-> "a" :-> TBool :-> "a"
      , undefined
      ))
  , ("id",
      ( "a" :-> "a"
      , lam "x" "x"
      ))
  , ("ccc",
      ( ("a" :-> "b") :-> "k" :@@ "a" :@@ "b"
      , undefined
      ))
  ]

