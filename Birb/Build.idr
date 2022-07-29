module Birb.Build

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

data BuildRes : Type -> Type where
  MkBuildRes : (result : a) -> (1 x : %World) -> BuildRes a

data OneOf : List Type -> Type where
   First : e -> OneOf (e :: es)
   Later : OneOf es -> OneOf (e :: es)

Uninhabited (OneOf []) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

0 execTy : List Type -> Type -> Type
execTy es ty = Either (OneOf es) ty

export
data Build : (e : List Type) -> (t : Type) -> Type where
  MkBuild : (1 prog : (1 w : %World) -> BuildRes (execTy e t)) -> Build e t

pureBuild : a -> Build e a
pureBuild v = MkBuild $ MkBuildRes (Right v)

bindBuild : Build e a -> (a -> Build e b) -> Build e b
bindBuild (MkBuild prog) next =
  MkBuild $ \world =>
    let MkBuildRes x' world' = prog world in
    case x' of
      Right res => let MkBuild r = next res in r world'
      Left err  => MkBuildRes (Left err) world'

export
Functor (Build es) where
  map f b = bindBuild b $ \b' => pureBuild (f b')

export
Applicative (Build es) where
  pure = pureBuild
  (<*>) f b = bindBuild f $ \f' => bindBuild b $ \b' => pure (f' b')

export
Monad (Build es) where
  (>>=) = bindBuild

export
(>>=) : Build e a -> (a -> Build e b) -> Build e b
(>>=) = bindBuild

PrimBuild : Type -> Type
PrimBuild a = (1 x : %World) -> BuildRes a

prim_build_pure : a -> PrimBuild a
prim_build_pure = MkBuildRes

prim_build_bind : (1 act : PrimBuild a) -> (1 k : a -> PrimBuild b) -> PrimBuild b
prim_build_bind fn k w = let MkBuildRes x' w' = fn w in k x' w'

toPrimBuild : (1 act : IO a) -> PrimBuild a
toPrimBuild x w = let MkIORes r w = toPrim x w in MkBuildRes r w

public export
data BuildIO : Type where

public export
Uninhabited BuildIO where
  uninhabited _ impossible

public export
Init : List Type
Init = [BuildIO]

export
runBuild : Build Init a -> IO a
runBuild (MkBuild prog) = primIO $ \w =>
 case (prim_build_bind prog $ \r =>
        case r of
          Right res => MkBuildRes res
          Left (First err) => absurd err) w of
  MkBuildRes r w => MkIORes r w
