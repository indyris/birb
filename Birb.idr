module Birb

-- import Data.List

-- data Pid = MkPid Int

-- ------------- standard library

-- data ConflictStrategy = Replace | Wait | Ignore

-- -- data Command 


-- ModTime : Type

-- data Path = MkPath String

-- child : Path -> Path -> Path

-- sibling : Path -> Path -> Path

-- relativeTo : Path -> Path -> Path

-- replaceExt : String -> Path -> Path

-- modTime : Path -> Build (Maybe ModTime)

-- glob : String -> Build (List Path)

-- -- isNewer : Path -> ModTime -> Build Bool
-- -- isNewer p t = 


-- --------- below this is example user code



-- -- ex1:

-- cToO : Path -> Path
-- cToO = replaceExt "o" . child (MkPath "build") . relativeTo (MkPath "src")

-- CompileC : Type

-- data PathCheckSum : (p : Path) -> Type where
--   FileCheckSum : String -> PathCheckSum p
--   DirCheckSum : List (p : Path ** PathCheckSum p) -> PathCheckSum p

-- -- checksums a bunch of files
-- checksums : List Path -> IO (List (p : Path ** PathCheckSum p))

-- -- verifies a bunch of checksums
-- verifyChecksums : List (Path, String) -> IO (Either (List (p : Path ** PathCheckSum p)) ())

-- -- creates a scratch directory somewhere, returns the path
-- mkBuildDir : IO Path

-- compileC : Path -> Path -> IO ()

-- -- interface Target (t : Type) where
  
-- record Builder where
  


-- -- record Facts where
-- --   constructor MkFacts
  

-- -- data Output : Type where
-- --   FileOutput : Path

-- release = do
--   c <- glob "src/**.c"
--   let o = map cToO c
--   let targets = zipWith compileCTarget c o
--   pure ()
  -- parallel (runCommand compileC)

-- rebuildIfOlder : List Path -> Path

-- compileC c = do
--   let o = cToO c
--   case compare (modTime c) (modTime o) do
--     LT -> cmd ["gcc", show c, "-o", show (cToO c)]
--     RT -> 

-- data CTarget
 
-- interface Emits (emitter : Type) (msg : Type) wheer

-- interface React m reactor msg where
--   react : reactor -> msg -> m reactor

-- plug : (emitter : Type)
--     -> (msg : Type)
--     -> (reactor : Type)
--     -> Emits emitter msg
--     => Reacts m reactor msg
--     => 

-- interface Lifecycle l where
  
--   close : 1 l ->


-- data ConduitT : (i : Type) -> (o : Type) -> (m : Type) -> (r : Type) -> Type where

-- data Iib : (r : Type) -> Type where
--   MkIib : IO r -> Iib r

-- interface Conduit r where

-- runIib : IO ()



-- dev = do
--   restartable $ \_ => restartableCommand "make" watch src ["*.idr"] <@> 
--   > make
    
    
  
