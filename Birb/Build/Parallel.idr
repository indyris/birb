module Birb.Build.Parallel

import Control.App
import Data.Fin

data Parallel : Type

public export
Uninhabited Parallel where
  uninhabited _ impossible

export
data Threads : (n : Nat) -> Type where
  MkThreads : Threads n

--- Parallelism manages 
export
interface Parallelism e where
  threadCount : App e Nat
  getThread : App {l} e (Threads 1)
  getThreads : (n : Nat) -> App {l} e (f : Fin (S n) ** Threads (finToNat f))
  allThreads : App {l} e (n : Nat ** Maybe (Threads n))
  returnThreads : {n : Nat} -> (1 t : Threads n) -> App {l} e ()

-- interface Process p where

-- interface FileInfo i where

-- export
-- runParallel : Nat -> Has [Parallelism] e => App e ()

