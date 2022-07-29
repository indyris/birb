# Birb - a little build tool written in idris

One nice thing about make is that it has natural support for
rebuilding dependencies, but this gets in the way sometimes.

Sometimes we want to declare things forwards as well.

If we know we want to compile a bunch of c files in parallel, it's
convenient to be able to just search for all c files in a directory
and run the compiler.


```idris

cToO : Path -> Path
cToO = replaceExt "o" .
       child (MkPath "build") .
       relativeTo (MkPath "src")

release = do
c <- glob "src/**.c" -- returns a list of all files matching *.c
  let o = map cToO c   -- figure out where the output should go
  let cc = zipWithM compileC

compileC : Path -> Path -> IO Rules
compileC (MkPath src) (MkPath dest) = do
  interruptibleCommand ["gcc", src, "-o", dest]
```
