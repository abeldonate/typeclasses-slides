import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Tabled Typeclass Resolution" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Tabled Typeclass Resolution

```lean
set_option trace.Meta.synthInstance true

example : Add (ℤ × ℤ) := by
    infer_instance













```


```lean
example : AddCommGroup (ℤ × ℤ) := by
    infer_instance











```
