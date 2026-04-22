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

# Tabled Typeclass Resolution

```lean
example : AddCommGroup (ℤ × ℤ) := by
    infer_instance











```

# Example: Tabled Typeclass Resolution

::: stretch
![Hierarchy of algebraic structures](figures/HierarchyAlgebra.png)
:::

Goal: Synth (A0 ?α)
- Try A3 --> A2$. New Goal: Synth (A2 ?α). Table it.
- Try A2 --> A1$. New Goal: Synth (A1 ?α). Table it.
- Try A1 --> A0$. Success! Result cached in Table.
- Try A3 --> B2 --> A2$.

# Code for the example

```lean
class A0 (α : Type)

class A1 (α : Type) extends A0 α
class B1 (α : Type) extends A0 α

class A2 (α : Type) extends A1 α, B1 α
class B2 (α : Type) extends A1 α, B1 α

class A3 (α : Type) extends A2 α, B2 α
class B3 (α : Type) extends A2 α, B2 α

set_option trace.Meta.synthInstance true
variable {α : Type} [A3 α]
example : A0 α := by infer_instance
```
