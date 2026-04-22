import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Chapter 3: Forgetful Inheritance" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Forgetful Inheritance

In this running example, every `Group α` should also be usable as a `Monoid α`.

```lean
/- !hide -/
namespace MyAlgebra2
/- !end hide -/
class Monoid (α : Type u) where
  mul : α → α → α
  one : α
  -- axioms omitted

class Group (α : Type u) extends Monoid α where
  inv : α → α
  -- axioms omitted
/- !hide -/
end MyAlgebra2
/- !end hide -/
```

# Forgetful Inheritance

::: fragment
1. `Group α` contains strictly more structure than `Monoid α`.
:::
::: fragment
2. Instance search can forget the extra part (`inv`) when only monoid data is needed.
:::
::: fragment
3. This keeps hierarchies modular while avoiding duplicate instance declarations.
:::
