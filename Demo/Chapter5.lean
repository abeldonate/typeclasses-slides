import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Cycle Problem" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# The Cycle Problem

- The cycle problem appears when instance search comes back to a goal
  it is already trying to solve.
- With naive DFS, this can cause non-termination: the
  resolver keeps unfolding one goal into subgoals that eventually
  recreate the original goal.

# Example 1: coercion transitivity

```lean
class MyCoeT (α β : Type) where
  coe : α → β

-- Natural transitivity rule.
def coeTransRule {α β γ : Type} [ab : MyCoeT α β] [bg : MyCoeT β γ] :
    MyCoeT α γ where
  coe x := bg.coe (ab.coe x)
```

# Example 1: coercion transitivity

`MyCoeT α β`
- Choose `coeTransRule` with a fresh middle type `?m₁`
- New subgoals: `MyCoeT α ?m₁` and `MyCoeT ?m₁ β`
- Again choose `coeTransRule` for `MyCoeT α ?m₁` -> `?m₂`
- New subgoals: `MyCoeT α ?m₂` and `MyCoeT ?m₂ ?m₁`
- Again choose `coeTransRule` for `MyCoeT α ?m₂` -> `?m₃`
- ...

# Example 1: coercion transitivity

:::stretch
![Trivial loop in coercion transitivity](../figures/CoeTransitive.svg)
:::

# Example 2: ring/algebra loop

```lean
-- Toy classes for a cyclic search pattern.
class ToyRing (A : Type) where
  mul_assoc : ∀ _ _ _ : A, True
class ToyAlgebra (R A : Type) where
  compat : ∀ _ : R, ∀ _ : A, True
```

# Example 2: ring/algebra loop

```lean
-- Rule 1: an algebra over itself gives a ring structure.
def ringFromAlgebraRule
    (A : Type) [ToyAlgebra A A] :
    ToyRing A :=
  { mul_assoc := by
      intro _ _ _
      trivial }

-- Rule 2: every ring is an algebra over itself.
def algebraFromRingRule
    (A : Type) [ToyRing A] :
    ToyAlgebra A A :=
  { compat := by
      intro _ _
      trivial }
```

# Example 2: ring/algebra loop

- Searching for `[ToyRing A]` may choose `ringFromAlgebraRule`,
- which asks for `[ToyAlgebra A A]`.
- Then search for `[ToyAlgebra A A]` may choose `algebraFromRingRule`,
- which asks again for `[ToyRing A]`.
- This recreates the original goal and forms a cycle.

In both examples, tabling breaks the loop by remembering subgoals and
reusing in-progress/known results instead of expanding forever.
