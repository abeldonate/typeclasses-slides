import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Diamond Problem" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Diamond Problem

:::stretch
![Hierarchy tree of some algebraic structures](../figures/HierarchyAlgebra.png)
:::

# A simple diamond hierarchy

:::stretch
![A simple diamond hierarchy](../figures/SingleDiamond.svg)
:::

# A simple diamond hierarchy

```lean
-- !fragment
class Base where
  base : String

class LeftBranch extends Base where
  left : String

class RightBranch extends Base where
  right : String

class Diamond extends LeftBranch, RightBranch

-- !fragment
example : Diamond :=
  { base := "base",
    left := "left",
    right := "right"}
```

# Why is this a problem

When we query for a `Diamond` instance, the resolver must:
1. Find a `LeftBranch` instance (which requires `Base`)
2. Find a `RightBranch` instance (which requires `Base`)
3. The `Base` instance is now required from *two different paths*

Tower of diamonds --> explodes exponentially.


# Real case in mathlib

From `[CommGroup α]`, Lean can obtain `[Monoid α]` by two routes:

- `CommGroup α -> Group α  -> DivInvMonoid α -> Monoid α`
- `CommGroup α -> CommMonoid α -> Monoid α`


# Real case in mathlib

:::stretch
![Hierarchy tree of some algebraic structures](../figures/AlgebraDiamond.svg)
:::


# Real case in mathlib

```lean
  /- !hide -/
namespace MyAlgebra
  /- !end hide -/
class CommGroup (G : Type u) extends Group G, CommMonoid G

class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  -- more stuff
  /- !hide -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  protected zpow : ℤ → G → G := zpowRec npowRec
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by intros; rfl
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl
  /- !end hide -/
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  protected npow : ℕ → M → M := npowRecAuto
  -- more stuff
  /- !hide -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl
  /- !end hide -/
  /- !hide -/
end MyAlgebra
  /- !end hide -/
```


# Problems caused by some diamonds: DefEq issues

:::stretch
![Hierarchy tree of some algebraic structures](../figures/TopDiamond.svg)
:::
