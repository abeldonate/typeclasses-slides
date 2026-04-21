import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Typeclasses Chapter 2" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Different Scenarios

The idea behind this choice is:

- Choose `class` when you expect inference to fill it in automatically, especially if many definitions and theorems should work uniformly once an instance is available.
- Choose `Prop` when the fact is local, passed explicitly, or when multiple distinct witnesses should remain visible and not be merged by typeclass search.



# Different Scenarios

We see the difference in the syntax here:
```lean
class MyClass (α : Type u) where
  field1 : α → α
  field2 : α
  myaxiom : ∀ x, field1 (field1 x) = field1 x

def MyProp (α : Type u) : Prop :=
  ∃ (field1 : α → α) (field2 : α),
    ∀ x, field1 (field1 x) = field1 x
```


# Different Scenarios

In practice:
- A class is resolved by typeclass search `[MyClass α]` and is convenient when you want implicit arguments.
- A proposition is provided directly as a term `(h : MyProp α)` and is convenient when assumptions are explicit and local.


# Algebraic structures

They are organized in hierarchies (`Semigroup`, `Monoid`, `Group`, `Ring`, ...) and are always encoded as classes.

Two major benefits:

- Inheritance: a `Ring` instance can extend many parent structures.
- Inference: once `[Ring α]` is available, notation and lemmas that require additive or multiplicative structure work immediately.

# Algebraic structures

![Hierarchy of algebraic structures](figures/HierarchyAlgebra.png)

# Instance inference

```lean
example : AddGroup ℤ := by infer_instance
-- How is this istance found?
```

```lean
-- In mathlib:
instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x := show (n + 1 : ℤ) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by simp only [Int.natCast_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [Int.negSucc_eq, Int.natCast_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
```

# Instance inference

```lean
instance instAddCommMonoid    : AddCommMonoid ℤ    := by infer_instance
instance instAddMonoid        : AddMonoid ℤ        := by infer_instance
instance instMonoid           : Monoid ℤ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℤ    := by infer_instance
instance instSemigroup        : Semigroup ℤ        := by infer_instance
instance instAddGroup         : AddGroup ℤ         := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℤ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℤ     := by infer_instance
```


# Proposition / Class

For this section, we build two definitions of monoid structure and compare them:

- `MonoidP` as an explicit proposition. Tells you about existence of data.
- `MonoidC` as a class carrying operations and laws. Tells you about the data itself.


# `MonoidP` / `MonoidC`

```lean
def MonoidP (α : Type u) : Prop :=
  ∃ (mul : α → α → α) (one : α),
    (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧
    (∀ a, mul one a = a) ∧
    (∀ a, mul a one = a)

class MonoidC (α : Type u) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
```

# `MonoidP` (Proposition)

```lean
theorem prodMonoidP (α β : Type u) (hα : MonoidP α) (hβ : MonoidP β) :
    MonoidP (α × β) := by
  rcases hα with ⟨mulα, oneα, hassocα, hone_mulα, hmul_oneα⟩
  rcases hβ with ⟨mulβ, oneβ, hassocβ, hone_mulβ, hmul_oneβ⟩
  refine ⟨
    (fun x y => (mulα x.1 y.1, mulβ x.2 y.2)),
    (oneα, oneβ),
    ?_, ?_, ?_⟩
  · intro a b c
    ext <;> simp [hassocα, hassocβ]
  · intro a
    ext <;> simp [hone_mulα, hone_mulβ]
  · intro a
    ext <;> simp [hmul_oneα, hmul_oneβ]
```
# `MonoidC` (Class)

```lean
instance prodMonoidC (α β : Type u) [MonoidC α] [MonoidC β] :
    MonoidC (α × β) where
  mul x y := (MonoidC.mul x.1 y.1, MonoidC.mul x.2 y.2)
  one := (MonoidC.one, MonoidC.one)
  mul_assoc a b c := by
    ext <;> simp [MonoidC.mul_assoc]
  one_mul a := by
    ext <;> simp [MonoidC.one_mul]
  mul_one a := by
    ext <;> simp [MonoidC.mul_one]
```

# MonoidP / MonoidC

But there is a key difference in how these are used:
```lean
example (α β : Type u) (hα : MonoidP α) (hβ : MonoidP β) :
    MonoidP (α × β) := by
  exact prodMonoidP α β hα hβ

example (α β : Type u) [MonoidC α] [MonoidC β] :
    MonoidC (α × β) := by
  infer_instance

-- If we want a more elaborate example
example (α β γ : Type u) [MonoidC α] [MonoidC β] [MonoidC γ] :
    MonoidC ((α × β) × γ) := by
  infer_instance
```


# Different Scenarios

Rule of thumb:

- Use a proposition (`MonoidP`) for local assumptions.
- Use a class (`MonoidC`) for reusable inferred structure.


# More Typeclasses

- From relations
  - Preorder, PartialOrder, LinearOrder, Lattice
- From category
  - Category, Functor, NaturalTransformation, Mono, Epi, Iso
- From sets
  - Subset, Disjoint, Finite, Infinite
- From other structures
  - Topological spaces, Metric spaces, Measurable spaces, etc.
