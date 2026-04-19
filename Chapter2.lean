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

# Different Scenarios

```lean
set_option trace.Meta.synthInstance true

class Group2 (α : Type u) extends Monoid α where
  inv : α → α
  -- axioms omitted

example : AddGroup ℤ := by infer_instance

-- How is this istance found? In the mathlib:
instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (· * ·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = n * x + x by rw [Int.add_mul, Int.one_mul]
  zsmul := (· * ·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [Int.natCast_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [Int.negSucc_eq, Int.natCast_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg


instance instAddCommMonoid    : AddCommMonoid ℤ    := by infer_instance
instance instAddMonoid        : AddMonoid ℤ        := by infer_instance
instance instMonoid           : Monoid ℤ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℤ    := by infer_instance
instance instSemigroup        : Semigroup ℤ        := by infer_instance
instance instAddGroup         : AddGroup ℤ         := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℤ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℤ     := by infer_instance
```


# Injective (Prop) / Mono (Class)

In mathlib, the class-oriented name is usually `Mono`
(in category theory), not `Injective`.

For this section, we build two definitions of Mono an compare them:

- `MonoP` as an explicit proposition.
- `MonoC` as a class carrying the same cancellation law.


# Injective (Prop) / Mono (Class)
```lean
variable {α β γ δ : Type u}

def MonoP (f : α → β) : Prop :=
  ∀ ⦃x y : α⦄, f x = f y → x = y

class MonoC (f : α → β) where
  cancel : ∀ ⦃x y : α⦄, f x = f y → x = y
```

# Injective (Prop)

```lean
theorem compositionP
    (f : α → β) (g : β → γ) (h₁ : MonoP f) (h₂ : MonoP g) :
    MonoP (g ∘ f) := by
  intro x y h
  apply h₁
  apply h₂
  simpa [Function.comp] using h
```
# Mono (Class)

```lean
instance monoComp
    (f : α → β) (g : β → γ)
    [MonoC f] [MonoC g] :
    MonoC (g ∘ f) where
  cancel := by
    intro x y h
    apply MonoC.cancel (f := f)
    apply MonoC.cancel (f := g)
    simpa [Function.comp] using h
```

# Injective (Prop) / Mono (Class)

But there is a key difference in how these are used:
```lean
example (f : α → β) (g : β → γ) (h₁ : MonoP f) (h₂ : MonoP g) :
    MonoP (g ∘ f) := by
  apply compositionP f g h₁ h₂

example (f : α → β) (g : β → γ) [MonoC f] [MonoC g] :
    MonoC (g ∘ f) := by
  infer_instance

-- If we want a more elaborate example
example (f : α → β) (g : β → γ) (h : γ → δ) [MonoC f] [MonoC g] [MonoC h] :
    MonoC (h ∘ g ∘ f) := by
  infer_instance
```


# Different Scenarios

Rule of thumb:

- Use a proposition (`MonoP`) for local assumptions.
- Use a class (`MonoC`) for reusable inferred structure.


# More Typeclasses

- From relations
  - Preorder, PartialOrder, LinearOrder, Lattice
- From category
  - Category, Functor, NaturalTransformation, Mono, Epi, Iso
- From sets
  - Subset, Disjoint, Finite, Infinite
- From other structures
  - Topological spaces, Metric spaces, Measurable spaces, etc.














# Features Overview

VersoSlides supports:

* Elaborated Lean code blocks with hovers and info panels
* Inline Lean expressions: elaborated and type-checked
* Progressive proof reveals with magic comments
* Hidden setup code and replaced expressions
* Fragment animations (block and inline)
* Per-slide metadata (backgrounds, transitions)
* Speaker notes (press `s` on your keyboard)

:::fragment
Read on for examples of each.
:::

# Code Example

Here is an elaborated Lean code block:

```lean
def hello : IO Unit := do
  IO.println "Hello from VersoSlides!"
```

```lean
#check hello
```
And some inline {lean}`hello` for good measure. {lean}`Unit`

# Code on Light Background
%%%
backgroundColor := "#f5f5f5"
%%%

A light-themed slide with Lean code:

```lean
def greet (name : String) : String :=
  s!"Hello, {name}!"

#eval greet "Lean"
```

# Proof

```lean
def replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | n' + 1 => x :: replicate n' x

-- !fragment
theorem replicate_length : ∀ {n : Nat} {x : α},
    (replicate n x).length = n := by
  intro n
-- !fragment
  intro x
-- ^ !click
  induction n
  . grind [replicate]
  next n' ih =>
-- !fragment fadeUp
    simp only [replicate]
    conv =>
      rhs
      rw [← ih]
    simp
```

# Proof with Hidden Setup

```lean
/- !hide -/def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n/- !end hide -/
theorem fact_pos : ∀ n, 0 < fact n := by
-- !fragment
  intro n
-- ^ !click
  induction n with
  | zero => simp [fact]
-- !fragment
  | succ n ih =>
    simp [fact]
    omega
```

# Proof with Fragment Indices

```lean
/- !hide -/
def sum_to : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sum_to n
/- !end hide -/

-- !fragment 2
theorem sum_to_formula : ∀ n,
    2 * sum_to n = n * (n + 1) := by
-- !fragment 1
  intro n
-- ^ !click 1
  induction n with
  | zero => simp [sum_to]
-- !fragment 3
  | succ n ih =>
    grind [sum_to]
```

# Proof with Fragment Effects

```lean -show
/-- This function is invisible -/
def hiddenFunction (x : Nat) : String := s!"{x}{x}"
```
```lean
/- !fragment highlight-current-green -/def y := /- !fragment grow -/hiddenFunction/- !end fragment -/ /- !fragment shrink -/22/- !end fragment -//- !end fragment -/

-- !fragment grow
def z := 5
-- !fragment highlight-current-red
def zz := 22
```

# Hidden Lean

This slide has hidden setup code.

```lean -show
section
set_option pp.all true
variable {α : Type} [ToString α]
```
We have {lean}`α` available here:

# Without Panel

```lean -panel
-- There is no info panel here
def simple : Nat := 42
```

# Replace Example

```lean
def result : Nat :=
  /- !replace ... -/ List.length [1, 2, 3] /- !end replace -/
```

# Other Languages

```code rust
fn main() {
    let nums = vec![3, 1, 4, 1, 5, 9];
    let max = nums.iter().max().unwrap();
    println!("Max: {max}");
}
```

```code "c++"
#include <iostream>
#include <vector>

int main() {
    std::vector<int> v = {1, 2, 3};
    for (auto x : v) std::cout << x << "\n";
}
```

# Fragment Styles

:::fragment fadeUp
This block fades up.
:::

:::fragment fadeUp (index := 2)
This block also fades up, but with explicit index 2.
:::

Here is an {fragment (style := highlightRed)}[inline red highlight]
within a sentence.

And another {fragment (style := highlightBlue) (index := 3)}[inline blue highlight]
with an explicit index.

# Vertical Slides
%%%
vertical := true
%%%

This content appears on the first implicit vertical sub-slide.

## Sub-slide A

This is vertical sub-slide A.

Navigate *down* to see the next sub-slide.

## Sub-slide B
%%%
backgroundColor := "#4d7e65"
%%%

This vertical sub-slide has a custom green background.

:::notes
Vertical slides are great for supplementary content.
:::

# Custom Attributes

:::fitText
Big text!
:::

:::id "custom-paragraph"
This paragraph has a custom `id` attribute.
:::

:::attr («data-id» := "my-box")
This paragraph has a custom `data-id` for auto-animate matching.
:::

# Auto-Animate

%%%
autoAnimate := true
%%%

:::attr («data-id» := "title")
Small title
:::

# Auto-Animate (cont.)

%%%
autoAnimate := true
%%%

:::::fitText
:::attr («data-id» := "title")
*Big* title
:::
:::::

# Custom Background
%%%
backgroundColor := "#2d1b69"
transition := "zoom"
%%%

This slide has a purple background and uses the *zoom* transition.

# Thank You

That concludes the *VersoSlides* demo.

:::fragment
Questions?
:::

:::notes
Wrap up and take questions.
:::
