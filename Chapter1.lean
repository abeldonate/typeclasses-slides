import VersoSlides
import Verso.Doc.Concrete
import Mathlib.Order.Lattice
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Cast.Defs

open VersoSlides

set_option verso.code.warnLineLength 500

#doc (Slides) "Typeclasses Chapter 1" =>
%%%
theme := "black"
slideNumber := true
transition := "slide"
%%%

# Typeclasses. First Talk

Welcome to *VersoSlides* — a Verso genre for building
[reveal.js](https://revealjs.com) slide presentations from Lean.

This demo exercises all the major features.

:::notes
This is a speaker note on the introduction slide.
Press *S* to open the speaker view.
:::

# Why Typeclasses?

Typeclasses enable _ad-hoc polymorphism_:

```lean
class myAdd (α : Type) where
  add : α → α → α
```

# Why Typeclasses?

We endow specific types with their own addition behavior by providing instances:

```lean
instance : myAdd Nat where
  add := Nat.add

instance : myAdd Bool where
  add := Bool.or

instance : myAdd Float where
  add := fun x y => x*y
```


# Why Typeclasses?

If we now evaluate these sums, we get different results based on the type:
```lean
#eval myAdd.add 1 2
#eval myAdd.add false false
#eval myAdd.add 2.5 4.5
```

# Why Typeclasses?

We can also define functions that are polymorphic over any type with a `myAdd` class:
```lean
def double {α : Type} [myAdd α] (x : α) : α :=
  myAdd.add x x

#eval double 3.3
```

# Why Typeclasses?
And compose instances to build new ones from existing ones:
```lean
instance [myAdd α] : myAdd (Array α) where
  add x y := Array.zipWith myAdd.add x y

#eval myAdd.add #[1, 2] #[3, 4]
```

# Why Typeclasses?
Adding `@` allows us to refer to the function with explicit type arguments:
```lean
#check myAdd.add
#check @myAdd.add
```

# Why Typeclasses?

```lean
instance latticeMyAdd [Lattice α] : myAdd α where
  add := fun x y => x ⊔ y

example : Lattice Nat := by infer_instance

#eval myAdd.add 3 4
#eval @myAdd.add Nat latticeMyAdd 3 4
```


# Why Typeclasses?

If we want to avoid the @ syntax, we can also open the instance locally, overriding the default for that scope:
```lean
#eval (let _ : myAdd Nat := latticeMyAdd; myAdd.add 3 4)
```
