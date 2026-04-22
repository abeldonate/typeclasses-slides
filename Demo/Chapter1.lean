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

# Typeclasses. Part 1


# Why Typeclasses?

Typeclasses enable _ad-hoc polymorphism_:

```lean
class myOp (α : Type) where
  add : α → α → α
```

We endow specific types with their own addition behavior by providing instances:

```lean
instance : myOp Nat where
  add := Nat.add

instance : myOp Bool where
  add := Bool.or

instance : myOp Float where
  add := fun x y => x*y
```


# Why Typeclasses?

If we now evaluate these sums, we get different results based on the type:
```lean
#eval myOp.add 1 2
#eval myOp.add false false
#eval myOp.add 2.5 4.5
```

# Why Typeclasses?

We can also define functions that are polymorphic over any type with a `myOp` class:
```lean
def double {α : Type} [myOp α] (x : α) : α :=
  myOp.add x x

#eval double 3.3
```
And compose instances to build new ones from existing ones:

```lean
instance [myOp α] : myOp (Array α) where
  add x y := Array.zipWith myOp.add x y

#eval myOp.add #[1, 2] #[3, 4]
```

# Why Typeclasses?
:::fragment
Adding `@` allows us to refer to the function with explicit type arguments:
:::

:::fragment
```lean
#check myOp.add
#check @myOp.add
```
:::

:::fragment
This allows us to use a specific instance without changing the default for the whole scope:
:::

:::fragment
```lean
instance latticeMyOp [Lattice α] : myOp α where
  add := fun x y => x ⊔ y

example : Lattice Nat := by infer_instance

#eval myOp.add 3 4
#eval @myOp.add Nat latticeMyOp 3 4
```
:::

# Why Typeclasses?

If we want to avoid the @ syntax, we can also open the instance locally, overriding the default for that scope:
```lean
#eval (let _ : myOp Nat := latticeMyOp; myOp.add 3 4)
```
