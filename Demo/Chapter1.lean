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

::: fragment
Typeclasses enable _ad-hoc polymorphism_:
:::

::: fragment
```lean
class myOp (α : Type) where
  op : α → α → α
```
:::

::: fragment
We endow specific types with their own operation behavior by providing instances:
:::

::: fragment
```lean
instance : myOp Nat where
  op := Nat.add

-- !fragment
instance : myOp Bool where
  op := Bool.or

-- !fragment
instance : myOp Float where
  op := fun x y => x*y
```
:::


# Why Typeclasses?

If we now evaluate these operations, we get different results based on the type:
```lean
#eval myOp.op 1 2
#eval myOp.op false false
#eval myOp.op 2.5 4.5
```

# Why Typeclasses?
::: fragment
We can also define functions that are polymorphic over any type with a `myOp` class:
```lean
def double {α : Type} [myOp α] (x : α) : α :=
  myOp.op x x

#eval double 3.3
```
:::
::: fragment
And compose instances to build new ones from existing ones:

```lean
instance [myOp α] : myOp (Array α) where
  op x y := Array.zipWith myOp.op x y

#eval myOp.op #[1, 2] #[3, 4]
```
:::

# Why Typeclasses?
:::fragment
The character `@` allows us to refer to the function with explicit type arguments:
:::

:::fragment
```lean
#check myOp.op
#check @myOp.op
```
:::

:::fragment
This allows us to use a specific instance without changing the default for the whole scope:
:::

:::fragment
```lean
instance latticeMyOp [Lattice α] : myOp α where
  op := fun x y => x ⊔ y

-- !fragment
example : Lattice Nat := by infer_instance

-- !fragment
#eval myOp.op 3 4
#eval @myOp.op Nat latticeMyOp 3 4
```
:::

# Why Typeclasses?

If we want to avoid the @ syntax, we can also open the instance locally, overriding the default for that scope:
```lean
#eval (let _ : myOp Nat := latticeMyOp; myOp.op 3 4)
```
