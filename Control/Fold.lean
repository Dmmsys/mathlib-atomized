/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Control.Traversable.Instances
public import Mathlib.Control.Traversable.Lemmas
public import Mathlib.Tactic.AdaptationNote

/-!

# List folds generalized to `Traversable`

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `foldMap` as a
primitive and `foldMap_hom` as a defining property.

```
def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω := ...

lemma foldMap_hom (α β) [Monoid α] [Monoid β] (f : α →* β) (g : γ → α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
...
```

`foldMap` uses a monoid ω to accumulate a value for every element of
a data structure and `foldMap_hom` uses a monoid homomorphism to
substitute the monoid used by `foldMap`. The two are sufficient to
define `foldl`, `foldr` and `toList`. `toList` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `toList` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`Traversable`.
-/

@[expose] public section


universe u v

open ULift CategoryTheory MulOpposite

namespace Monoid

variable {m : Type u → Type u} [Monad m]
variable {α β : Type u}

/-- For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : List β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (fun y ↦ const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*>
         traverse (fun y ↦ const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (fun y ↦ const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `Foldl`.
-/
/-
**Monoid.Foldl** 是 Mathlib 中的一个缩写定义，位于命名空间 `Monoid`。
形式化陈述：Foldl (α : Type u) : Type u
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : List β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (fun y ↦ const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*>
         traverse (fun y ↦ const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (fun y ↦ const.mk' (flip 
f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `Foldl`.
-/
abbrev Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ
/-
**Monoid.Foldl.mk** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldl`。
形式化陈述：{α : Type u} → (α → α) → Monoid.Foldl α
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldl.mk (f : α → α) : Foldl α :=
  op (↾f)
/-
**Monoid.Foldl.get** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldl`。
形式化陈述：{α : Type u} → Monoid.Foldl α → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldl.get (x : Foldl α) : α → α :=
  ConcreteCategory.hom (unop x)

@[simps]
/-
**Monoid.Foldl.ofFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldl`。
形式化陈述：{α β : Type u} → (β → α → β) → FreeMonoid α →* Monoid.Foldl β
参数：β → α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldl.ofFreeMonoid (f : β → α → β) : FreeMonoid α →* Monoid.Foldl β where
  toFun xs := op <| ↾(flip (List.foldl f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' := by
    intros
    simp only [FreeMonoid.toList_mul, List.foldl_append, Function.flip_def]
    rfl
/-
**Monoid.Foldr** 是 Mathlib 中的一个缩写定义，位于命名空间 `Monoid`。
形式化陈述：Foldr (α : Type u) : Type u
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Foldr (α : Type u) : Type u :=
  End α
/-
**Monoid.Foldr.mk** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldr`。
形式化陈述：{α : Type u} → (α → α) → Monoid.Foldr α
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldr.mk (f : α → α) : Foldr α :=
  ↾f
/-
**Monoid.Foldr.get** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldr`。
形式化陈述：{α : Type u} → Monoid.Foldr α → α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldr.get (x : Foldr α) : α → α :=
  ConcreteCategory.hom x

@[simps]
/-
**Monoid.Foldr.ofFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Foldr`。
形式化陈述：{α β : Type u} → (α → β → β) → FreeMonoid α →* Monoid.Foldr β
参数：α → β → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Foldr.ofFreeMonoid (f : α → β → β) : FreeMonoid α →* Monoid.Foldr β where
  toFun xs := ↾(flip (List.foldr f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' _ _ := by
    apply ConcreteCategory.ext
    ext
    apply List.foldr_append
/-
**Monoid.foldlM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Monoid`。
形式化陈述：foldlM (m : Type u -> Type u) [Monad m] (α : Type u) : Type u
参数：m : Type u -> Type u；α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev foldlM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  MulOpposite <| End <| KleisliCat.mk m α
/-
**Monoid.foldlM.mk** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldlM`。
形式化陈述：{m : Type u → Type u} → [inst : Monad m] → {α : Type u} → (α → m α) → Mono
id.foldlM m α
参数：α → m α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldlM.mk (f : α → m α) : foldlM m α :=
  op f
/-
**Monoid.foldlM.get** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldlM`。
形式化陈述：{m : Type u → Type u} → [inst : Monad m] → {α : Type u} → Monoid.foldlM m 
α → α → m α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldlM.get (x : foldlM m α) : α → m α :=
  unop x

@[simps]
/-
**Monoid.foldlM.ofFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldlM`。
形式化陈述：{m : Type u → Type u} →   [inst : Monad m] → {α β : Type u} → [inst_1 : La
wfulMonad m] → (β → α → m β) → FreeMonoid α →* Monoid.foldlM m β
参数：β → α → m β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldlM.ofFreeMonoid [LawfulMonad m] (f : β → α → m β) : FreeMonoid α →* Monoid.foldlM m β where
  toFun xs := op <| flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros
    apply unop_injective
    funext
    apply List.foldlM_append
/-
**Monoid.foldrM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Monoid`。
形式化陈述：foldrM (m : Type u -> Type u) [Monad m] (α : Type u) : Type u
参数：m : Type u -> Type u；α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev foldrM (m : Type u → Type u) [Monad m] (α : Type u) : Type u :=
  End <| KleisliCat.mk m α
/-
**Monoid.foldrM.mk** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldrM`。
形式化陈述：{m : Type u → Type u} → [inst : Monad m] → {α : Type u} → (α → m α) → Mono
id.foldrM m α
参数：α → m α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldrM.mk (f : α → m α) : foldrM m α :=
  f
/-
**Monoid.foldrM.get** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldrM`。
形式化陈述：{m : Type u → Type u} → [inst : Monad m] → {α : Type u} → Monoid.foldrM m 
α → α → m α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldrM.get (x : foldrM m α) : α → m α :=
  x

@[simps]
/-
**Monoid.foldrM.ofFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.foldrM`。
形式化陈述：{m : Type u → Type u} →   [inst : Monad m] → {α β : Type u} → [inst_1 : La
wfulMonad m] → (α → β → m β) → FreeMonoid α →* Monoid.foldrM m β
参数：α → β → m β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldrM.ofFreeMonoid [LawfulMonad m] (f : α → β → m β) : FreeMonoid α →* Monoid.foldrM m β where
  toFun xs := flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append

end Monoid

namespace Traversable

open Monoid Functor

section Defs

variable {α β : Type u} {t : Type u → Type u} [Traversable t]

/-
**Traversable.foldMap** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：foldMap {α ω} [One ω] [Mul ω] (f : α -> ω) : t α -> ω
参数：f : α -> ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (Const.mk' ∘ f)
/-
**Traversable.foldl** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：foldl (f : α -> β -> α) (x : α) (xs : t β) : α
参数：f : α -> β -> α；x : α；xs : t β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
  (foldMap (Foldl.mk ∘ flip f) xs).get x
/-
**Traversable.foldr** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：foldr (f : α -> β -> β) (x : β) (xs : t α) : β
参数：f : α -> β -> β；x : β；xs : t α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
  (foldMap (Foldr.mk ∘ f) xs).get x

/-- Conceptually, `toList` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma toList_spec (x : t α) : toList x = foldMap FreeMonoid.mk x`.

The definition of `toList` is based on `foldl` and `List.cons` for
speed. It is faster than using `foldMap FreeMonoid.mk` because, by
using `foldl` and `List.cons`, each insertion is done in constant
time. As a consequence, `toList` performs in linear.

On the other hand, `foldMap FreeMonoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
/-
**Traversable.toList** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：toList : t α -> List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conceptually, `toList` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma toList_spec (x : t α) : toList x = foldMap FreeMonoid.mk x`.

The definition of `toList` is based on `foldl` and `List.cons` for
speed. It is faster than using `foldMap FreeMonoid.mk` because, by
using `foldl` and `List.cons`, each insertion is done in constant
time. As a consequence, `toList` performs in linear.

On the other hand, `foldMap FreeMonoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time.
-/
def toList : t α → List α :=
  List.reverse ∘ foldl (flip List.cons) []
/-
**Traversable.length** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：length (xs : t α) : Nat
参数：xs : t α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def length (xs : t α) : ℕ :=
  down <| foldl (fun l _ => up <| l.down + 1) (up 0) xs

variable {m : Type u → Type u} [Monad m]
/-
**Traversable.foldlm** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：foldlm (f : α -> β -> m α) (x : α) (xs : t β) : m α
参数：f : α -> β -> m α；x : α；xs : t β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldlm (f : α → β → m α) (x : α) (xs : t β) : m α :=
  (foldMap (foldlM.mk ∘ flip f) xs).get x
/-
**Traversable.foldrm** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：foldrm (f : α -> β -> m β) (x : β) (xs : t α) : m β
参数：f : α -> β -> m β；x : β；xs : t α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def foldrm (f : α → β → m β) (x : β) (xs : t α) : m β :=
  (foldMap (foldrM.mk ∘ f) xs).get x

end Defs

section ApplicativeTransformation

variable {α β γ : Type u}

open Function hiding const

set_option backward.isDefEq.respectTransparency.types false in
/-
**Traversable.mapFold** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：mapFold [Monoid α] [Monoid β] (f : α ->* β) : ApplicativeTransformation (C
onst α) (Const β) where app _
参数：f : α ->* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapFold [Monoid α] [Monoid β] (f : α →* β) : ApplicativeTransformation (Const α) (Const β) where
  app _ := f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
  preserves_pure' := by intros; simp only [map_one, pure]
/-
**Traversable.Free.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable.Free`。
形式化陈述：∀ {α β : Type u} (f : α → β) (xs : List α), f <$> xs = FreeMonoid.toList (
(FreeMonoid.map f) (FreeMonoid.ofList xs))
参数：f : α → β；xs : List α；(FreeMonoid.map f) (FreeMonoid.ofList xs)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Free.map_eq_map (f : α → β) (xs : List α) :
    f <$> xs = (FreeMonoid.toList (FreeMonoid.map f (FreeMonoid.ofList xs))) :=
  rfl
/-
**Traversable.foldl.unop_ofFreeMonoid** 是 Mathlib 中的一个定理，位于命名空间 `Traversable.fol
dl`。
形式化陈述：∀ {α β : Type u} (f : β → α → β) (xs : FreeMonoid α) (a : β),   (CategoryT
heory.ConcreteCategory.hom (MulOpposite.unop ((Monoid.Foldl.ofFreeMonoid f) xs))
) a =     List.foldl f a (FreeMonoid.toList xs)
参数：f : β → α → β；xs : FreeMonoid α；a : β；CategoryTheory.ConcreteCategory.hom (Mu
lOpposite.unop ((Monoid.Foldl.ofFreeMonoid f) xs))；FreeMonoid.toList xs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl.unop_ofFreeMonoid (f : β → α → β) (xs : FreeMonoid α) (a : β) :
    ConcreteCategory.hom (unop (Foldl.ofFreeMonoid f xs)) a =
      List.foldl f a (FreeMonoid.toList xs) :=
  rfl

variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]

open LawfulTraversable

set_option backward.isDefEq.respectTransparency false in
/-
**Traversable.foldMap_hom** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldMap_hom [Monoid α] [Monoid β] (f : α ->* β) (g : γ -> α) (x : t γ) : f
 (foldMap g x) = foldMap (f ∘ g) x
参数：f : α ->* β；g : γ -> α；x : t γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
· 使用定理 `instLawfulApplicativeConst`：∀ {α : Type u_1} [inst : Monoid α], LawfulAp
plicative (Functor.Const α)
-/
theorem foldMap_hom [Monoid α] [Monoid β] (f : α →* β) (g : γ → α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl
/-
**Traversable.foldMap_hom_free** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldMap_hom_free [Monoid β] (f : FreeMonoid α ->* β) (x : t α) : f (foldMa
p FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x
参数：f : FreeMonoid α ->* β；x : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Traversable.foldMap_hom`：foldMap_hom [Monoid α] [Monoid β] (f : α ->* β)
 (g : γ -> α) (x : t γ) : f (foldMap g x) = foldMap (f ∘ g) x
-/
theorem foldMap_hom_free [Monoid β] (f : FreeMonoid α →* β) (x : t α) :
    f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x :=
  foldMap_hom f _ x

end ApplicativeTransformation

section Equalities

open LawfulTraversable

open List (cons)

variable {α β γ : Type u}
variable {t : Type u → Type u} [Traversable t] [LawfulTraversable t]

@[simp]
/-
**Traversable.foldl.ofFreeMonoid_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Traversable.
foldl`。
形式化陈述：∀ {α β : Type u} (f : α → β → α), ⇑(Monoid.Foldl.ofFreeMonoid f) ∘ FreeMon
oid.of = Monoid.Foldl.mk ∘ flip f
参数：f : α → β → α；Monoid.Foldl.ofFreeMonoid f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl.ofFreeMonoid_comp_of (f : α → β → α) :
    Foldl.ofFreeMonoid f ∘ FreeMonoid.of = Foldl.mk ∘ flip f :=
  rfl

@[simp]
/-
**Traversable.foldr.ofFreeMonoid_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Traversable.
foldr`。
形式化陈述：∀ {α β : Type u} (f : β → α → α), ⇑(Monoid.Foldr.ofFreeMonoid f) ∘ FreeMon
oid.of = Monoid.Foldr.mk ∘ f
参数：f : β → α → α；Monoid.Foldr.ofFreeMonoid f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr.ofFreeMonoid_comp_of (f : β → α → α) :
    Foldr.ofFreeMonoid f ∘ FreeMonoid.of = Foldr.mk ∘ f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Traversable.foldlm.ofFreeMonoid_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Traversable
.foldlm`。
形式化陈述：∀ {α β : Type u} {m : Type u → Type u} [inst : Monad m] [inst_1 : LawfulMo
nad m] (f : α → β → m α),   ⇑(Monoid.foldlM.ofFreeMonoid f) ∘ FreeMonoid.of = Mo
noid.foldlM.mk ∘ flip f
参数：f : α → β → m α；Monoid.foldlM.ofFreeMonoid f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldlM_cons`：∀ {m : Type u_1 → Type u_2} {β : Type u_1} {α : Type u
_3} [inst : Monad m] {f : β → α → m β} {b : β} {a : α}   {l : List α},   List.fo
ldlM f…
· 使用定理 `bind_pure`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [inst : Monad m] [
LawfulMonad m] (x : m α), x >>= pure = x
-/
theorem foldlm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : α → β → m α) :
    foldlM.ofFreeMonoid f ∘ FreeMonoid.of = foldlM.mk ∘ flip f := by
  ext1 x
  simp only [foldlM.ofFreeMonoid, Function.flip_def, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, FreeMonoid.toList_of, List.foldlM_cons, List.foldlM_nil, bind_pure,
    foldlM.mk, op_inj]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Traversable.foldrm.ofFreeMonoid_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Traversable
.foldrm`。
形式化陈述：∀ {α β : Type u} {m : Type u → Type u} [inst : Monad m] [inst_1 : LawfulMo
nad m] (f : β → α → m α),   ⇑(Monoid.foldrM.ofFreeMonoid f) ∘ FreeMonoid.of = Mo
noid.foldrM.mk ∘ f
参数：f : β → α → m α；Monoid.foldrM.ofFreeMonoid f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldrM_cons`：∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u
_1} [inst : Monad m] [LawfulMonad m] {a : α} {l : List α}   {f : α → β → m β} {b
 : β},…
· 使用定理 `LawfulMonad.pure_bind`：∀ {m : Type u → Type v} {inst : Monad m} [self : 
LawfulMonad m] {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldrm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : β → α → m α) :
    foldrM.ofFreeMonoid f ∘ FreeMonoid.of = foldrM.mk ∘ f := by
  ext
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, Function.flip_def]

set_option backward.isDefEq.respectTransparency false in
/-
**Traversable.toList_spec** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid
.of xs)
参数：xs : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeMonoid.reverse_reverse`：reverse_reverse {a : FreeMonoid α} : reverse
 (reverse a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.foldr_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α 
→ β → β} {b : β},   List.foldr f b l.reverse = List.foldl (fun x y => f y x) b l
· 使用定理 `List.foldl_flip_cons_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : Lis
t α} {f : α → β} {l' : List β},   List.foldl (fun xs y => f y :: xs) l' l = (Lis
t.map f l).reverse +…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun'`：∀ {α : Type u_1}, (List.map fun a => a) = id
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `Traversable.foldMap_hom_free`：foldMap_hom_free [Monoid β] (f : FreeMonoi
d α ->* β) (x : t α) : f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of)
 x
-/
theorem toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs) :=
  Eq.symm <|
    calc
      FreeMonoid.toList (foldMap FreeMonoid.of xs) =
          FreeMonoid.toList (foldMap FreeMonoid.of xs).reverse.reverse := by
          simp only [FreeMonoid.reverse_reverse]
      _ = (List.foldr cons [] (foldMap FreeMonoid.of xs).toList.reverse).reverse := by simp
      _ = (ConcreteCategory.hom
          (unop (Foldl.ofFreeMonoid (flip cons) (foldMap FreeMonoid.of xs))) []).reverse := by
            simp [Function.flip_def, List.foldr_reverse, Foldl.ofFreeMonoid, unop_op]
      _ = toList xs := by
            rw [foldMap_hom_free (Foldl.ofFreeMonoid (flip <| @cons α))]
            simp only [toList, foldl, Foldl.get, foldl.ofFreeMonoid_comp_of,
              Function.comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Traversable.foldMap_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ) (xs : t α) : foldMap g (f
 <$> xs) = foldMap (g ∘ f) xs
参数：f : α -> β；g : β -> γ；xs : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
· 使用定理 `instLawfulApplicativeConst`：∀ {α : Type u_1} [inst : Monoid α], LawfulAp
plicative (Functor.Const α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldMap_map [Monoid γ] (f : α → β) (g : β → γ) (xs : t α) :
    foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by
  simp only [foldMap, traverse_map, Function.comp_def]
/-
**Traversable.foldl_toList** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldl_toList (f : α -> β -> α) (xs : t β) (x : α) : foldl f x xs = List.fo
ldl f x (toList xs)
参数：f : α -> β -> α；xs : t β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FreeMonoid.toList_ofList`：toList_ofList (l : List α) : toList (ofList l)
 = l
· 使用定理 `Traversable.foldl.unop_ofFreeMonoid`：∀ {α β : Type u} (f : β → α → β) (x
s : FreeMonoid α) (a : β),   (CategoryTheory.ConcreteCategory.hom (MulOpposite.u
nop ((Monoid.Foldl.ofFree…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `Traversable.foldMap_hom_free`：foldMap_hom_free [Monoid β] (f : FreeMonoi
d α ->* β) (x : t α) : f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of)
 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldl_toList (f : α → β → α) (xs : t β) (x : α) :
    foldl f x xs = List.foldl f x (toList xs) := by
  rw [← FreeMonoid.toList_ofList (toList xs), ← foldl.unop_ofFreeMonoid]
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]
/-
**Traversable.foldr_toList** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldr_toList (f : α -> β -> β) (xs : t α) (x : β) : foldr f x xs = List.fo
ldr f x (toList xs)
参数：f : α -> β -> β；xs : t α；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `Traversable.foldr.eq_1`：∀ {α β : Type u} {t : Type u → Type u} [inst : T
raversable t] (f : α → β → β) (x : β) (xs : t α),   Traversable.foldr f x xs = (
Traversable.…
· 使用定理 `Monoid.Foldr.get.eq_1`：∀ {α : Type u} (x : Monoid.Foldr α), x.get = ⇑(Ca
tegoryTheory.ConcreteCategory.hom x)
· 使用定理 `FreeMonoid.ofList_toList`：ofList_toList (xs : FreeMonoid α) : ofList (to
List xs) = xs
· 使用定理 `Traversable.foldMap_hom_free`：foldMap_hom_free [Monoid β] (f : FreeMonoi
d α ->* β) (x : t α) : f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of)
 x
· 使用定理 `Traversable.foldr.ofFreeMonoid_comp_of`：∀ {α β : Type u} (f : β → α → α)
, ⇑(Monoid.Foldr.ofFreeMonoid f) ∘ FreeMonoid.of = Monoid.Foldr.mk ∘ f
-/
theorem foldr_toList (f : α → β → β) (xs : t α) (x : β) :
    foldr f x xs = List.foldr f x (toList xs) := by
  change _ = (Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs)).hom _
  rw [toList_spec, foldr, Foldr.get, FreeMonoid.ofList_toList, foldMap_hom_free,
    foldr.ofFreeMonoid_comp_of]
/-
**Traversable.toList_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：toList_map (f : α -> β) (xs : t α) : toList (f <$> xs) = f < > toList xs
参数：f : α -> β；xs : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `Traversable.foldMap_map`：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ
) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs
· 使用定理 `Traversable.foldMap_hom`：foldMap_hom [Monoid α] [Monoid β] (f : α ->* β)
 (g : γ -> α) (x : t γ) : f (foldMap g x) = foldMap (f ∘ g) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toList_map (f : α → β) (xs : t α) : toList (f <$> xs) = f <$> toList xs := by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, Function.comp_def]

@[simp]
/-
**Traversable.foldl_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldl_map (g : β -> γ) (f : α -> γ -> α) (a : α) (l : t β) : foldl f a (g 
<$> l) = foldl (fun x y => f x (g y)) a l
参数：g : β -> γ；f : α -> γ -> α；a : α；l : t β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.foldMap_map`：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ
) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  simp only [foldl, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]
/-
**Traversable.foldr_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldr_map (g : β -> γ) (f : γ -> α -> α) (a : α) (l : t β) : foldr f a (g 
<$> l) = foldr (f ∘ g) a l
参数：g : β -> γ；f : γ -> α -> α；a : α；l : t β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.foldMap_map`：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ
) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
    foldr f a (g <$> l) = foldr (f ∘ g) a l := by
  simp only [foldr, foldMap_map, Function.comp_def]

@[simp]
/-
**Traversable.toList_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：toList_eq_self {xs : List α} : toList xs = xs
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toList_eq_self {xs : List α} : toList xs = xs := by
  simp only [toList_spec, foldMap, traverse]
  induction xs with
  | nil => rfl
  | cons _ _ ih => (conv_rhs => rw [← ih]); rfl
/-
**Traversable.length_toList** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：length_toList {xs : t α} : length xs = List.length (toList xs)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.foldl_toList`：foldl_toList (f : α -> β -> α) (xs : t β) (x :
 α) : foldl f x xs = List.foldl f x (toList xs)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Internal.Linear.ExprCnstr.eq_true_of_isValid`：∀ (ctx : Nat.Internal.
Linear.Context) (c : Nat.Internal.Linear.ExprCnstr),   c.toNormPoly.isValid = tr
ue → Nat.Internal.Linear.ExprCnstr.den…
-/
theorem length_toList {xs : t α} : length xs = List.length (toList xs) := by
  unfold length
  rw [foldl_toList]
  generalize toList xs = ys
  rw [← Nat.add_zero ys.length]
  generalize 0 = n
  induction ys generalizing n with
  | nil => simp
  | cons _ _ ih => simp +arith [ih]

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]

set_option backward.isDefEq.respectTransparency false in
/-
**Traversable.foldlm_toList** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldlm_toList {f : α -> β -> m α} {x : α} {xs : t β} : foldlm f x xs = Lis
t.foldlM f x (toList xs)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `Traversable.foldMap_hom_free`：foldMap_hom_free [Monoid β] (f : FreeMonoi
d α ->* β) (x : t α) : f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of)
 x
· 使用定理 `Traversable.foldlm.ofFreeMonoid_comp_of`：∀ {α β : Type u} {m : Type u → 
Type u} [inst : Monad m] [inst_1 : LawfulMonad m] (f : α → β → m α),   ⇑(Monoid.
foldlM.ofFreeMonoid f) ∘ Free…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldlm_toList {f : α → β → m α} {x : α} {xs : t β} :
    foldlm f x xs = List.foldlM f x (toList xs) :=
  calc foldlm f x xs
    _ = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]
/-
**Traversable.foldrm_toList** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldrm_toList (f : α -> β -> m β) (x : β) (xs : t α) : foldrm f x xs = Lis
t.foldrM f x (toList xs)
参数：f : α -> β -> m β；x : β；xs : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Traversable.toList_spec`：toList_spec (xs : t α) : toList xs = FreeMonoid
.toList (foldMap FreeMonoid.of xs)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Traversable.foldMap_hom_free`：foldMap_hom_free [Monoid β] (f : FreeMonoi
d α ->* β) (x : t α) : f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of)
 x
· 使用定理 `Traversable.foldrm.ofFreeMonoid_comp_of`：∀ {α β : Type u} {m : Type u → 
Type u} [inst : Monad m] [inst_1 : LawfulMonad m] (f : β → α → m α),   ⇑(Monoid.
foldrM.ofFreeMonoid f) ∘ Free…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldrm_toList (f : α → β → m β) (x : β) (xs : t α) :
    foldrm f x xs = List.foldrM f x (toList xs) := by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]

@[simp]
/-
**Traversable.foldlm_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldlm_map (g : β -> γ) (f : α -> γ -> m α) (a : α) (l : t β) : foldlm f a
 (g <$> l) = foldlm (fun x y => f x (g y)) a l
参数：g : β -> γ；f : α -> γ -> m α；a : α；l : t β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.foldMap_map`：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ
) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldlm_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
    foldlm f a (g <$> l) = foldlm (fun x y => f x (g y)) a l := by
  simp only [foldlm, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]
/-
**Traversable.foldrm_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：foldrm_map (g : β -> γ) (f : γ -> α -> m α) (a : α) (l : t β) : foldrm f a
 (g <$> l) = foldrm (f ∘ g) a l
参数：g : β -> γ；f : γ -> α -> m α；a : α；l : t β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.foldMap_map`：foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ
) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldrm_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
    foldrm f a (g <$> l) = foldrm (f ∘ g) a l := by
  simp only [foldrm, foldMap_map, Function.comp_def]

end Equalities

end Traversable

