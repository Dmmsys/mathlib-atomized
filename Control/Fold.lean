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

variable {m : Type u -> Type u} [Monad m]
variable {α β : Type u}

/--
Definition of `Foldl` / `Foldl` 的定义

English:
abbreviation Foldl
  signature: (α : Type u)
  body: (End α)ᵐᵒᵖ

中文:
缩写 Foldl
  签名: (α : 类型u)
  定义体: (End α)ᵐᵒᵖ
-/
abbrev Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ

/--
Definition of `Foldl.mk` / `Foldl.mk` 的定义

English:
definition Foldl.mk
  signature: (f : α -> α)
  body: op (↾f)

中文:
定义 Foldl.mk
  签名: (f : α -> α)
  定义体: op (↾f)
-/
def Foldl.mk (f : α -> α) : Foldl α :=
  op (↾f)

/--
Definition of `Foldl.get` / `Foldl.get` 的定义

English:
definition Foldl.get
  signature: (x : Foldl α)
  body: ConcreteCategory.hom (unop x)

@[simps]

中文:
定义 Foldl.get
  签名: (x : Foldl α)
  定义体: ConcreteCategory.hom (unop x)

@[simps]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom
-/
def Foldl.get (x : Foldl α) : α -> α :=
  ConcreteCategory.hom (unop x)

@[simps]
/--
Definition of `Foldl.ofFreeMonoid` / `Foldl.ofFreeMonoid` 的定义

English:
definition Foldl.ofFreeMonoid
  signature: (f : β -> α -> β)
  body: op ↾(flip (List.foldl f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' := by
    intros
    simp only [FreeMonoid.toList_mul, List.foldl_append, Function.flip_def]
    rfl

中文:
定义 Foldl.ofFreeMonoid
  签名: (f : β -> α -> β)
  定义体: op ↾(flip (List.foldl f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' := by
    intros
    simp only [FreeMonoid.toList_mul, List.foldl_append, Function.flip_def]
    rfl

Depends on / 依赖: FreeMonoid, FreeMonoid.toList, List.foldl, toList
-/
def Foldl.ofFreeMonoid (f : β -> α -> β) : FreeMonoid α ->* Monoid.Foldl β where
toFun xs := op ↾(flip (List.foldl f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' := by
    intros
    simp only [FreeMonoid.toList_mul, List.foldl_append, Function.flip_def]
    rfl

/--
Definition of `Foldr` / `Foldr` 的定义

English:
abbreviation Foldr
  signature: (α : Type u)
  body: End α

中文:
缩写 Foldr
  签名: (α : 类型u)
  定义体: End α
-/
abbrev Foldr (α : Type u) : Type u :=
  End α

/--
Definition of `Foldr.mk` / `Foldr.mk` 的定义

English:
definition Foldr.mk
  signature: (f : α -> α)
  body: ↾f

中文:
定义 Foldr.mk
  签名: (f : α -> α)
  定义体: ↾f
-/
def Foldr.mk (f : α -> α) : Foldr α :=
  ↾f

/--
Definition of `Foldr.get` / `Foldr.get` 的定义

English:
definition Foldr.get
  signature: (x : Foldr α)
  body: ConcreteCategory.hom x

@[simps]

中文:
定义 Foldr.get
  签名: (x : Foldr α)
  定义体: ConcreteCategory.hom x

@[simps]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom
-/
def Foldr.get (x : Foldr α) : α -> α :=
  ConcreteCategory.hom x

@[simps]
/--
Definition of `Foldr.ofFreeMonoid` / `Foldr.ofFreeMonoid` 的定义

English:
definition Foldr.ofFreeMonoid
  signature: (f : α -> β -> β)
  body: ↾(flip (List.foldr f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' _ _ := by
    apply ConcreteCategory.ext
    ext
    apply List.foldr_append

中文:
定义 Foldr.ofFreeMonoid
  签名: (f : α -> β -> β)
  定义体: ↾(flip (List.foldr f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' _ _ := by
    apply ConcreteCategory.ext
    ext
    apply List.foldr_append

Depends on / 依赖: FreeMonoid, FreeMonoid.toList, List.foldr, toList
-/
def Foldr.ofFreeMonoid (f : α -> β -> β) : FreeMonoid α ->* Monoid.Foldr β where
  toFun xs := ↾(flip (List.foldr f) (FreeMonoid.toList xs))
  map_one' := rfl
  map_mul' _ _ := by
    apply ConcreteCategory.ext
    ext
    apply List.foldr_append

/--
Definition of `foldlM` / `foldlM` 的定义

English:
abbreviation foldlM
  signature: (m : Type u -> Type u) [Monad m] (α : Type u)
  body: MulOpposite End KleisliCat.mk m α

中文:
缩写 foldlM
  签名: (m : 类型u -> 类型u) [单子 m] (α : 类型u)
  定义体: MulOpposite End KleisliCat.mk m α

Depends on / 依赖: KleisliCat, KleisliCat.mk, MulOpposite
-/
abbrev foldlM (m : Type u -> Type u) [Monad m] (α : Type u) : Type u :=
MulOpposite End KleisliCat.mk m α

/--
Definition of `foldlM.mk` / `foldlM.mk` 的定义

English:
definition foldlM.mk
  signature: (f : α -> m α)
  body: op f

中文:
定义 foldlM.mk
  签名: (f : α -> m α)
  定义体: op f
-/
def foldlM.mk (f : α -> m α) : foldlM m α :=
  op f

/--
Definition of `foldlM.get` / `foldlM.get` 的定义

English:
definition foldlM.get
  signature: (x : foldlM m α)
  body: unop x

@[simps]

中文:
定义 foldlM.get
  签名: (x : foldlM m α)
  定义体: unop x

@[simps]
-/
def foldlM.get (x : foldlM m α) : α -> m α :=
  unop x

@[simps]
/--
Definition of `foldlM.ofFreeMonoid` / `foldlM.ofFreeMonoid` 的定义

English:
definition foldlM.ofFreeMonoid
  signature: [LawfulMonad m] (f : β -> α -> m β)
  body: op flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros
    apply unop_injective
    funext
    apply List.foldlM_append

中文:
定义 foldlM.ofFreeMonoid
  签名: [合法单子 m] (f : β -> α -> m β)
  定义体: op flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros
    apply unop_injective
    funext
    apply List.foldlM_append

Depends on / 依赖: FreeMonoid, FreeMonoid.toList, List.foldlM, foldlM, toList
-/
def foldlM.ofFreeMonoid [LawfulMonad m] (f : β -> α -> m β) : FreeMonoid α ->* Monoid.foldlM m β where
toFun xs := op flip (List.foldlM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by
    intros
    apply unop_injective
    funext
    apply List.foldlM_append

/--
Definition of `foldrM` / `foldrM` 的定义

English:
abbreviation foldrM
  signature: (m : Type u -> Type u) [Monad m] (α : Type u)
  body: End KleisliCat.mk m α

中文:
缩写 foldrM
  签名: (m : 类型u -> 类型u) [单子 m] (α : 类型u)
  定义体: End KleisliCat.mk m α

Depends on / 依赖: KleisliCat, KleisliCat.mk
-/
abbrev foldrM (m : Type u -> Type u) [Monad m] (α : Type u) : Type u :=
End KleisliCat.mk m α

/--
Definition of `foldrM.mk` / `foldrM.mk` 的定义

English:
definition foldrM.mk
  signature: (f : α -> m α)
  body: f

中文:
定义 foldrM.mk
  签名: (f : α -> m α)
  定义体: f
-/
def foldrM.mk (f : α -> m α) : foldrM m α :=
  f

/--
Definition of `foldrM.get` / `foldrM.get` 的定义

English:
definition foldrM.get
  signature: (x : foldrM m α)
  body: x

@[simps]

中文:
定义 foldrM.get
  签名: (x : foldrM m α)
  定义体: x

@[simps]
-/
def foldrM.get (x : foldrM m α) : α -> m α :=
  x

@[simps]
/--
Definition of `foldrM.ofFreeMonoid` / `foldrM.ofFreeMonoid` 的定义

English:
definition foldrM.ofFreeMonoid
  signature: [LawfulMonad m] (f : α -> β -> m β)
  body: flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append

中文:
定义 foldrM.ofFreeMonoid
  签名: [合法单子 m] (f : α -> β -> m β)
  定义体: flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append

Depends on / 依赖: FreeMonoid, FreeMonoid.toList, List.foldrM, foldrM, toList
-/
def foldrM.ofFreeMonoid [LawfulMonad m] (f : α -> β -> m β) : FreeMonoid α ->* Monoid.foldrM m β where
  toFun xs := flip (List.foldrM f) (FreeMonoid.toList xs)
  map_one' := rfl
  map_mul' := by intros; funext; apply List.foldrM_append

end Monoid

namespace Traversable

open Monoid Functor

section Defs

variable {α β : Type u} {t : Type u -> Type u} [Traversable t]

/--
Definition of `foldMap` / `foldMap` 的定义

English:
definition foldMap
  signature: {α ω} [One ω] [Mul ω] (f : α -> ω)
  body: traverse (Const.mk' ∘ f)

中文:
定义 foldMap
  签名: {α ω} [幺 ω] [乘法 ω] (f : α -> ω)
  定义体: traverse (Const.mk' ∘ f)

Depends on / 依赖: Const.mk, traverse
-/
def foldMap {α ω} [One ω] [Mul ω] (f : α -> ω) : t α -> ω :=
  traverse (Const.mk' ∘ f)

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: (f : α -> β -> α) (x : α) (xs : t β)
  body: (foldMap (Foldl.mk ∘ flip f) xs).get x

中文:
定义 foldl
  签名: (f : α -> β -> α) (x : α) (xs : t β)
  定义体: (foldMap (Foldl.mk ∘ flip f) xs).get x

Depends on / 依赖: Foldl.mk, foldMap
-/
def foldl (f : α -> β -> α) (x : α) (xs : t β) : α :=
  (foldMap (Foldl.mk ∘ flip f) xs).get x

/--
Definition of `foldr` / `foldr` 的定义

English:
definition foldr
  signature: (f : α -> β -> β) (x : β) (xs : t α)
  body: (foldMap (Foldr.mk ∘ f) xs).get x

中文:
定义 foldr
  签名: (f : α -> β -> β) (x : β) (xs : t α)
  定义体: (foldMap (Foldr.mk ∘ f) xs).get x

Depends on / 依赖: Foldr.mk, foldMap
-/
def foldr (f : α -> β -> β) (x : β) (xs : t α) : β :=
  (foldMap (Foldr.mk ∘ f) xs).get x

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: : t α -> List α
  body: List.reverse ∘ foldl (flip List.cons) []

中文:
定义 toList
  签名: : t α -> 列表 α
  定义体: List.reverse ∘ foldl (flip List.cons) []

Depends on / 依赖: List.cons, List.reverse, reverse
-/
def toList : t α -> List α :=
  List.reverse ∘ foldl (flip List.cons) []

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (xs : t α)
  body: down foldl (fun l _ => up <| l.down + 1) (up 0) xs

中文:
定义 length
  签名: (xs : t α)
  定义体: down foldl (fun l _ => up <| l.down + 1) (up 0) xs

Depends on / 依赖: l.down
-/
def length (xs : t α) : Nat :=
down foldl (fun l _ => up <| l.down + 1) (up 0) xs

variable {m : Type u -> Type u} [Monad m]

/--
Definition of `foldlm` / `foldlm` 的定义

English:
definition foldlm
  signature: (f : α -> β -> m α) (x : α) (xs : t β)
  body: (foldMap (foldlM.mk ∘ flip f) xs).get x

中文:
定义 foldlm
  签名: (f : α -> β -> m α) (x : α) (xs : t β)
  定义体: (foldMap (foldlM.mk ∘ flip f) xs).get x

Depends on / 依赖: foldMap, foldlM, foldlM.mk
-/
def foldlm (f : α -> β -> m α) (x : α) (xs : t β) : m α :=
  (foldMap (foldlM.mk ∘ flip f) xs).get x

/--
Definition of `foldrm` / `foldrm` 的定义

English:
definition foldrm
  signature: (f : α -> β -> m β) (x : β) (xs : t α)
  body: (foldMap (foldrM.mk ∘ f) xs).get x

中文:
定义 foldrm
  签名: (f : α -> β -> m β) (x : β) (xs : t α)
  定义体: (foldMap (foldrM.mk ∘ f) xs).get x

Depends on / 依赖: foldMap, foldrM, foldrM.mk
-/
def foldrm (f : α -> β -> m β) (x : β) (xs : t α) : m β :=
  (foldMap (foldrM.mk ∘ f) xs).get x

end Defs

section ApplicativeTransformation

variable {α β γ : Type u}

open Function hiding const

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapFold` / `mapFold` 的定义

English:
definition mapFold
  signature: [Monoid α] [Monoid β] (f : α ->* β)
  body: f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
  preserves_pure' := by intros; simp only [map_one, pure]

中文:
定义 mapFold
  签名: [幺半群 α] [幺半群 β] (f : α ->* β)
  定义体: f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
  preserves_pure' := by intros; simp only [map_one, pure]
-/
def mapFold [Monoid α] [Monoid β] (f : α ->* β) : ApplicativeTransformation (Const α) (Const β) where
  app _ := f
  preserves_seq' := by intros; simp only [Seq.seq, map_mul]
  preserves_pure' := by intros; simp only [map_one, pure]

/--
theorem `Free.map_eq_map` / 定理 `Free.map_eq_map`

English:
theorem Free.map_eq_map
  given: (f : α -> β) (xs : List α)
  proof: rfl

中文:
定理 自由.map_eq_map
  条件: (f : α -> β) (xs : 列表 α)
  证明: rfl
-/
theorem Free.map_eq_map (f : α -> β) (xs : List α) :
f < > xs = (FreeMonoid.toList (FreeMonoid.map f (FreeMonoid.ofList xs))) :=
  rfl

/--
theorem `foldl.unop_ofFreeMonoid` / 定理 `foldl.unop_ofFreeMonoid`

English:
theorem foldl.unop_ofFreeMonoid
  given: (f : β -> α -> β) (xs : FreeMonoid α) (a : β)
  proof: rfl

中文:
定理 foldl.unop_ofFreeMonoid
  条件: (f : β -> α -> β) (xs : 自由幺半群 α) (a : β)
  证明: rfl
-/
theorem foldl.unop_ofFreeMonoid (f : β -> α -> β) (xs : FreeMonoid α) (a : β) :
    ConcreteCategory.hom (unop (Foldl.ofFreeMonoid f xs)) a =
      List.foldl f a (FreeMonoid.toList xs) :=
  rfl

variable {t : Type u -> Type u} [Traversable t] [LawfulTraversable t]

open LawfulTraversable

set_option backward.isDefEq.respectTransparency false in
/--
theorem `foldMap_hom` / 定理 `foldMap_hom`

English:
theorem foldMap_hom
  given: [Monoid α] [Monoid β] (f : α ->* β) (g : γ -> α) (x : t γ)
  proof: calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl

中文:
定理 foldMap_hom
  条件: [幺半群 α] [幺半群 β] (f : α ->* β) (g : γ -> α) (x : t γ)
  证明: calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl

Depends on / 依赖: Const.mk, foldMap, mapFold, naturality, traverse
-/
theorem foldMap_hom [Monoid α] [Monoid β] (f : α ->* β) (g : γ -> α) (x : t γ) :
    f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (Const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (Const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ Const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl

/--
theorem `foldMap_hom_free` / 定理 `foldMap_hom_free`

English:
theorem foldMap_hom_free
  given: [Monoid β] (f : FreeMonoid α ->* β) (x : t α)
  proof: foldMap_hom f _ x

中文:
定理 foldMap_hom_free
  条件: [幺半群 β] (f : 自由幺半群 α ->* β) (x : t α)
  证明: foldMap_hom f _ x

Depends on / 依赖: foldMap_hom
-/
theorem foldMap_hom_free [Monoid β] (f : FreeMonoid α ->* β) (x : t α) :
    f (foldMap FreeMonoid.of x) = foldMap (f ∘ FreeMonoid.of) x :=
  foldMap_hom f _ x

end ApplicativeTransformation

section Equalities

open LawfulTraversable

open List (cons)

variable {α β γ : Type u}
variable {t : Type u -> Type u} [Traversable t] [LawfulTraversable t]

@[simp]
/--
theorem `foldl.ofFreeMonoid_comp_of` / 定理 `foldl.ofFreeMonoid_comp_of`

English:
theorem foldl.ofFreeMonoid_comp_of
  given: (f : α -> β -> α)
  proof: rfl

@[simp]

中文:
定理 foldl.ofFreeMonoid_comp_of
  条件: (f : α -> β -> α)
  证明: rfl

@[simp]
-/
theorem foldl.ofFreeMonoid_comp_of (f : α -> β -> α) :
    Foldl.ofFreeMonoid f ∘ FreeMonoid.of = Foldl.mk ∘ flip f :=
  rfl

@[simp]
/--
theorem `foldr.ofFreeMonoid_comp_of` / 定理 `foldr.ofFreeMonoid_comp_of`

English:
theorem foldr.ofFreeMonoid_comp_of
  given: (f : β -> α -> α)
  proof: rfl

中文:
定理 foldr.ofFreeMonoid_comp_of
  条件: (f : β -> α -> α)
  证明: rfl
-/
theorem foldr.ofFreeMonoid_comp_of (f : β -> α -> α) :
    Foldr.ofFreeMonoid f ∘ FreeMonoid.of = Foldr.mk ∘ f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `foldlm.ofFreeMonoid_comp_of` / 定理 `foldlm.ofFreeMonoid_comp_of`

English:
theorem foldlm.ofFreeMonoid_comp_of
  given: {m} [Monad m] [LawfulMonad m] (f : α -> β -> m α)
  proof: by
  ext1 x
  simp only [foldlM.ofFreeMonoid, Function.flip_def, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, FreeMonoid.toList_of, List.foldlM_cons, List.foldlM_nil, bind_pure,
    foldlM.mk, op_inj]
  rfl

中文:
定理 foldlm.ofFreeMonoid_comp_of
  条件: {m} [单子 m] [合法单子 m] (f : α -> β -> m α)
  证明: by
  ext1 x
  simp only [foldlM.ofFreeMonoid, Function.flip_def, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, FreeMonoid.toList_of, List.foldlM_cons, List.foldlM_nil, bind_pure,
    foldlM.mk, op_inj]
  rfl

Depends on / 依赖: FreeMonoid, FreeMonoid.toList_of, Function, Function.comp_apply, Function.flip_def, List.foldlM_cons, List.foldlM_nil, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, bind_pure, coe_mk, comp_apply, flip_def, foldlM, foldlM.mk, foldlM.ofFreeMonoid, foldlM_cons, foldlM_nil
-/
theorem foldlm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : α -> β -> m α) :
    foldlM.ofFreeMonoid f ∘ FreeMonoid.of = foldlM.mk ∘ flip f := by
  ext1 x
  simp only [foldlM.ofFreeMonoid, Function.flip_def, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, FreeMonoid.toList_of, List.foldlM_cons, List.foldlM_nil, bind_pure,
    foldlM.mk, op_inj]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `foldrm.ofFreeMonoid_comp_of` / 定理 `foldrm.ofFreeMonoid_comp_of`

English:
theorem foldrm.ofFreeMonoid_comp_of
  given: {m} [Monad m] [LawfulMonad m] (f : β -> α -> m α)
  proof: by
  ext
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, Function.flip_def]

中文:
定理 foldrm.ofFreeMonoid_comp_of
  条件: {m} [单子 m] [合法单子 m] (f : β -> α -> m α)
  证明: by
  ext
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, Function.flip_def]

Depends on / 依赖: Function, Function.flip_def, flip_def, foldrM, foldrM.mk, foldrM.ofFreeMonoid, ofFreeMonoid
-/
theorem foldrm.ofFreeMonoid_comp_of {m} [Monad m] [LawfulMonad m] (f : β -> α -> m α) :
    foldrM.ofFreeMonoid f ∘ FreeMonoid.of = foldrM.mk ∘ f := by
  ext
  simp [(· ∘ ·), foldrM.ofFreeMonoid, foldrM.mk, Function.flip_def]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toList_spec` / 定理 `toList_spec`

English:
theorem toList_spec
  given: (xs : t α)
  statement: toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs)
  proof: Eq.symm
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

中文:
定理 toList_spec
  条件: (xs : t α)
  结论: toList xs = 自由幺半群.toList (foldMap 自由幺半群.of xs)
  证明: Eq.symm
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

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Eq.symm, Foldl.ofFreeMonoid, FreeMonoid, FreeMonoid.of, FreeMonoid.reverse_reverse, FreeMonoid.toList, Function, Function.flip_def, List.foldr, List.foldr_reverse, flip_def, foldMap, foldMap_hom_free, foldr_reverse, ofFreeMonoid, reverse, reverse.reverse, reverse_reverse
-/
theorem toList_spec (xs : t α) : toList xs = FreeMonoid.toList (foldMap FreeMonoid.of xs) :=
Eq.symm
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
/--
theorem `foldMap_map` / 定理 `foldMap_map`

English:
theorem foldMap_map
  given: [Monoid γ] (f : α -> β) (g : β -> γ) (xs : t α)
  proof: by
  simp only [foldMap, traverse_map, Function.comp_def]

中文:
定理 foldMap_map
  条件: [幺半群 γ] (f : α -> β) (g : β -> γ) (xs : t α)
  证明: by
  simp only [foldMap, traverse_map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, foldMap, traverse_map
-/
theorem foldMap_map [Monoid γ] (f : α -> β) (g : β -> γ) (xs : t α) :
    foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by
  simp only [foldMap, traverse_map, Function.comp_def]

/--
theorem `foldl_toList` / 定理 `foldl_toList`

English:
theorem foldl_toList
  given: (f : α -> β -> α) (xs : t β) (x : α)
  proof: by
  rw [← FreeMonoid.toList_ofList (toList xs)]; rw [← foldl.unop_ofFreeMonoid]
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]

中文:
定理 foldl_toList
  条件: (f : α -> β -> α) (xs : t β) (x : α)
  证明: by
  rw [← FreeMonoid.toList_ofList (toList xs)]; rw [← foldl.unop_ofFreeMonoid]
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]

Depends on / 依赖: Foldl.get, FreeMonoid, FreeMonoid.ofList_toList, FreeMonoid.toList_ofList, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, foldl.unop_ofFreeMonoid, ofFreeMonoid_comp_of, ofList_toList, toList, toList_ofList, toList_spec, unop_ofFreeMonoid
-/
theorem foldl_toList (f : α -> β -> α) (xs : t β) (x : α) :
    foldl f x xs = List.foldl f x (toList xs) := by
  rw [← FreeMonoid.toList_ofList (toList xs)]; rw [← foldl.unop_ofFreeMonoid]
  simp only [foldl, toList_spec, foldMap_hom_free, foldl.ofFreeMonoid_comp_of, Foldl.get,
    FreeMonoid.ofList_toList]

/--
theorem `foldr_toList` / 定理 `foldr_toList`

English:
theorem foldr_toList
  given: (f : α -> β -> β) (xs : t α) (x : β)
  proof: by
  change _ = (Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs)).hom _
  rw [toList_spec]; rw [foldr]; rw [Foldr.get]; rw [FreeMonoid.ofList_toList]; rw [foldMap_hom_free]; rw [foldr.ofFreeMonoid_comp_of]

中文:
定理 foldr_toList
  条件: (f : α -> β -> β) (xs : t α) (x : β)
  证明: by
  change _ = (Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs)).hom _
  rw [toList_spec]; rw [foldr]; rw [Foldr.get]; rw [FreeMonoid.ofList_toList]; rw [foldMap_hom_free]; rw [foldr.ofFreeMonoid_comp_of]

Depends on / 依赖: Foldr.get, Foldr.ofFreeMonoid, FreeMonoid, FreeMonoid.ofList, FreeMonoid.ofList_toList, foldMap_hom_free, foldr.ofFreeMonoid_comp_of, ofFreeMonoid, ofFreeMonoid_comp_of, ofList, ofList_toList, toList, toList_spec
-/
theorem foldr_toList (f : α -> β -> β) (xs : t α) (x : β) :
    foldr f x xs = List.foldr f x (toList xs) := by
  change _ = (Foldr.ofFreeMonoid _ (FreeMonoid.ofList <| toList xs)).hom _
  rw [toList_spec]; rw [foldr]; rw [Foldr.get]; rw [FreeMonoid.ofList_toList]; rw [foldMap_hom_free]; rw [foldr.ofFreeMonoid_comp_of]

/--
theorem `toList_map` / 定理 `toList_map`

English:
theorem toList_map
  given: (f : α -> β) (xs : t α)
  statement: toList (f <$> xs) = f < > toList xs
  proof: by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, Function.comp_def]

@[simp]

中文:
定理 toList_map
  条件: (f : α -> β) (xs : t α)
  结论: toList (f <$> xs) = f < > toList xs
  证明: by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, Function.comp_def]

@[simp]

Depends on / 依赖: Free.map_eq_map, FreeMonoid, FreeMonoid.map_of, FreeMonoid.ofList_toList, Function, Function.comp_def, comp_def, foldMap_hom, foldMap_map, map_eq_map, map_of, ofList_toList, toList_spec
-/
theorem toList_map (f : α -> β) (xs : t α) : toList (f <$> xs) = f < > toList xs := by
  simp only [toList_spec, Free.map_eq_map, foldMap_hom, foldMap_map, FreeMonoid.ofList_toList,
    FreeMonoid.map_of, Function.comp_def]

@[simp]
/--
theorem `foldl_map` / 定理 `foldl_map`

English:
theorem foldl_map
  given: (g : β -> γ) (f : α -> γ -> α) (a : α) (l : t β)
  proof: by
  simp only [foldl, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]

中文:
定理 foldl_map
  条件: (g : β -> γ) (f : α -> γ -> α) (a : α) (l : t β)
  证明: by
  simp only [foldl, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Function.flip_def, comp_def, flip_def, foldMap_map
-/
theorem foldl_map (g : β -> γ) (f : α -> γ -> α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  simp only [foldl, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]
/--
theorem `foldr_map` / 定理 `foldr_map`

English:
theorem foldr_map
  given: (g : β -> γ) (f : γ -> α -> α) (a : α) (l : t β)
  proof: by
  simp only [foldr, foldMap_map, Function.comp_def]

@[simp]

中文:
定理 foldr_map
  条件: (g : β -> γ) (f : γ -> α -> α) (a : α) (l : t β)
  证明: by
  simp only [foldr, foldMap_map, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, comp_def, foldMap_map
-/
theorem foldr_map (g : β -> γ) (f : γ -> α -> α) (a : α) (l : t β) :
    foldr f a (g <$> l) = foldr (f ∘ g) a l := by
  simp only [foldr, foldMap_map, Function.comp_def]

@[simp]
/--
theorem `toList_eq_self` / 定理 `toList_eq_self`

English:
theorem toList_eq_self
  given: {xs : List α}
  statement: toList xs = xs
  proof: by
  simp only [toList_spec, foldMap, traverse]
  induction xs with
  | nil => rfl
  | cons _ _ ih => (conv_rhs => rw [← ih]); rfl

中文:
定理 toList_eq_self
  条件: {xs : 列表 α}
  结论: toList xs = xs
  证明: by
  simp only [toList_spec, foldMap, traverse]
  induction xs with
  | nil => rfl
  | cons _ _ ih => (conv_rhs => rw [← ih]); rfl

Depends on / 依赖: conv_rhs, foldMap, toList_spec, traverse
-/
theorem toList_eq_self {xs : List α} : toList xs = xs := by
  simp only [toList_spec, foldMap, traverse]
  induction xs with
  | nil => rfl
  | cons _ _ ih => (conv_rhs => rw [← ih]); rfl

/--
theorem `length_toList` / 定理 `length_toList`

English:
theorem length_toList
  given: {xs : t α}
  statement: length xs = List.length (toList xs)
  proof: by
  unfold length
  rw [foldl_toList]
  generalize toList xs = ys
  rw [← Nat.add_zero ys.length]
  generalize 0 = n
  induction ys generalizing n with
  | nil => simp
  | cons _ _ ih => simp +arith [ih]

中文:
定理 length_toList
  条件: {xs : t α}
  结论: length xs = 列表.length (toList xs)
  证明: by
  unfold length
  rw [foldl_toList]
  generalize toList xs = ys
  rw [← Nat.add_zero ys.length]
  generalize 0 = n
  induction ys generalizing n with
  | nil => simp
  | cons _ _ ih => simp +arith [ih]

Depends on / 依赖: Nat.add_zero, add_zero, foldl_toList, generalize, generalizing, length, toList, ys.length
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

variable {m : Type u -> Type u} [Monad m] [LawfulMonad m]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `foldlm_toList` / 定理 `foldlm_toList`

English:
theorem foldlm_toList
  given: {f : α -> β -> m α} {x : α} {xs : t β}
  proof: calc foldlm f x xs
    _ = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]

中文:
定理 foldlm_toList
  条件: {f : α -> β -> m α} {x : α} {xs : t β}
  证明: calc foldlm f x xs
    _ = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]

Depends on / 依赖: FreeMonoid, FreeMonoid.ofList, FreeMonoid.ofList_toList, List.foldlM, foldMap_hom_free, foldlM, foldlM.get, foldlM.ofFreeMonoid, foldlm, foldlm.ofFreeMonoid_comp_of, ofFreeMonoid, ofFreeMonoid_comp_of, ofList, ofList_toList, toList, toList_spec, unop_op
-/
theorem foldlm_toList {f : α -> β -> m α} {x : α} {xs : t β} :
    foldlm f x xs = List.foldlM f x (toList xs) :=
  calc foldlm f x xs
    _ = unop (foldlM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs)) x := by
      simp only [foldlm, toList_spec, foldMap_hom_free (foldlM.ofFreeMonoid f),
        foldlm.ofFreeMonoid_comp_of, foldlM.get, FreeMonoid.ofList_toList]
    _ = List.foldlM f x (toList xs) := by simp [foldlM.ofFreeMonoid, unop_op, flip]

/--
theorem `foldrm_toList` / 定理 `foldrm_toList`

English:
theorem foldrm_toList
  given: (f : α -> β -> m β) (x : β) (xs : t α)
  proof: by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]

@[simp]

中文:
定理 foldrm_toList
  条件: (f : α -> β -> m β) (x : β) (xs : t α)
  证明: by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]

@[simp]

Depends on / 依赖: FreeMonoid, FreeMonoid.ofList, FreeMonoid.ofList_toList, foldMap_hom_free, foldrM, foldrM.get, foldrM.ofFreeMonoid, foldrm, foldrm.ofFreeMonoid_comp_of, ofFreeMonoid, ofFreeMonoid_comp_of, ofList, ofList_toList, toList, toList_spec
-/
theorem foldrm_toList (f : α -> β -> m β) (x : β) (xs : t α) :
    foldrm f x xs = List.foldrM f x (toList xs) := by
  change _ = foldrM.ofFreeMonoid f (FreeMonoid.ofList <| toList xs) x
  simp only [foldrm, toList_spec, foldMap_hom_free (foldrM.ofFreeMonoid f),
    foldrm.ofFreeMonoid_comp_of, foldrM.get, FreeMonoid.ofList_toList]

@[simp]
/--
theorem `foldlm_map` / 定理 `foldlm_map`

English:
theorem foldlm_map
  given: (g : β -> γ) (f : α -> γ -> m α) (a : α) (l : t β)
  proof: by
  simp only [foldlm, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]

中文:
定理 foldlm_map
  条件: (g : β -> γ) (f : α -> γ -> m α) (a : α) (l : t β)
  证明: by
  simp only [foldlm, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Function.flip_def, comp_def, flip_def, foldMap_map, foldlm
-/
theorem foldlm_map (g : β -> γ) (f : α -> γ -> m α) (a : α) (l : t β) :
    foldlm f a (g <$> l) = foldlm (fun x y => f x (g y)) a l := by
  simp only [foldlm, foldMap_map, Function.comp_def, Function.flip_def]

@[simp]
/--
theorem `foldrm_map` / 定理 `foldrm_map`

English:
theorem foldrm_map
  given: (g : β -> γ) (f : γ -> α -> m α) (a : α) (l : t β)
  proof: by
  simp only [foldrm, foldMap_map, Function.comp_def]

中文:
定理 foldrm_map
  条件: (g : β -> γ) (f : γ -> α -> m α) (a : α) (l : t β)
  证明: by
  simp only [foldrm, foldMap_map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, foldMap_map, foldrm
-/
theorem foldrm_map (g : β -> γ) (f : γ -> α -> m α) (a : α) (l : t β) :
    foldrm f a (g <$> l) = foldrm (f ∘ g) a l := by
  simp only [foldrm, foldMap_map, Function.comp_def]

end Equalities

end Traversable
