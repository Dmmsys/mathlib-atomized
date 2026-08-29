/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Unbounded lattice homomorphisms

This file defines unbounded lattice homomorphisms. _Bounded_ lattice homomorphisms are defined in
`Mathlib/Order/Hom/BoundedLattice.lean`.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupHom`: Maps which preserve `⊔`.
* `InfHom`: Maps which preserve `⊓`.
* `LatticeHom`: Lattice homomorphisms. Maps which preserve `⊔` and `⊓`.

## Typeclasses

* `SupHomClass`
* `InfHomClass`
* `LatticeHomClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/--
Definition of `SupHom` / `SupHom` 的定义

English:
structure SupHom
  parameters: (α β : Type*) [Max α] [Max β]
  axioms and operations (2):
    - toFun : α -> β
    - map_sup'((a b : α)) : toFun (a ⊔ b) = toFun a ⊔ toFun b

中文:
结构 SupHom
  参数: (α β : 类型) [Max α] [Max β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_sup'((a b : α)) : toFun (a ⊔ b) = toFun a ⊔ toFun b
-/
structure SupHom (α β : Type*) [Max α] [Max β] where
  /-- The underlying function of a `SupHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α -> β
  /-- A `SupHom` preserves suprema.

  Do not use this directly. Use `map_sup` instead. -/
  map_sup' (a b : α) : toFun (a ⊔ b) = toFun a ⊔ toFun b

/-- The type of `⊓`-preserving functions from `α` to `β`. -/
@[to_dual existing]
/--
Definition of `InfHom` / `InfHom` 的定义

English:
structure InfHom
  parameters: (α β : Type*) [Min α] [Min β]
  axioms and operations (2):
    - toFun : α -> β
    - map_inf'((a b : α)) : toFun (a ⊓ b) = toFun a ⊓ toFun b

中文:
结构 InfHom
  参数: (α β : 类型) [Min α] [Min β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_inf'((a b : α)) : toFun (a ⊓ b) = toFun a ⊓ toFun b
-/
structure InfHom (α β : Type*) [Min α] [Min β] where
  /-- The underlying function of an `InfHom`.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α -> β
  /-- An `InfHom` preserves infima.

  Do not use this directly. Use `map_inf` instead. -/
  map_inf' (a b : α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

/--
Definition of `LatticeHom` / `LatticeHom` 的定义

English:
structure LatticeHom
  parameters: (α β : Type*) [Lattice α] [Lattice β]
  extends: SupHom α β, InfHom α β
  (no additional axioms)

中文:
结构 LatticeHom
  参数: (α β : 类型) [Lattice α] [Lattice β]
  继承: SupHom α β, InfHom α β
  (无附加公理)
-/
structure LatticeHom (α β : Type*) [Lattice α] [Lattice β] extends SupHom α β, InfHom α β where

attribute [nolint docBlame] LatticeHom.toInfHom

attribute [to_dual existing] LatticeHom.toInfHom

section

/--
Definition of `SupHomClass` / `SupHomClass` 的定义

English:
class SupHomClass
  parameters: (F α β : Type*) [Max α] [Max β] [FunLike F α β]
  axioms and operations (1):
    - map_sup((f : F) (a b : α)) : f (a ⊔ b) = f a ⊔ f b

中文:
类 SupHomClass
  参数: (F α β : 类型) [Max α] [Max β] [FunLike F α β]
  公理与运算 (1 个):
    - map_sup((f : F) (a b : α)) : f (a ⊔ b) = f a ⊔ f b
-/
class SupHomClass (F α β : Type*) [Max α] [Max β] [FunLike F α β] : Prop where
  /-- A `SupHomClass` morphism preserves suprema. -/
  map_sup (f : F) (a b : α) : f (a ⊔ b) = f a ⊔ f b

/-- `InfHomClass F α β` states that `F` is a type of `⊓`-preserving morphisms.

You should extend this class when you extend `InfHom`. -/
@[to_dual existing]
/--
Definition of `InfHomClass` / `InfHomClass` 的定义

English:
class InfHomClass
  parameters: (F α β : Type*) [Min α] [Min β] [FunLike F α β]
  axioms and operations (1):
    - map_inf((f : F) (a b : α)) : f (a ⊓ b) = f a ⊓ f b

中文:
类 InfHomClass
  参数: (F α β : 类型) [Min α] [Min β] [FunLike F α β]
  公理与运算 (1 个):
    - map_inf((f : F) (a b : α)) : f (a ⊓ b) = f a ⊓ f b

Depends on / 依赖: FiniteEtale, FiniteEtale.equivOfIsSepClosed, equivOfIsSepClosed, isEquivalence_functor
-/
class InfHomClass (F α β : Type*) [Min α] [Min β] [FunLike F α β] : Prop where
  /-- An `InfHomClass` morphism preserves infima. -/
  map_inf (f : F) (a b : α) : f (a ⊓ b) = f a ⊓ f b

/--
Definition of `LatticeHomClass` / `LatticeHomClass` 的定义

English:
class LatticeHomClass
  parameters: (F α β : Type*) [Lattice α] [Lattice β] [FunLike F α β]
  extends: SupHomClass F α β, InfHomClass F α β
  (no additional axioms)

中文:
类 LatticeHomClass
  参数: (F α β : 类型) [Lattice α] [Lattice β] [FunLike F α β]
  继承: SupHomClass F α β, InfHomClass F α β
  (无附加公理)

Depends on / 依赖: FiniteEtale, FiniteEtale.fiberIsoFiniteSpec, Functor, Functor.isEquivalence_of_iso, fiberIsoFiniteSpec, isEquivalence_of_iso
-/
class LatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [FunLike F α β] : Prop
  extends SupHomClass F α β, InfHomClass F α β where

attribute [to_dual existing] LatticeHomClass.toInfHomClass

end

export SupHomClass (map_sup)

export InfHomClass (map_inf)

attribute [simp] map_sup map_inf

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) SupHomClass.toOrderHomClass [SemilatticeSup α] [SemilatticeSup β]
    [SupHomClass F α β] : OrderHomClass F α β where
  map_rel := fun f a b h => by rw [← sup_eq_right, ← map_sup, sup_eq_right.2 h]

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.toSupHomClass [SemilatticeSup α] [SemilatticeSup β]
    [OrderIsoClass F α β] : SupHomClass F α β where
  map_sup := fun f a b =>
    eq_of_forall_ge_iff fun c => by simp only [← le_map_inv_iff, sup_le_iff]

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toLatticeHomClass [Lattice α] [Lattice β]
    [OrderIsoClass F α β] : LatticeHomClass F α β where

end Equiv

section OrderEmbedding

variable [FunLike F α β]

/-- We can regard an injective map preserving binary infima as an order embedding. -/
@[simps! apply]
/--
Definition of `orderEmbeddingOfInjective` / `orderEmbeddingOfInjective` 的定义

English:
definition orderEmbeddingOfInjective
  signature: [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
  body: OrderEmbedding.ofMapLEIff f (fun x y => by
    refine ⟨fun h => ?_, fun h => OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

中文:
定义 orderEmbeddingOfInjective
  签名: [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
  定义体: OrderEmbedding.ofMapLEIff f (fun x y => by
    refine ⟨fun h => ?_, fun h => OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofMapLEIff, OrderHomClass, OrderHomClass.mono, eq_iff, hf.eq_iff, inf_eq_left, map_inf, ofMapLEIff
-/
def orderEmbeddingOfInjective [SemilatticeInf α] [SemilatticeInf β] (f : F) [InfHomClass F α β]
    (hf : Injective f) : α ↪o β :=
  OrderEmbedding.ofMapLEIff f (fun x y => by
    refine ⟨fun h => ?_, fun h => OrderHomClass.mono f h⟩
    rwa [← inf_eq_left, ← hf.eq_iff, map_inf, inf_eq_left])

end OrderEmbedding

variable [FunLike F α β]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Max
  signature: α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β)
  body: ⟨fun f => ⟨f, map_sup f⟩⟩

中文:
实例 [Max
  签名: α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β)
  定义体: ⟨fun f => ⟨f, map_sup f⟩⟩

Depends on / 依赖: map_sup
-/
instance [Max α] [Max β] [SupHomClass F α β] : CoeTC F (SupHom α β) :=
  ⟨fun f => ⟨f, map_sup f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β)
  body: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

中文:
实例 [Lattice
  签名: α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β)
  定义体: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

Depends on / 依赖: map_inf, map_sup
-/
instance [Lattice α] [Lattice β] [LatticeHomClass F α β] : CoeTC F (LatticeHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f }⟩

/-! ### Supremum homomorphisms -/

namespace SupHom

variable [Max α]

section Sup

variable [Max β] [Max γ] [Max δ]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (SupHom α β) α β
  body: SupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

中文:
实例 :
  签名: FunLike (SupHom α β) α β
  定义体: SupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

Depends on / 依赖: SupHom, SupHom.toFun
-/
instance : FunLike (SupHom α β) α β where
  coe := SupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupHomClass (SupHom α β) α β
  body: SupHom.map_sup'

中文:
实例 :
  签名: SupHomClass (SupHom α β) α β
  定义体: SupHom.map_sup'

Depends on / 依赖: SupHom, SupHom.map_sup, map_sup
-/
instance : SupHomClass (SupHom α β) α β where
  map_sup := SupHom.map_sup'

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : SupHom α β)
  statement: f.toFun = f
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
引理 toFun_eq_coe
  条件: (f : SupHom α β)
  结论: f.toFun = f
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
@[to_dual (attr := simp)] lemma toFun_eq_coe (f : SupHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : α -> β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[to_dual (attr := ext)]

中文:
引理 coe_mk
  条件: (f : α -> β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[to_dual (attr := ext)]
-/
lemma coe_mk (f : α -> β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : SupHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : SupHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : SupHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of an `InfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_sup' := h.symm ▸ f.map_sup'

@[to_dual (attr := simp)]

中文:
定义 copy
  签名: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_sup' := h.symm ▸ f.map_sup'

@[to_dual (attr := simp)]
-/
protected def copy (f : SupHom α β) (f' : α -> β) (h : f' = f) : SupHom α β where
  toFun := f'
  map_sup' := h.symm ▸ f.map_sup'

@[to_dual (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

@[to_dual]

中文:
定理 coe_copy
  条件: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

@[to_dual]
-/
theorem coe_copy (f : SupHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : SupHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : SupHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupHom`. -/
@[to_dual /-- `id` as an `InfHom`. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : SupHom α α
  body: ⟨id, fun _ _ => rfl⟩

@[to_dual]

中文:
定义 id
  签名: : SupHom α α
  定义体: ⟨id, fun _ _ => rfl⟩

@[to_dual]
-/
protected def id : SupHom α α :=
  ⟨id, fun _ _ => rfl⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SupHom α α)
  body: ⟨SupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

中文:
实例 :
  签名: Inhabited (SupHom α α)
  定义体: ⟨SupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: SupHom, SupHom.id
-/
instance : Inhabited (SupHom α α) :=
  ⟨SupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(SupHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(SupHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(SupHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: SupHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: SupHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : SupHom.id α a = a :=
  rfl

/-- Composition of `SupHom`s as a `SupHom`. -/
@[to_dual /-- Composition of `InfHom`s as an `InfHom`. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : SupHom β γ) (g : SupHom α β)
  body: f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[to_dual (attr := simp)]

中文:
定义 comp
  签名: (f : SupHom β γ) (g : SupHom α β)
  定义体: f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[to_dual (attr := simp)]
-/
def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
  toFun := f ∘ g
  map_sup' a b := by rw [comp_apply, map_sup, map_sup]; rfl

@[to_dual (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : SupHom β γ) (g : SupHom α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp
  条件: (f : SupHom β γ) (g : SupHom α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp (f : SupHom β γ) (g : SupHom α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : SupHom β γ) (g : SupHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_apply
  条件: (f : SupHom β γ) (g : SupHom α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_apply (f : SupHom β γ) (g : SupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β)
  证明: rfl
-/
theorem comp_assoc (f : SupHom γ δ) (g : SupHom β γ) (h : SupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : SupHom α β)
  statement: f.comp (SupHom.id α) = f
  proof: rfl

中文:
定理 comp_id
  条件: (f : SupHom α β)
  结论: f.comp (SupHom.id α) = f
  证明: rfl
-/
@[to_dual (attr := simp)] theorem comp_id (f : SupHom α β) : f.comp (SupHom.id α) = f := rfl

/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : SupHom α β)
  statement: (SupHom.id β).comp f = f
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 id_comp
  条件: (f : SupHom α β)
  结论: (SupHom.id β).comp f = f
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] theorem id_comp (f : SupHom α β) : (SupHom.id β).comp f = f := rfl

@[to_dual (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f)
  proof: ⟨fun h => SupHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f)
  证明: ⟨fun h => SupHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, SupHom, SupHom.ext, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : SupHom β γ} {f : SupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => SupHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g)
  proof: ⟨fun h => SupHom.ext fun a => hg by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g)
  证明: ⟨fun h => SupHom.ext fun a => hg by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

Depends on / 依赖: SupHom, SupHom.comp_apply, SupHom.ext, comp_apply, congr_arg
-/
theorem cancel_left {g : SupHom β γ} {f₁ f₂ : SupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => SupHom.ext fun a => hg by rw [← SupHom.comp_apply, h, SupHom.comp_apply],
    congr_arg _⟩

end Sup

variable (α) [SemilatticeSup β]

/-- The constant function as a `SupHom`. -/
@[to_dual /-- The constant function as an `InfHom`. -/]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (b : β)
  body: ⟨fun _ => b, fun _ _ => (sup_idem _).symm⟩

@[to_dual (attr := simp)]

中文:
定义 const
  签名: (b : β)
  定义体: ⟨fun _ => b, fun _ _ => (sup_idem _).symm⟩

@[to_dual (attr := simp)]

Depends on / 依赖: sup_idem
-/
def const (b : β) : SupHom α β := ⟨fun _ => b, fun _ _ => (sup_idem _).symm⟩

@[to_dual (attr := simp)]
/--
theorem `coe_const` / 定理 `coe_const`

English:
theorem coe_const
  given: (b : β)
  statement: ⇑(const α b) = Function.const α b
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_const
  条件: (b : β)
  结论: ⇑(const α b) = Function.const α b
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (b : β) (a : α)
  statement: const α b a = b
  proof: rfl

中文:
定理 const_apply
  条件: (b : β) (a : α)
  结论: const α b a = b
  证明: rfl
-/
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl

variable {α}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (SupHom α β)
  body: ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply]; rw [map_sup]; rw [map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

@[to_dual]

中文:
实例 :
  签名: Max (SupHom α β)
  定义体: ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply]; rw [map_sup]; rw [map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

@[to_dual]

Depends on / 依赖: Pi.sup_apply, map_sup, sup_apply, sup_sup_sup_comm
-/
instance : Max (SupHom α β) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun a b => by
      rw [Pi.sup_apply]; rw [map_sup]; rw [map_sup]
      exact sup_sup_sup_comm _ _ _ _⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SupHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

中文:
实例 :
  签名: PartialOrder (SupHom α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (SupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (SupHom α β)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]

中文:
实例 :
  签名: SemilatticeSup (SupHom α β)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, semilatticeSup
-/
instance : SemilatticeSup (SupHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Bot
  signature: β] : Bot (SupHom α β)
  body: ⟨SupHom.const α ⊥⟩

@[to_dual]

中文:
实例 [Bot
  签名: β] : Bot (SupHom α β)
  定义体: ⟨SupHom.const α ⊥⟩

@[to_dual]

Depends on / 依赖: SupHom, SupHom.const
-/
instance [Bot β] : Bot (SupHom α β) :=
  ⟨SupHom.const α ⊥⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Top
  signature: β] : Top (SupHom α β)
  body: ⟨SupHom.const α ⊤⟩

@[to_dual]

中文:
实例 [Top
  签名: β] : Top (SupHom α β)
  定义体: ⟨SupHom.const α ⊤⟩

@[to_dual]

Depends on / 依赖: SupHom, SupHom.const
-/
instance [Top β] : Top (SupHom α β) :=
  ⟨SupHom.const α ⊤⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderBot
  signature: β] : OrderBot (SupHom α β)
  body: OrderBot.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]

中文:
实例 [OrderBot
  签名: β] : OrderBot (SupHom α β)
  定义体: OrderBot.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]

Depends on / 依赖: OrderBot, OrderBot.lift
-/
instance [OrderBot β] : OrderBot (SupHom α β) :=
  OrderBot.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OrderTop
  signature: β] : OrderTop (SupHom α β)
  body: OrderTop.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]

中文:
实例 [OrderTop
  签名: β] : OrderTop (SupHom α β)
  定义体: OrderTop.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]

Depends on / 依赖: OrderTop, OrderTop.lift
-/
instance [OrderTop β] : OrderTop (SupHom α β) :=
  OrderTop.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BoundedOrder
  signature: β] : BoundedOrder (SupHom α β)
  body: BoundedOrder.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl rfl

@[to_dual (attr := simp)]

中文:
实例 [BoundedOrder
  签名: β] : BoundedOrder (SupHom α β)
  定义体: BoundedOrder.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl rfl

@[to_dual (attr := simp)]

Depends on / 依赖: BoundedOrder, BoundedOrder.lift
-/
instance [BoundedOrder β] : BoundedOrder (SupHom α β) :=
  BoundedOrder.lift ((↑) : _ -> α -> β) (fun _ _ => id) rfl rfl

@[to_dual (attr := simp)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (f g : SupHom α β)
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_sup
  条件: (f g : SupHom α β)
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_sup (f g : SupHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  given: [Bot β]
  statement: ⇑(⊥ : SupHom α β) = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_bot
  条件: [Bot β]
  结论: ⇑(⊥ : SupHom α β) = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_bot [Bot β] : ⇑(⊥ : SupHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  given: [Top β]
  statement: ⇑(⊤ : SupHom α β) = ⊤
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_top
  条件: [Top β]
  结论: ⇑(⊤ : SupHom α β) = ⊤
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_top [Top β] : ⇑(⊤ : SupHom α β) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (f g : SupHom α β) (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 sup_apply
  条件: (f g : SupHom α β) (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem sup_apply (f g : SupHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: [Bot β] (a : α)
  statement: (⊥ : SupHom α β) a = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 bot_apply
  条件: [Bot β] (a : α)
  结论: (⊥ : SupHom α β) a = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem bot_apply [Bot β] (a : α) : (⊥ : SupHom α β) a = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `top_apply` / 定理 `top_apply`

English:
theorem top_apply
  given: [Top β] (a : α)
  statement: (⊤ : SupHom α β) a = ⊤
  proof: rfl

@[to_dual (attr := simp, gcongr) (reorder := toFun₁ toFun₂, map_sup₁ map_sup₂)
  (rename := toFun₁ ↔ toFun₂, map_sup₁ -> map_inf₂, map_sup₂ -> map_inf₁)]

中文:
定理 top_apply
  条件: [Top β] (a : α)
  结论: (⊤ : SupHom α β) a = ⊤
  证明: rfl

@[to_dual (attr := simp, gcongr) (reorder := toFun₁ toFun₂, map_sup₁ map_sup₂)
  (rename := toFun₁ ↔ toFun₂, map_sup₁ -> map_inf₂, map_sup₂ -> map_inf₁)]
-/
theorem top_apply [Top β] (a : α) : (⊤ : SupHom α β) a = ⊤ :=
  rfl

@[to_dual (attr := simp, gcongr) (reorder := toFun₁ toFun₂, map_sup₁ map_sup₂)
  (rename := toFun₁ ↔ toFun₂, map_sup₁ -> map_inf₂, map_sup₂ -> map_inf₁)]
/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  given: (toFun₁ toFun₂ : α -> β) (map_sup₁ map_sup₂)
  proof: .rfl

中文:
引理 mk_le_mk
  条件: (toFun₁ toFun₂ : α -> β) (map_sup₁ map_sup₂)
  证明: .rfl
-/
lemma mk_le_mk (toFun₁ toFun₂ : α -> β) (map_sup₁ map_sup₂) :
    mk toFun₁ map_sup₁ <= mk toFun₂ map_sup₂ ↔ toFun₁ <= toFun₂ := .rfl

/-- `Subtype.val` as a `SupHom`. -/
@[to_dual (rename := Psup -> Pinf) /-- `Subtype.val` as an `InfHom`. -/]
/--
Definition of `subtypeVal` / `subtypeVal` 的定义

English:
definition subtypeVal
  signature: {P : β -> Prop}
  body: Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

@[to_dual (attr := simp) (rename := Psup -> Pinf)]

中文:
定义 subtypeVal
  签名: {P : β -> 命题}
  定义体: Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

@[to_dual (attr := simp) (rename := Psup -> Pinf)]

Depends on / 依赖: Subtype, Subtype.semilatticeSup, semilatticeSup
-/
def subtypeVal {P : β -> Prop}
    (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) :
    letI := Subtype.semilatticeSup Psup
    SupHom {x : β // P x} β :=
  letI := Subtype.semilatticeSup Psup
  .mk Subtype.val (by simp)

@[to_dual (attr := simp) (rename := Psup -> Pinf)]
/--
lemma `subtypeVal_apply` / 引理 `subtypeVal_apply`

English:
lemma subtypeVal_apply
  statement: {P : β -> Prop}
  proof: rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]

中文:
引理 subtypeVal_apply
  结论: {P : β -> 命题}
  证明: rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]
-/
lemma subtypeVal_apply {P : β -> Prop}
    (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Psup x = x := rfl

@[to_dual (attr := simp) (rename := Psup -> Pinf)]
/--
lemma `subtypeVal_coe` / 引理 `subtypeVal_coe`

English:
lemma subtypeVal_coe
  statement: {P : β -> Prop}
  proof: rfl

中文:
引理 subtypeVal_coe
  结论: {P : β -> 命题}
  证明: rfl
-/
lemma subtypeVal_coe {P : β -> Prop}
    (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) :
    ⇑(subtypeVal Psup) = Subtype.val := rfl

end SupHom

/-! ### Lattice homomorphisms -/


namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (LatticeHom α β) α β
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

中文:
实例 :
  签名: FunLike (LatticeHom α β) α β
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (LatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LatticeHomClass (LatticeHom α β) α β
  body: f.map_sup'
  map_inf f := f.map_inf'

中文:
实例 :
  签名: LatticeHomClass (LatticeHom α β) α β
  定义体: f.map_sup'
  map_inf f := f.map_inf'

Depends on / 依赖: f.map_sup, map_sup
-/
instance : LatticeHomClass (LatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : LatticeHom α β)
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (f : LatticeHom α β)
  结论: f.toFun = f
  证明: rfl
-/
lemma toFun_eq_coe (f : LatticeHom α β) : f.toFun = f := rfl

/--
lemma `coe_toSupHom` / 引理 `coe_toSupHom`

English:
lemma coe_toSupHom
  given: (f : LatticeHom α β)
  statement: ⇑f.toSupHom = f
  proof: rfl

中文:
引理 coe_toSupHom
  条件: (f : LatticeHom α β)
  结论: ⇑f.toSupHom = f
  证明: rfl
-/
@[to_dual (attr := simp)] lemma coe_toSupHom (f : LatticeHom α β) : ⇑f.toSupHom = f := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : SupHom α β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[ext]

中文:
引理 coe_mk
  条件: (f : SupHom α β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[ext]
-/
@[simp] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : LatticeHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : LatticeHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : LatticeHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  body: { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  定义体: { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

@[simp]
-/
protected def copy (f : LatticeHom α β) (f' : α -> β) (h : f' = f) : LatticeHom α β :=
  { f.toSupHom.copy f' h, f.toInfHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : LatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : LatticeHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : LatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : LatticeHom α α where
  body: id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 id
  签名: : LatticeHom α α where
  定义体: id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
-/
protected def id : LatticeHom α α where
  toFun := id
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LatticeHom α α)
  body: ⟨LatticeHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Inhabited (LatticeHom α α)
  定义体: ⟨LatticeHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: LatticeHom, LatticeHom.id
-/
instance : Inhabited (LatticeHom α α) :=
  ⟨LatticeHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(LatticeHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(LatticeHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(LatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: LatticeHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: LatticeHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : LatticeHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : LatticeHom β γ) (g : LatticeHom α β)
  body: { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]

中文:
定义 comp
  签名: (f : LatticeHom β γ) (g : LatticeHom α β)
  定义体: { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]

Depends on / 依赖: f.toInfHom.comp, f.toSupHom.comp, g.toInfHom, g.toSupHom, toInfHom, toSupHom
-/
def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toInfHom.comp g.toInfHom with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : LatticeHom β γ) (g : LatticeHom α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : LatticeHom β γ) (g : LatticeHom α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : LatticeHom β γ) (g : LatticeHom α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : LatticeHom β γ) (g : LatticeHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_apply
  条件: (f : LatticeHom β γ) (g : LatticeHom α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_apply (f : LatticeHom β γ) (g : LatticeHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
-- `simp`-normal form of `coe_comp_sup_hom`
/--
theorem `coe_comp_sup_hom'` / 定理 `coe_comp_sup_hom'`

English:
theorem coe_comp_sup_hom'
  given: (f : LatticeHom β γ) (g : LatticeHom α β)
  proof: rfl

@[to_dual]

中文:
定理 coe_comp_sup_hom'
  条件: (f : LatticeHom β γ) (g : LatticeHom α β)
  证明: rfl

@[to_dual]
-/
theorem coe_comp_sup_hom' (f : LatticeHom β γ) (g : LatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

@[to_dual]
/--
theorem `coe_comp_sup_hom` / 定理 `coe_comp_sup_hom`

English:
theorem coe_comp_sup_hom
  given: (f : LatticeHom β γ) (g : LatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_sup_hom
  条件: (f : LatticeHom β γ) (g : LatticeHom α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_sup_hom (f : LatticeHom β γ) (g : LatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : LatticeHom γ δ) (g : LatticeHom β γ) (h : LatticeHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : LatticeHom α β)
  statement: f.comp (LatticeHom.id α) = f
  proof: LatticeHom.ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : LatticeHom α β)
  结论: f.comp (LatticeHom.id α) = f
  证明: LatticeHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: LatticeHom, LatticeHom.ext
-/
theorem comp_id (f : LatticeHom α β) : f.comp (LatticeHom.id α) = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : LatticeHom α β)
  statement: (LatticeHom.id β).comp f = f
  proof: LatticeHom.ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : LatticeHom α β)
  结论: (LatticeHom.id β).comp f = f
  证明: LatticeHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: LatticeHom, LatticeHom.ext
-/
theorem id_comp (f : LatticeHom α β) : (LatticeHom.id β).comp f = f :=
  LatticeHom.ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f)
  proof: ⟨fun h => LatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f)
  证明: ⟨fun h => LatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, LatticeHom, LatticeHom.ext, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : LatticeHom β γ} {f : LatticeHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => LatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g)
  proof: ⟨fun h => LatticeHom.ext fun a => hg by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g)
  证明: ⟨fun h => LatticeHom.ext fun a => hg by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

Depends on / 依赖: LatticeHom, LatticeHom.comp_apply, LatticeHom.ext, comp_apply, congr_arg
-/
theorem cancel_left {g : LatticeHom β γ} {f₁ f₂ : LatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => LatticeHom.ext fun a => hg by rw [← LatticeHom.comp_apply, h, LatticeHom.comp_apply],
    congr_arg _⟩

/-- `Subtype.val` as a `LatticeHom`. -/
@[to_dual self (reorder := 4 5)]
/--
Definition of `subtypeVal` / `subtypeVal` 的定义

English:
definition subtypeVal
  signature: {P : β -> Prop}
  body: Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

@[simp, to_dual self (reorder := 4 5)]

中文:
定义 subtypeVal
  签名: {P : β -> 命题}
  定义体: Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

@[simp, to_dual self (reorder := 4 5)]

Depends on / 依赖: Subtype, Subtype.lattice, lattice
-/
def subtypeVal {P : β -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    LatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_inf Pinf])

@[simp, to_dual self (reorder := 4 5)]
/--
lemma `subtypeVal_apply` / 引理 `subtypeVal_apply`

English:
lemma subtypeVal_apply
  statement: {P : β -> Prop}
  proof: rfl

@[simp, to_dual self (reorder := 4 5)]

中文:
引理 subtypeVal_apply
  结论: {P : β -> 命题}
  证明: rfl

@[simp, to_dual self (reorder := 4 5)]

Depends on / 依赖: Function, Function.bijective_id, P.hasMap_X, StandardEtalePair, StandardEtalePair.lift_X_left, bijective_id, hasMap_X, lift_X_left
-/
lemma subtypeVal_apply {P : β -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y))
    (x : {x : β // P x}) :
    subtypeVal Psup Pinf x = x := rfl

@[simp, to_dual self (reorder := 4 5)]
/--
lemma `subtypeVal_coe` / 引理 `subtypeVal_coe`

English:
lemma subtypeVal_coe
  statement: {P : β -> Prop}
  proof: rfl

中文:
引理 subtypeVal_coe
  结论: {P : β -> 命题}
  证明: rfl

Depends on / 依赖: Algebra, Algebra.Etale, IsStandardEtale
-/
lemma subtypeVal_coe {P : β -> Prop}
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) :
    ⇑(subtypeVal Psup Pinf) = Subtype.val := rfl

end LatticeHom

namespace OrderHomClass

variable (α β)
variable [LinearOrder α] [Lattice β] [OrderHomClass F α β]

/-- An order homomorphism from a linear order is a lattice homomorphism. -/
instance (priority := 100) toLatticeHomClass : LatticeHomClass F α β :=
  { ‹OrderHomClass F α β› with
    map_sup := fun f a b => by
      obtain h | h := le_total a b
      · rw [sup_eq_right.2 h, sup_eq_right.2 (OrderHomClass.mono f h : f a <= f b)]
      · rw [sup_eq_left.2 h, sup_eq_left.2 (OrderHomClass.mono f h : f b <= f a)]
    map_inf := fun f a b => by
      obtain h | h := le_total a b
      · rw [inf_eq_left.2 h, inf_eq_left.2 (OrderHomClass.mono f h : f a <= f b)]
      · rw [inf_eq_right.2 h, inf_eq_right.2 (OrderHomClass.mono f h : f b <= f a)] }

/--
Definition of `toLatticeHom` / `toLatticeHom` 的定义

English:
definition toLatticeHom
  signature: (f : F)
  body: f

@[simp]

中文:
定义 toLatticeHom
  签名: (f : F)
  定义体: f

@[simp]
-/
def toLatticeHom (f : F) : LatticeHom α β := f

@[simp]
/--
theorem `coe_to_lattice_hom` / 定理 `coe_to_lattice_hom`

English:
theorem coe_to_lattice_hom
  given: (f : F)
  statement: ⇑(toLatticeHom α β f) = f
  proof: rfl

@[simp]

中文:
定理 coe_to_lattice_hom
  条件: (f : F)
  结论: ⇑(toLatticeHom α β f) = f
  证明: rfl

@[simp]
-/
theorem coe_to_lattice_hom (f : F) : ⇑(toLatticeHom α β f) = f :=
  rfl

@[simp]
/--
theorem `to_lattice_hom_apply` / 定理 `to_lattice_hom_apply`

English:
theorem to_lattice_hom_apply
  given: (f : F) (a : α)
  statement: toLatticeHom α β f a = f a
  proof: rfl

中文:
定理 to_lattice_hom_apply
  条件: (f : F) (a : α)
  结论: toLatticeHom α β f a = f a
  证明: rfl
-/
theorem to_lattice_hom_apply (f : F) (a : α) : toLatticeHom α β f a = f a :=
  rfl

end OrderHomClass

/-! ### Dual homs -/

namespace SupHom

variable [Max α] [Max β] [Max γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[to_dual (attr := simps) /--
Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  body: ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩

@[to_dual (attr := simp)]

中文:
定义 dual
  签名: : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  定义体: ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩

@[to_dual (attr := simp)]
-/
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩

@[to_dual (attr := simp)]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: SupHom.dual (SupHom.id α) = InfHom.id _
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_id
  结论: SupHom.dual (SupHom.id α) = InfHom.id _
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_id : SupHom.dual (SupHom.id α) = InfHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : SupHom β γ) (f : SupHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_comp
  条件: (g : SupHom β γ) (f : SupHom α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) :
    SupHom.dual (g.comp f) = (SupHom.dual g).comp (SupHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: SupHom.dual.symm (InfHom.id _) = SupHom.id α
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symm_dual_id
  结论: SupHom.dual.symm (InfHom.id _) = SupHom.id α
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ)
  证明: rfl

Depends on / 依赖: WeaklyEtale
-/
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) =
      (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps!]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  body: ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩

中文:
定义 dual
  签名: : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  定义体: ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩

Depends on / 依赖: Algebra, Algebra.TensorProduct.cancelBaseChange, Function, Function.bijective_id, TensorProduct, TensorProduct.assoc, TensorProduct.lmul, TensorProduct.map, TensorProduct.one_def, WeaklyEtale, WeaklyEtale.flat_lmul, bijective, bijective_id, cancelBaseChange, e.bijective, e.toAlgHom, flat_lmul, of_bijective, one_def, otimes
-/
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩

/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _
  proof: rfl

@[simp]

中文:
定理 dual_id
  结论: LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _
  证明: rfl

@[simp]
-/
@[simp] theorem dual_id : LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _ := rfl

@[simp]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : LatticeHom β γ) (f : LatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 dual_comp
  条件: (g : LatticeHom β γ) (f : LatticeHom α β)
  证明: rfl

@[simp]

Depends on / 依赖: Algebra, Algebra.compHom, P.Ring, algebraMap, compHom
-/
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    LatticeHom.dual (g.comp f) = (LatticeHom.dual g).comp (LatticeHom.dual f) :=
  rfl

@[simp]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α
  proof: rfl

@[simp]

中文:
定理 symm_dual_id
  结论: LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α
  证明: rfl

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl

@[simp]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ)
  证明: rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.comp_assoc, algebraMap_eq, comp_assoc, of_algebraMap_eq
-/
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) =
      (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl

end LatticeHom

/-! ### Prod -/

namespace LatticeHom
variable [Lattice α] [Lattice β]

/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : LatticeHom (α × β) α where
  body: Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 fst
  签名: : LatticeHom (α × β) α where
  定义体: Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, P.Ring, Prod.fst, RingHom, RingHom.comp_assoc, algebraMap_eq, comp_assoc, of_algebraMap_eq
-/
def fst : LatticeHom (α × β) α where
  toFun := Prod.fst
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : LatticeHom (α × β) β where
  body: Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 snd
  签名: : LatticeHom (α × β) β where
  定义体: Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

Depends on / 依赖: Prod.snd
-/
def snd : LatticeHom (α × β) β where
  toFun := Prod.snd
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
lemma `coe_fst` / 引理 `coe_fst`

English:
lemma coe_fst
  statement: ⇑(fst (α := α) (β := β)) = Prod.fst
  proof: rfl

中文:
引理 coe_fst
  结论: ⇑(fst (α := α) (β := β)) = Prod.fst
  证明: rfl
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst (α := α) (β := β)) = Prod.fst := rfl
/--
lemma `coe_snd` / 引理 `coe_snd`

English:
lemma coe_snd
  statement: ⇑(snd (α := α) (β := β)) = Prod.snd
  proof: rfl

中文:
引理 coe_snd
  结论: ⇑(snd (α := α) (β := β)) = Prod.snd
  证明: rfl
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd (α := α) (β := β)) = Prod.snd := rfl
/--
lemma `fst_apply` / 引理 `fst_apply`

English:
lemma fst_apply
  given: (x : α × β)
  statement: fst x = x.fst
  proof: rfl

中文:
引理 fst_apply
  条件: (x : α × β)
  结论: fst x = x.fst
  证明: rfl
-/
lemma fst_apply (x : α × β) : fst x = x.fst := rfl
/--
lemma `snd_apply` / 引理 `snd_apply`

English:
lemma snd_apply
  given: (x : α × β)
  statement: snd x = x.snd
  proof: rfl

中文:
引理 snd_apply
  条件: (x : α × β)
  结论: snd x = x.snd
  证明: rfl
-/
lemma snd_apply (x : α × β) : snd x = x.snd := rfl

end LatticeHom

/-! ### Pi -/

namespace Pi
variable {ι : Type*} {α : ι -> Type*} [forall i, Lattice (α i)]

/--
Definition of `evalLatticeHom` / `evalLatticeHom` 的定义

English:
definition evalLatticeHom
  signature: (i : ι)
  body: Function.eval i
  map_sup' _a _b := rfl
  map_inf' _a _b := rfl

@[simp, norm_cast]

中文:
定义 evalLatticeHom
  签名: (i : ι)
  定义体: Function.eval i
  map_sup' _a _b := rfl
  map_inf' _a _b := rfl

@[simp, norm_cast]

Depends on / 依赖: Function, Function.eval
-/
def evalLatticeHom (i : ι) : LatticeHom (forall i, α i) (α i) where
  toFun := Function.eval i
  map_sup' _a _b := rfl
  map_inf' _a _b := rfl

@[simp, norm_cast]
/--
lemma `coe_evalLatticeHom` / 引理 `coe_evalLatticeHom`

English:
lemma coe_evalLatticeHom
  given: (i : ι)
  statement: ⇑(evalLatticeHom (α := α) i) = Function.eval i
  proof: rfl

中文:
引理 coe_evalLatticeHom
  条件: (i : ι)
  结论: ⇑(evalLatticeHom (α := α) i) = Function.eval i
  证明: rfl

Depends on / 依赖: Function, Function.eval
-/
lemma coe_evalLatticeHom (i : ι) : ⇑(evalLatticeHom (α := α) i) = Function.eval i := rfl

/--
lemma `evalLatticeHom_apply` / 引理 `evalLatticeHom_apply`

English:
lemma evalLatticeHom_apply
  given: (i : ι) (f : forall i, α i)
  statement: evalLatticeHom i f = f i
  proof: rfl

中文:
引理 evalLatticeHom_apply
  条件: (i : ι) (f : 对任意 i, α i)
  结论: evalLatticeHom i f = f i
  证明: rfl
-/
lemma evalLatticeHom_apply (i : ι) (f : forall i, α i) : evalLatticeHom i f = f i := rfl

end Pi
