/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Complete lattice homomorphisms

This file defines frame homomorphisms and complete lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `sSupHom`: Maps which preserve `⨆`.
* `sInfHom`: Maps which preserve `⨅`.
* `FrameHom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`. Note that while a frame
  is a Heyting algebra, frame homs need not preserve `⇨`. For instance,
  `TopologicalSpace.Opens.frameHom` does not in general preserve complementation.
* `CompleteLatticeHom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `sSupHomClass`
* `sInfHomClass`
* `FrameHomClass`
* `CompleteLatticeHomClass`

## Concrete homs

* `CompleteLatticeHom.setPreimage`: `Set.preimage` as a complete lattice homomorphism.
-/

@[expose] public section
assert_not_exists Monoid

open Function OrderDual Set

variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι -> Sort*}

/--
Definition of `sSupHom` / `sSupHom` 的定义

English:
structure sSupHom
  parameters: (α β : Type*) [SupSet α] [SupSet β]
  axioms and operations (2):
    - toFun : α -> β
    - map_sSup'((s : Set α)) : toFun (sSup s) = sSup (toFun '' s)

中文:
结构 sSup态射
  参数: (α β : 类型) [上确界集 α] [上确界集 β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_sSup'((s : 集合 α)) : toFun (sSup s) = sSup (toFun '' s)
-/
structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α -> β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
@[to_dual]
/--
Definition of `sInfHom` / `sInfHom` 的定义

English:
structure sInfHom
  parameters: (α β : Type*) [InfSet α] [InfSet β]
  axioms and operations (2):
    - toFun : α -> β
    - map_sInf'((s : Set α)) : toFun (sInf s) = sInf (toFun '' s)

中文:
结构 sInf态射
  参数: (α β : 类型) [下确界集 α] [下确界集 β]
  公理与运算 (2 个):
    - toFun : α -> β
    - map_sInf'((s : 集合 α)) : toFun (sInf s) = sInf (toFun '' s)
-/
structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  /-- The underlying function of an `sInfHom`. -/
  toFun : α -> β
  /-- The proposition that a `sInfHom` commutes with arbitrary infima/meets -/
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)

/--
Definition of `FrameHom` / `FrameHom` 的定义

English:
structure FrameHom
  parameters: (α β : Type*) [CompleteLattice α] [CompleteLattice β]
  axioms and operations (1):
    - map_sSup'((s : Set α)) : toFun (sSup s) = sSup (toFun '' s)

中文:
结构 框架态射
  参数: (α β : 类型) [完备格 α] [完备格 β]
  公理与运算 (1 个):
    - map_sSup'((s : 集合 α)) : toFun (sSup s) = sSup (toFun '' s)
-/
structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)


/--
Definition of `CompleteLatticeHom` / `CompleteLatticeHom` 的定义

English:
structure CompleteLatticeHom
  parameters: (α β : Type*) [CompleteLattice α] [CompleteLattice β]
  (no additional axioms)

中文:
结构 完备格态射
  参数: (α β : 类型) [完备格 α] [完备格 β]
  (无附加公理)
-/
structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β, sSupHom α β where

attribute [to_dual existing] CompleteLatticeHom.tosSupHom

attribute [nolint docBlame] CompleteLatticeHom.tosSupHom

section

/--
Definition of `sSupHomClass` / `sSupHomClass` 的定义

English:
class sSupHomClass
  parameters: (F α β : Type*) [SupSet α] [SupSet β] [FunLike F α β]
  axioms and operations (1):
    - map_sSup((f : F) (s : Set α)) : f (sSup s) = sSup (f '' s)

中文:
类 sSup态射类
  参数: (F α β : 类型) [上确界集 α] [上确界集 β] [函数状 F α β]
  公理与运算 (1 个):
    - map_sSup((f : F) (s : 集合 α)) : f (sSup s) = sSup (f '' s)
-/
class sSupHomClass (F α β : Type*) [SupSet α] [SupSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sSupHomClass`s commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/-- `sInfHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `sInfHom`. -/
@[to_dual]
/--
Definition of `sInfHomClass` / `sInfHomClass` 的定义

English:
class sInfHomClass
  parameters: (F α β : Type*) [InfSet α] [InfSet β] [FunLike F α β]
  axioms and operations (1):
    - map_sInf((f : F) (s : Set α)) : f (sInf s) = sInf (f '' s)

中文:
类 sInf态射类
  参数: (F α β : 类型) [下确界集 α] [下确界集 β] [函数状 F α β]
  公理与运算 (1 个):
    - map_sInf((f : F) (s : 集合 α)) : f (sInf s) = sInf (f '' s)
-/
class sInfHomClass (F α β : Type*) [InfSet α] [InfSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sInfHomClass`s commute with arbitrary infima/meets. -/
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)

/--
Definition of `FrameHomClass` / `FrameHomClass` 的定义

English:
class FrameHomClass
  parameters: (F α β : Type*) [CompleteLattice α] [CompleteLattice β] [FunLike F α β]
  extends: InfTopHomClass F α β
  axioms and operations (1):
    - map_sSup((f : F) (s : Set α)) : f (sSup s) = sSup (f '' s)

中文:
类 框架态射类
  参数: (F α β : 类型) [完备格 α] [完备格 β] [函数状 F α β]
  继承: InfTop态射类 F α β
  公理与运算 (1 个):
    - map_sSup((f : F) (s : 集合 α)) : f (sSup s) = sSup (f '' s)
-/
class FrameHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β] [FunLike F α β] : Prop
  extends InfTopHomClass F α β where
  /-- The proposition that members of `FrameHomClass` commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/--
Definition of `CompleteLatticeHomClass` / `CompleteLatticeHomClass` 的定义

English:
class CompleteLatticeHomClass
  parameters: (F α β : Type*) [CompleteLattice α] [CompleteLattice β]
  extends: sInfHomClass F α β, sSupHomClass F α β
  (no additional axioms)

中文:
类 完备格态射类
  参数: (F α β : 类型) [完备格 α] [完备格 β]
  继承: sInf态射类 F α β, sSup态射类 F α β
  (无附加公理)
-/
class CompleteLatticeHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β]
    [FunLike F α β] : Prop
  extends sInfHomClass F α β, sSupHomClass F α β where

attribute [to_dual existing] CompleteLatticeHomClass.tosSupHomClass

end

export sSupHomClass (map_sSup)

export sInfHomClass (map_sInf)

attribute [simp] map_sSup map_sInf

section Hom

variable [FunLike F α β]

@[to_dual (attr := simp)]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι -> α)
  proof: by simp [iSup, ← Set.range_comp, Function.comp_def]

@[to_dual]

中文:
定理 map_iSup
  条件: [上确界集 α] [上确界集 β] [sSup态射类 F α β] (f : F) (g : ι -> α)
  证明: by simp [iSup, ← Set.range_comp, Function.comp_def]

@[to_dual]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, comp_def, range_comp
-/
theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι -> α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [iSup, ← Set.range_comp, Function.comp_def]

@[to_dual]
/--
theorem `map_iSup₂` / 定理 `map_iSup₂`

English:
theorem map_iSup₂
  given: [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : forall i, κ i -> α)
  proof: by simp_rw [map_iSup]

中文:
定理 map_iSup₂
  条件: [上确界集 α] [上确界集 β] [sSup态射类 F α β] (f : F) (g : 对任意 i, κ i -> α)
  证明: by simp_rw [map_iSup]

Depends on / 依赖: map_iSup, simp_rw
-/
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : forall i, κ i -> α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [sSupHomClass F α β] : SupBotHomClass F α β :=
  { ‹sSupHomClass F α β› with
    map_sup := fun f a b => by
      rw [← sSup_pair]; rw [map_sSup]
      simp only [Set.image_pair, sSup_insert, sSup_singleton]
    map_bot := fun f => by
      rw [← sSup_empty]; rw [map_sSup]; rw [Set.image_empty]; rw [sSup_empty] }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }

-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sSupHomClass F α β where
  map_sSup := fun f s =>
    eq_of_forall_ge_iff fun c => by
      simp only [← le_map_inv_iff, sSup_le_iff, Set.forall_mem_image]

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.tosInfHomClass with }

end Equiv

variable [FunLike F α β]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SupSet
  signature: α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β)
  body: ⟨fun f => ⟨f, map_sSup f⟩⟩

中文:
实例 [上确界集
  签名: α] [上确界集 β] [sSup态射类 F α β] : CoeTC F (sSup态射 α β)
  定义体: ⟨fun f => ⟨f, map_sSup f⟩⟩

Depends on / 依赖: map_sSup
-/
instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β)
  body: ⟨fun f => ⟨f, map_sSup f⟩⟩

中文:
实例 [完备格
  签名: α] [完备格 β] [框架态射类 F α β] : CoeTC F (框架态射 α β)
  定义体: ⟨fun f => ⟨f, map_sSup f⟩⟩

Depends on / 依赖: map_sSup
-/
instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteLattice
  signature: α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
  body: ⟨fun f => ⟨f, map_sSup f⟩⟩

中文:
实例 [完备格
  签名: α] [完备格 β] [完备格态射类 F α β] :
  定义体: ⟨fun f => ⟨f, map_sSup f⟩⟩

Depends on / 依赖: map_sSup
-/
instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum and infimum homomorphisms -/


namespace sSupHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (sSupHom α β) α β
  body: sSupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

中文:
实例 :
  签名: 函数状 (sSup态射 α β) α β
  定义体: sSupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]

Depends on / 依赖: sSupHom, sSupHom.toFun
-/
instance : FunLike (sSupHom α β) α β where
  coe := sSupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: sSupHomClass (sSupHom α β) α β
  body: sSupHom.map_sSup'

@[to_dual (attr := simp)]

中文:
实例 :
  签名: sSup态射类 (sSup态射 α β) α β
  定义体: sSupHom.map_sSup'

@[to_dual (attr := simp)]

Depends on / 依赖: map_sSup, sSupHom, sSupHom.map_sSup
-/
instance : sSupHomClass (sSupHom α β) α β where
  map_sSup := sSupHom.map_sSup'

@[to_dual (attr := simp)]
/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : sSupHom α β)
  statement: f.toFun = f
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
引理 toFun_eq_coe
  条件: (f : sSup态射 α β)
  结论: f.toFun = f
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
lemma toFun_eq_coe (f : sSupHom α β) : f.toFun = f := rfl

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
  given: {f g : sSupHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : sSup态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `sSupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual
/-- Copy of a `sInfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : sSupHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_sSup' := h.symm ▸ f.map_sSup'

@[to_dual (attr := simp)]

中文:
定义 copy
  签名: (f : sSup态射 α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_sSup' := h.symm ▸ f.map_sSup'

@[to_dual (attr := simp)]
-/
protected def copy (f : sSupHom α β) (f' : α -> β) (h : f' = f) : sSupHom α β where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'

@[to_dual (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : sSupHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

@[to_dual]

中文:
定理 coe_copy
  条件: (f : sSup态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

@[to_dual]
-/
theorem coe_copy (f : sSupHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : sSupHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : sSup态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : sSupHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `sSupHom`. -/
@[to_dual /-- `id` as an `sInfHom`. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : sSupHom α α
  body: ⟨id, fun s => by rw [id, Set.image_id]⟩

@[to_dual]

中文:
定义 id
  签名: : sSup态射 α α
  定义体: ⟨id, fun s => by rw [id, Set.image_id]⟩

@[to_dual]
-/
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (sSupHom α α)
  body: ⟨sSupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

中文:
实例 :
  签名: 可居 (sSup态射 α α)
  定义体: ⟨sSupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: sSupHom, sSupHom.id
-/
instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(sSupHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(sSup态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: sSupHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: sSup态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl

/-- Composition of `sSupHom`s as a `sSupHom`. -/
@[to_dual /-- Composition of `sInfHom`s as a `sInfHom`. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : sSupHom β γ) (g : sSupHom α β)
  body: f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]

@[to_dual (attr := simp)]

中文:
定义 comp
  签名: (f : sSup态射 β γ) (g : sSup态射 α β)
  定义体: f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]

@[to_dual (attr := simp)]
-/
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]

@[to_dual (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : sSupHom β γ) (g : sSupHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp
  条件: (f : sSup态射 β γ) (g : sSup态射 α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : sSupHom β γ) (g : sSupHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_apply
  条件: (f : sSup态射 β γ) (g : sSup态射 α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_assoc
  条件: (f : sSup态射 γ δ) (g : sSup态射 β γ) (h : sSup态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : sSupHom α β)
  statement: f.comp (sSupHom.id α) = f
  proof: ext fun _ => rfl

@[to_dual (attr := simp)]

中文:
定理 comp_id
  条件: (f : sSup态射 α β)
  结论: f.comp (sSup态射.id α) = f
  证明: ext fun _ => rfl

@[to_dual (attr := simp)]
-/
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : sSupHom α β)
  statement: (sSupHom.id β).comp f = f
  proof: ext fun _ => rfl

@[to_dual (attr := simp)]

中文:
定理 id_comp
  条件: (f : sSup态射 α β)
  结论: (sSup态射.id β).comp f = f
  证明: ext fun _ => rfl

@[to_dual (attr := simp)]
-/
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[to_dual (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : sSup态射 β γ} {f : sSup态射 α β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[to_dual (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : sSup态射 β γ} {f₁ f₂ : sSup态射 α β} (hg : 单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end SupSet

variable {_ : CompleteLattice β}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (sSupHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

中文:
实例 :
  签名: 偏序 (sSup态射 α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (sSupHom α β)
  body: ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

@[to_dual]

中文:
实例 :
  签名: 底元素 (sSup态射 α β)
  定义体: ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

@[to_dual]

Depends on / 依赖: Set.image_empty, eq_empty_or_nonempty, hs.image_const, image_const, image_empty, s.eq_empty_or_nonempty, sSup_empty, sSup_singleton
-/
instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (sSupHom α β)
  body: fun _ _ => OrderBot.bot_le _

@[to_dual (attr := simp)]

中文:
实例 :
  签名: 有底序 (sSup态射 α β)
  定义体: fun _ _ => OrderBot.bot_le _

@[to_dual (attr := simp)]

Depends on / 依赖: OrderBot, OrderBot.bot_le, bot_le
-/
instance : OrderBot (sSupHom α β) where
  bot_le := fun _ _ => OrderBot.bot_le _

@[to_dual (attr := simp)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ⇑(⊥ : sSupHom α β) = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_bot
  结论: ⇑(⊥ : sSup态射 α β) = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: (a : α)
  statement: (⊥ : sSupHom α β) a = ⊥
  proof: rfl

中文:
定理 bot_apply
  条件: (a : α)
  结论: (⊥ : sSup态射 α β) a = ⊥
  证明: rfl
-/
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl

end sSupHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (FrameHom α β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

中文:
实例 :
  签名: 函数状 (框架态射 α β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (FrameHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FrameHomClass (FrameHom α β) α β
  body: f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

中文:
实例 :
  签名: 框架态射类 (框架态射 α β) α β
  定义体: f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

Depends on / 依赖: f.map_sSup, map_sSup
-/
instance : FrameHomClass (FrameHom α β) α β where
  map_sSup f := f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/--
Definition of `toLatticeHom` / `toLatticeHom` 的定义

English:
definition toLatticeHom
  signature: (f : FrameHom α β)
  body: f

中文:
定义 toLatticeHom
  签名: (f : 框架态射 α β)
  定义体: f
-/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : FrameHom α β)
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (f : 框架态射 α β)
  结论: f.toFun = f
  证明: rfl
-/
lemma toFun_eq_coe (f : FrameHom α β) : f.toFun = f := rfl

/--
lemma `coe_toInfTopHom` / 引理 `coe_toInfTopHom`

English:
lemma coe_toInfTopHom
  given: (f : FrameHom α β)
  statement: ⇑f.toInfTopHom = f
  proof: rfl

中文:
引理 coe_toInfTopHom
  条件: (f : 框架态射 α β)
  结论: ⇑f.toInfTopHom = f
  证明: rfl
-/
@[simp] lemma coe_toInfTopHom (f : FrameHom α β) : ⇑f.toInfTopHom = f := rfl
/--
lemma `coe_toLatticeHom` / 引理 `coe_toLatticeHom`

English:
lemma coe_toLatticeHom
  given: (f : FrameHom α β)
  statement: ⇑f.toLatticeHom = f
  proof: rfl

中文:
引理 coe_toLatticeHom
  条件: (f : 框架态射 α β)
  结论: ⇑f.toLatticeHom = f
  证明: rfl

Depends on / 依赖: FormallyEtale
-/
@[simp] lemma coe_toLatticeHom (f : FrameHom α β) : ⇑f.toLatticeHom = f := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : InfTopHom α β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[ext]

中文:
引理 coe_mk
  条件: (f : InfTop态射 α β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[ext]

Depends on / 依赖: FormallyEtale, FormallySmooth
-/
@[simp] lemma coe_mk (f : InfTopHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : FrameHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 框架态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : FrameHom α β) (f' : α -> β) (h : f' = f)
  body: { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

@[simp]

中文:
定义 copy
  签名: (f : 框架态射 α β) (f' : α -> β) (h : f' = f)
  定义体: { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

@[simp]
-/
protected def copy (f : FrameHom α β) (f' : α -> β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : FrameHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 框架态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : FrameHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : FrameHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 框架态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : FrameHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : FrameHom α α
  body: { sSupHom.id α with toInfTopHom := InfTopHom.id α }

中文:
定义 id
  签名: : 框架态射 α α
  定义体: { sSupHom.id α with toInfTopHom := InfTopHom.id α }
-/
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FrameHom α α)
  body: ⟨FrameHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (框架态射 α α)
  定义体: ⟨FrameHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: FrameHom, FrameHom.id
-/
instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(FrameHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(框架态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: FrameHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 框架态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : FrameHom β γ) (g : FrameHom α β)
  body: { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]

中文:
定义 comp
  签名: (f : 框架态射 β γ) (g : 框架态射 α β)
  定义体: { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]

Depends on / 依赖: f.toInfTopHom.comp, g.toInfTopHom, sSupHom, toInfTopHom
-/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : FrameHom β γ) (g : FrameHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : 框架态射 β γ) (g : 框架态射 α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : FrameHom β γ) (g : FrameHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : 框架态射 β γ) (g : 框架态射 α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : 框架态射 γ δ) (g : 框架态射 β γ) (h : 框架态射 α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : FrameHom α β)
  statement: f.comp (FrameHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : 框架态射 α β)
  结论: f.comp (框架态射.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : FrameHom α β)
  statement: (FrameHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : 框架态射 α β)
  结论: (框架态射.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

中文:
定理 cancel_right
  条件: {g₁ g₂ : 框架态射 β γ} {f : 框架态射 α β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : 框架态射 β γ} {f₁ f₂ : 框架态射 α β} (hg : 单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (FrameHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: 偏序 (框架态射 α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CompleteLatticeHom α β) α β
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

中文:
实例 :
  签名: 函数状 (完备格态射 α β) α β
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (CompleteLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLatticeHomClass (CompleteLatticeHom α β) α β
  body: f.map_sSup'
  map_sInf f := f.map_sInf'

中文:
实例 :
  签名: 完备格态射类 (完备格态射 α β) α β
  定义体: f.map_sSup'
  map_sInf f := f.map_sInf'

Depends on / 依赖: f.map_sSup, map_sSup
-/
instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  map_sSup f := f.map_sSup'
  map_sInf f := f.map_sInf'

/--
Definition of `OrderIso.toCompleteLatticeHom` / `OrderIso.toCompleteLatticeHom` 的定义

English:
definition OrderIso.toCompleteLatticeHom
  signature: (f : OrderIso α β)
  body: f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

中文:
定义 OrderIso.toCompleteLatticeHom
  签名: (f : OrderIso α β)
  定义体: f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

Depends on / 依赖: Unramified
-/
@[simps] def OrderIso.toCompleteLatticeHom (f : OrderIso α β) : CompleteLatticeHom α β where
  toFun := f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

/--
Definition of `toBoundedLatticeHom` / `toBoundedLatticeHom` 的定义

English:
definition toBoundedLatticeHom
  signature: (f : CompleteLatticeHom α β)
  body: f

中文:
定义 toBoundedLatticeHom
  签名: (f : 完备格态射 α β)
  定义体: f
-/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : CompleteLatticeHom α β)
  statement: f.toFun = f
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 toFun_eq_coe
  条件: (f : 完备格态射 α β)
  结论: f.toFun = f
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma toFun_eq_coe (f : CompleteLatticeHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp)]
/--
lemma `coe_tosInfHom` / 引理 `coe_tosInfHom`

English:
lemma coe_tosInfHom
  given: (f : CompleteLatticeHom α β)
  statement: ⇑f.tosInfHom = f
  proof: rfl

@[simp]

中文:
引理 coe_tosInfHom
  条件: (f : 完备格态射 α β)
  结论: ⇑f.tosInfHom = f
  证明: rfl

@[simp]
-/
lemma coe_tosInfHom (f : CompleteLatticeHom α β) : ⇑f.tosInfHom = f := rfl

@[simp]
/--
lemma `coe_toBoundedLatticeHom` / 引理 `coe_toBoundedLatticeHom`

English:
lemma coe_toBoundedLatticeHom
  given: (f : CompleteLatticeHom α β)
  statement: ⇑f.toBoundedLatticeHom = f
  proof: rfl

中文:
引理 coe_toBoundedLatticeHom
  条件: (f : 完备格态射 α β)
  结论: ⇑f.toBoundedLatticeHom = f
  证明: rfl
-/
lemma coe_toBoundedLatticeHom (f : CompleteLatticeHom α β) : ⇑f.toBoundedLatticeHom = f := rfl

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : sInfHom α β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[ext]

中文:
引理 coe_mk
  条件: (f : sInf态射 α β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[ext]

Depends on / 依赖: RingHom, RingHom.snd, toAlgebra
-/
@[simp] lemma coe_mk (f : sInfHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : CompleteLatticeHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 完备格态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext, RingHom, RingHom.fst, toAlgebra
-/
theorem ext {f g : CompleteLatticeHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f)
  body: { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }

@[simp]

中文:
定义 copy
  签名: (f : 完备格态射 α β) (f' : α -> β) (h : f' = f)
  定义体: { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }

@[simp]

Depends on / 依赖: RingHom, RingHom.snd, toAlgebra
-/
protected def copy (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 完备格态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 完备格态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : CompleteLatticeHom α α
  body: { sSupHom.id α, sInfHom.id α with toFun := id }

中文:
定义 id
  签名: : 完备格态射 α α
  定义体: { sSupHom.id α, sInfHom.id α with toFun := id }
-/
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CompleteLatticeHom α α)
  body: ⟨CompleteLatticeHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (完备格态射 α α)
  定义体: ⟨CompleteLatticeHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: CompleteLatticeHom, CompleteLatticeHom.id
-/
instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(CompleteLatticeHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(完备格态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl

variable {α}
@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: CompleteLatticeHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 完备格态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β)
  body: { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }

@[simp]

中文:
定义 comp
  签名: (f : 完备格态射 β γ) (g : 完备格态射 α β)
  定义体: { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }

@[simp]

Depends on / 依赖: f.tosInfHom.comp, f.tosSupHom.comp, g.tosInfHom, g.tosSupHom, tosInfHom, tosSupHom
-/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : 完备格态射 β γ) (g : 完备格态射 α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : 完备格态射 β γ) (g : 完备格态射 α β) (a : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: (f : 完备格态射 γ δ) (g : 完备格态射 β γ)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : CompleteLatticeHom α β)
  statement: f.comp (CompleteLatticeHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : 完备格态射 α β)
  结论: f.comp (完备格态射.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : CompleteLatticeHom α β)
  statement: (CompleteLatticeHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : 完备格态射 α β)
  结论: (完备格态射.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  statement: {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

中文:
定理 cancel_right
  结论: {g₁ g₂ : 完备格态射 β γ} {f : 完备格态射 α β}
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  statement: {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  结论: {g : 完备格态射 β γ} {f₁ f₂ : 完备格态射 α β}
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[to_dual (attr := simps)
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ where
  body: ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩

@[to_dual (attr := simp)]

中文:
定义 dual
  签名: : sSup态射 α β ≃ sInf态射 αᵒᵈ βᵒᵈ where
  定义体: ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩

@[to_dual (attr := simp)]
-/
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩

@[to_dual (attr := simp)]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: sSupHom.dual (sSupHom.id α) = sInfHom.id _
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_id
  结论: sSup态射.dual (sSup态射.id α) = sInf态射.id _
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : sSupHom β γ) (f : sSupHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_comp
  条件: (g : sSup态射 β γ) (f : sSup态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) :
    sSupHom.dual (g.comp f) = (sSupHom.dual g).comp (sSupHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symm_dual_id
  结论: sSup态射.dual.symm (sInf态射.id _) = sSup态射.id α
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : sInf态射 βᵒᵈ γᵒᵈ) (f : sInf态射 αᵒᵈ βᵒᵈ)
  证明: rfl
-/
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl

end sSupHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps!]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  body: ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩

@[simp]

中文:
定义 dual
  签名: : 完备格态射 α β ≃ 完备格态射 αᵒᵈ βᵒᵈ where
  定义体: ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩

@[simp]
-/
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s => f.map_sInf' s⟩

@[simp]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _
  proof: rfl

@[simp]

中文:
定理 dual_id
  结论: 完备格态射.dual (完备格态射.id α) = 完备格态射.id _
  证明: rfl

@[simp]
-/
theorem dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _ :=
  rfl

@[simp]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 dual_comp
  条件: (g : 完备格态射 β γ) (f : 完备格态射 α β)
  证明: rfl

@[simp]
-/
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    CompleteLatticeHom.dual (g.comp f) =
      (CompleteLatticeHom.dual g).comp (CompleteLatticeHom.dual f) :=
  rfl

@[simp]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  proof: rfl

@[simp]

中文:
定理 symm_dual_id
  证明: rfl

@[simp]
-/
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl

@[simp]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : 完备格态射 βᵒᵈ γᵒᵈ) (f : 完备格态射 αᵒᵈ βᵒᵈ)
  证明: rfl
-/
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/--
Definition of `setPreimage` / `setPreimage` 的定义

English:
definition setPreimage
  signature: (f : α -> β)
  body: preimage f
map_sSup' s := preimage_sUnion.trans by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
map_sInf' s := preimage_sInter.trans by simp only [Set.sInf_eq_sInter, Set.sInter_image]

@[simp]

中文:
定义 setPreimage
  签名: (f : α -> β)
  定义体: preimage f
map_sSup' s := preimage_sUnion.trans by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
map_sInf' s := preimage_sInter.trans by simp only [Set.sInf_eq_sInter, Set.sInter_image]

@[simp]

Depends on / 依赖: preimage
-/
def setPreimage (f : α -> β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := preimage f
map_sSup' s := preimage_sUnion.trans by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
map_sInf' s := preimage_sInter.trans by simp only [Set.sInf_eq_sInter, Set.sInter_image]

@[simp]
/--
theorem `coe_setPreimage` / 定理 `coe_setPreimage`

English:
theorem coe_setPreimage
  given: (f : α -> β)
  statement: ⇑(setPreimage f) = preimage f
  proof: rfl

@[simp]

中文:
定理 coe_setPreimage
  条件: (f : α -> β)
  结论: ⇑(setPreimage f) = 原像 f
  证明: rfl

@[simp]
-/
theorem coe_setPreimage (f : α -> β) : ⇑(setPreimage f) = preimage f :=
  rfl

@[simp]
/--
theorem `setPreimage_apply` / 定理 `setPreimage_apply`

English:
theorem setPreimage_apply
  given: (f : α -> β) (s : Set β)
  statement: setPreimage f s = s.preimage f
  proof: rfl

@[simp]

中文:
定理 setPreimage_apply
  条件: (f : α -> β) (s : 集合 β)
  结论: setPreimage f s = s.原像 f
  证明: rfl

@[simp]

Depends on / 依赖: S.property.right, property
-/
theorem setPreimage_apply (f : α -> β) (s : Set β) : setPreimage f s = s.preimage f :=
  rfl

@[simp]
/--
theorem `setPreimage_id` / 定理 `setPreimage_id`

English:
theorem setPreimage_id
  statement: setPreimage (id : α -> α) = CompleteLatticeHom.id _
  proof: rfl

中文:
定理 setPreimage_id
  结论: setPreimage (id : α -> α) = 完备格态射.id _
  证明: rfl

Depends on / 依赖: S.property.left, property
-/
theorem setPreimage_id : setPreimage (id : α -> α) = CompleteLatticeHom.id _ :=
  rfl

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` syntactically)
/--
theorem `setPreimage_comp` / 定理 `setPreimage_comp`

English:
theorem setPreimage_comp
  given: (g : β -> γ) (f : α -> β)
  proof: rfl

中文:
定理 setPreimage_comp
  条件: (g : β -> γ) (f : α -> β)
  证明: rfl
-/
theorem setPreimage_comp (g : β -> γ) (f : α -> β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl

end CompleteLatticeHom

/--
theorem `Set.image_sSup` / 定理 `Set.image_sSup`

English:
theorem Set.image_sSup
  given: {f : α -> β} (s : Set (Set α))
  statement: f '' sSup s = sSup (image f '' s)
  proof: Set.image_sUnion

中文:
定理 集合.image_sSup
  条件: {f : α -> β} (s : 集合 (集合 α))
  结论: f '' sSup s = sSup (像 f '' s)
  证明: Set.image_sUnion

Depends on / 依赖: Set.image_sUnion, image_sUnion
-/
theorem Set.image_sSup {f : α -> β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  Set.image_sUnion

/-- Using `Set.image`, a function between types yields a `sSupHom` between their lattices of
subsets.

See also `CompleteLatticeHom.setPreimage`. -/
@[simps]
/--
Definition of `sSupHom.setImage` / `sSupHom.setImage` 的定义

English:
definition sSupHom.setImage
  signature: (f : α -> β)
  body: image f
  map_sSup' := Set.image_sSup

中文:
定义 sSup态射.setImage
  签名: (f : α -> β)
  定义体: image f
  map_sSup' := Set.image_sSup
-/
def sSupHom.setImage (f : α -> β) : sSupHom (Set α) (Set β) where
  toFun := image f
  map_sSup' := Set.image_sSup

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
/--
Definition of `Equiv.toOrderIsoSet` / `Equiv.toOrderIsoSet` 的定义

English:
definition Equiv.toOrderIsoSet
  signature: (e : α ≃ β)
  body: e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩

中文:
定义 等价.toOrderIsoSet
  签名: (e : α ≃ β)
  定义体: e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩

Depends on / 依赖: Algebra, Algebra.FormallyUnramified.finite_of_free, FormallyUnramified, finite_of_free, isArtinian_of_tower
-/
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩

variable [CompleteLattice α] (x : α × α)

/--
Definition of `supsSupHom` / `supsSupHom` 的定义

English:
definition supsSupHom
  signature: : sSupHom (α × α) α where
  body: x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]

中文:
定义 supsSupHom
  签名: : sSup态射 (α × α) α where
  定义体: x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
-/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]

/--
Definition of `infsInfHom` / `infsInfHom` 的定义

English:
definition infsInfHom
  signature: : sInfHom (α × α) α where
  body: x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]

@[simp, norm_cast]

中文:
定义 infsInfHom
  签名: : sInf态射 (α × α) α where
  定义体: x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]

@[simp, norm_cast]
-/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]

@[simp, norm_cast]
/--
theorem `supsSupHom_apply` / 定理 `supsSupHom_apply`

English:
theorem supsSupHom_apply
  statement: supsSupHom x = x.1 ⊔ x.2
  proof: rfl

@[simp, norm_cast]

中文:
定理 supsSupHom_apply
  结论: supsSupHom x = x.1 ⊔ x.2
  证明: rfl

@[simp, norm_cast]
-/
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl

@[simp, norm_cast]
/--
theorem `infsInfHom_apply` / 定理 `infsInfHom_apply`

English:
theorem infsInfHom_apply
  statement: infsInfHom x = x.1 ⊓ x.2
  proof: rfl

中文:
定理 infsInfHom_apply
  结论: infsInfHom x = x.1 ⊓ x.2
  证明: rfl
-/
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
