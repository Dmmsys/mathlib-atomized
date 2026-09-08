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

variable {F α β γ δ : Type*} {ι : Sort*} {κ : ι → Sort*}

/-- The type of `⨆`-preserving functions from `α` to `β`. -/
/-
**sSupHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_8) → (β : Type u_9) → [SupSet α] → [SupSet β] → Type (max u_8 
u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⨆`-preserving functions from `α` to `β`.
-/
structure sSupHom (α β : Type*) [SupSet α] [SupSet β] where
  /-- The underlying function of a sSupHom. -/
  toFun : α → β
  /-- The proposition that a `sSupHom` commutes with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)

/-- The type of `⨅`-preserving functions from `α` to `β`. -/
@[to_dual]
/-
**sInfHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_8) → (β : Type u_9) → [InfSet α] → [InfSet β] → Type (max u_8 
u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `⨅`-preserving functions from `α` to `β`.
-/
structure sInfHom (α β : Type*) [InfSet α] [InfSet β] where
  /-- The underlying function of an `sInfHom`. -/
  toFun : α → β
  /-- The proposition that a `sInfHom` commutes with arbitrary infima/meets -/
  map_sInf' (s : Set α) : toFun (sInf s) = sInf (toFun '' s)

/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
/-
**FrameHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_8) → (β : Type u_9) → [CompleteLattice α] → [CompleteLattice β
] → Type (max u_8 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of frame homomorphisms from `α` to `β`. They preserve finite meets and 
arbitrary joins.
-/
structure FrameHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  /-- The proposition that frame homomorphisms commute with arbitrary suprema/joins. -/
  map_sSup' (s : Set α) : toFun (sSup s) = sSup (toFun '' s)


/-- The type of complete lattice homomorphisms from `α` to `β`. -/
/-
**CompleteLatticeHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_8) → (β : Type u_9) → [CompleteLattice α] → [CompleteLattice β
] → Type (max u_8 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of complete lattice homomorphisms from `α` to `β`.
-/
structure CompleteLatticeHom (α β : Type*) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β, sSupHom α β where

attribute [to_dual existing] CompleteLatticeHom.tosSupHom

attribute [nolint docBlame] CompleteLatticeHom.tosSupHom

section

/-- `sSupHomClass F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `sSupHom`. -/
/-
**sSupHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) → (α : Type u_9) → (β : Type u_10) → [SupSet α] → [SupSet β
] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sSupHomClass F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `sSupHom`.
-/
class sSupHomClass (F α β : Type*) [SupSet α] [SupSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sSupHomClass`s commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/-- `sInfHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `sInfHom`. -/
@[to_dual]
/-
**sInfHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) → (α : Type u_9) → (β : Type u_10) → [InfSet α] → [InfSet β
] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sInfHomClass F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `sInfHom`.
-/
class sInfHomClass (F α β : Type*) [InfSet α] [InfSet β] [FunLike F α β] : Prop where
  /-- The proposition that members of `sInfHomClass`s commute with arbitrary infima/meets. -/
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)

/-- `FrameHomClass F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `FrameHom`. -/
/-
**FrameHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) → (α : Type u_9) → (β : Type u_10) → [CompleteLattice α] → 
[CompleteLattice β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FrameHomClass F α β` states that `F` is a type of frame morphisms. They preserv
e `⊓` and `⨆`.

You should extend this class when you extend `FrameHom`.
-/
class FrameHomClass (F α β : Type*) [CompleteLattice α] [CompleteLattice β] [FunLike F α β] : Prop
  extends InfTopHomClass F α β where
  /-- The proposition that members of `FrameHomClass` commute with arbitrary suprema/joins. -/
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)

/-- `CompleteLatticeHomClass F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `CompleteLatticeHom`. -/
/-
**CompleteLatticeHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) → (α : Type u_9) → (β : Type u_10) → [CompleteLattice α] → 
[CompleteLattice β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CompleteLatticeHomClass F α β` states that `F` is a type of complete lattice mo
rphisms.

You should extend this class when you extend `CompleteLatticeHom`.
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
/-
**map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι -> α) :
 f (⨆ i, g i) = ⨆ i, f (g i)
参数：f : F；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSupHomClass.map_sSup`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {
inst : SupSet α} {inst_1 : SupSet β} {inst_2 : FunLike F α β}   [self : sSupHomC
lass F α β]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by simp [iSup, ← Set.range_comp, Function.comp_def]

@[to_dual]
/-
**map_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι -> α) :
 f (⨆ i, g i) = ⨆ i, f (g i)
参数：f : F；g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSupHomClass.map_sSup`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {
inst : SupSet α} {inst_1 : SupSet β} {inst_2 : FunLike F α β}   [self : sSupHomC
lass F α β]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α]
    [CompleteLattice β] [sSupHomClass F α β] : SupBotHomClass F α β :=
  { ‹sSupHomClass F α β› with
    map_sup := fun f a b => by
      rw [← sSup_pair, map_sSup]
      simp only [Set.image_pair, sSup_insert, sSup_singleton]
    map_bot := fun f => by
      rw [← sSup_empty, map_sSup, Set.image_empty, sSup_empty] }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : sSupHomClass F α β where
  map_sSup := fun f s =>
    eq_of_forall_ge_iff fun c => by
      simp only [← le_map_inv_iff, sSup_le_iff, Set.forall_mem_image]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.tosInfHomClass with }

end Equiv

variable [FunLike F α β]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (sSupHom α β) α β where
  coe := sSupHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_dual]
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : sSupHomClass (sSupHom α β) α β where
  map_sSup := sSupHom.map_sSup'

@[to_dual (attr := simp)]
/-
**sSupHom.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `sSupHom`。
形式化陈述：toFun_eq_coe (f : sSupHom α β) : f.toFun = f
参数：f : sSupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe (f : sSupHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp, norm_cast)]
/-
**sSupHom.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `sSupHom`。
形式化陈述：coe_mk (f : α -> β) (hf) : ⇑(mk f hf) = f
参数：f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (f : α → β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
/-
**sSupHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `sSupHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual
/-- Copy of a `sInfHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/-
**sSupHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `sSupHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : SupSet α] → [inst_1 : SupSet β
] → (f : sSupHom α β) → (f' : α → β) → f' = ⇑f → sSupHom α β
参数：f : sSupHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β where
  toFun := f'
  map_sSup' := h.symm ▸ f.map_sSup'

@[to_dual (attr := simp)]
/-
**sSupHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：coe_copy (f : sSupHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f
'
参数：f : sSupHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/-
**sSupHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：copy_eq (f : sSupHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : sSupHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `sSupHom`. -/
@[to_dual /-- `id` as an `sInfHom`. -/]
/-
**sSupHom.id** 是 Mathlib 中的一个定义，位于命名空间 `sSupHom`。
形式化陈述：(α : Type u_2) → [inst : SupSet α] → sSupHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `sSupHom`.
-/
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩

@[to_dual]
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/-
**sSupHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：coe_id : ⇑(sSupHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl

variable {α}

@[to_dual (attr := simp)]
/-
**sSupHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：id_apply (a : α) : sSupHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl

/-- Composition of `sSupHom`s as a `sSupHom`. -/
@[to_dual /-- Composition of `sInfHom`s as a `sInfHom`. -/]
/-
**sSupHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `sSupHom`。
形式化陈述：comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where toFun
参数：f : sSupHom β γ；g : sSupHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `sSupHom`s as a `sSupHom`.
-/
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
  toFun := f ∘ g
  map_sSup' s := by rw [comp_apply, map_sSup, map_sSup, Set.image_image]; simp only [Function.comp]

@[to_dual (attr := simp)]
/-
**sSupHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g
参数：f : sSupHom β γ；g : sSupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f 
(g a)
参数：f : sSupHom β γ；g : sSupHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) : (f.comp
 g).comp h = f.comp (g.comp h)
参数：f : sSupHom γ δ；g : sSupHom β γ；h : sSupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f
参数：f : sSupHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupHom.ext`：ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g
-/
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
/-
**sSupHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f
参数：f : sSupHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupHom.ext`：ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g
-/
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun _ => rfl

@[to_dual (attr := simp)]
/-
**sSupHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
 g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupHom.ext`：ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[to_dual (attr := simp)]
/-
**sSupHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) : g
.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupHom.ext`：ext {f g : sSupHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSupHom.comp_apply`：comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : 
α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end SupSet

variable {_ : CompleteLattice β}

@[to_dual]
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

@[to_dual]
/-
**sSupHom.** 是 Mathlib 中的一个实例，位于命名空间 `sSupHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (sSupHom α β) where
  bot_le := fun _ _ ↦ OrderBot.bot_le _

@[to_dual (attr := simp)]
/-
**sSupHom.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：coe_bot : ⇑(⊥ : sSupHom α β) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl

end sSupHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

/-
**FrameHom.** 是 Mathlib 中的一个实例，位于命名空间 `FrameHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (FrameHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
/-
**FrameHom.** 是 Mathlib 中的一个实例，位于命名空间 `FrameHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FrameHomClass (FrameHom α β) α β where
  map_sSup f := f.map_sSup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Reinterpret a `FrameHom` as a `LatticeHom`. -/
/-
**FrameHom.toLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `FrameHom`。
形式化陈述：toLatticeHom (f : FrameHom α β) : LatticeHom α β
参数：f : FrameHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `FrameHom` as a `LatticeHom`.
-/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
/-
**FrameHom.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `FrameHom`。
形式化陈述：toFun_eq_coe (f : FrameHom α β) : f.toFun = f
参数：f : FrameHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe (f : FrameHom α β) : f.toFun = f := rfl
/-
**FrameHom.coe_toInfTopHom** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : FrameHom α β),   ⇑f.toInfTopHom = ⇑f
参数：f : FrameHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toInfTopHom (f : FrameHom α β) : ⇑f.toInfTopHom = f := rfl
/-
**FrameHom.coe_toLatticeHom** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : FrameHom α β),   ⇑f.toLatticeHom = ⇑f
参数：f : FrameHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLatticeHom (f : FrameHom α β) : ⇑f.toLatticeHom = f := rfl
/-
**FrameHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : InfTopHom α β)   (hf : ∀ (s : Set α), f.toFun (sSup s) = sSup
 (f.toFun '' s)), ⇑{ toInfTopHom := f, map_sSup' := hf } = ⇑f
参数：f : InfTopHom α β；hf : ∀ (s : Set α), f.toFun (sSup s) = sSup (f.toFun '' s)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : InfTopHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/-
**FrameHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `FrameHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**FrameHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `FrameHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : CompleteLattice α] →      
 [inst_1 : CompleteLattice β] → (f : FrameHom α β) → (f' : α → β) → f' = ⇑f → Fr
ameHom α β
参数：f : FrameHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `FrameHom` with a new `toFun` equal to the old one. Useful to fix defi
nitional
equalities.
-/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }

@[simp]
/-
**FrameHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：coe_copy (f : FrameHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = 
f'
参数：f : FrameHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**FrameHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：copy_eq (f : FrameHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : FrameHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `FrameHom`. -/
/-
**FrameHom.id** 是 Mathlib 中的一个定义，位于命名空间 `FrameHom`。
形式化陈述：(α : Type u_2) → [inst : CompleteLattice α] → FrameHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `FrameHom`.
-/
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
/-
**FrameHom.** 是 Mathlib 中的一个实例，位于命名空间 `FrameHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

@[simp, norm_cast]
/-
**FrameHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：coe_id : ⇑(FrameHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**FrameHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：id_apply (a : α) : FrameHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl

/-- Composition of `FrameHom`s as a `FrameHom`. -/
/-
**FrameHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `FrameHom`。
形式化陈述：comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ
参数：f : FrameHom β γ；g : FrameHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `FrameHom`s as a `FrameHom`.
-/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with
    toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }

@[simp]
/-
**FrameHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g
参数：f : FrameHom β γ；g : FrameHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**FrameHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = 
f (g a)
参数：f : FrameHom β γ；g : FrameHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
/-
**FrameHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) : (f.c
omp g).comp h = f.comp (g.comp h)
参数：f : FrameHom γ δ；g : FrameHom β γ；h : FrameHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**FrameHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f
参数：f : FrameHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
-/
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**FrameHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f
参数：f : FrameHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
-/
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**FrameHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f)
 : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
/-
**FrameHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `FrameHom`。
形式化陈述：cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
 g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FrameHom.comp_apply`：comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a
 : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
/-
**FrameHom.** 是 Mathlib 中的一个实例，位于命名空间 `FrameHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

/-
**CompleteLatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CompleteLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
/-
**CompleteLatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β where
  map_sSup f := f.map_sSup'
  map_sInf f := f.map_sInf'

/-- Reinterpret an order isomorphism as a morphism of complete lattices. -/
/-
**CompleteLatticeHom.OrderIso.toCompleteLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `Co
mpleteLatticeHom.OrderIso`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : CompleteLattice α] → [inst_1 :
 CompleteLattice β] → α ≃o β → CompleteLatticeHom α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an order isomorphism as a morphism of complete lattices.
-/
@[simps] def OrderIso.toCompleteLatticeHom (f : OrderIso α β) : CompleteLatticeHom α β where
  toFun := f
  map_sInf' := sInfHomClass.map_sInf f
  map_sSup' := sSupHomClass.map_sSup f

/-- Reinterpret a `CompleteLatticeHom` as a `BoundedLatticeHom`. -/
/-
**CompleteLatticeHom.toBoundedLatticeHom** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatt
iceHom`。
形式化陈述：toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β
参数：f : CompleteLatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `CompleteLatticeHom` as a `BoundedLatticeHom`.
-/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
/-
**CompleteLatticeHom.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `CompleteLatticeHom`
。
形式化陈述：toFun_eq_coe (f : CompleteLatticeHom α β) : f.toFun = f
参数：f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe (f : CompleteLatticeHom α β) : f.toFun = f := rfl

@[to_dual (attr := simp)]
/-
**CompleteLatticeHom.coe_tosInfHom** 是 Mathlib 中的一个引理，位于命名空间 `CompleteLatticeHom
`。
形式化陈述：coe_tosInfHom (f : CompleteLatticeHom α β) : ⇑f.tosInfHom = f
参数：f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_tosInfHom (f : CompleteLatticeHom α β) : ⇑f.tosInfHom = f := rfl

@[simp]
/-
**CompleteLatticeHom.coe_toBoundedLatticeHom** 是 Mathlib 中的一个引理，位于命名空间 `Complete
LatticeHom`。
形式化陈述：coe_toBoundedLatticeHom (f : CompleteLatticeHom α β) : ⇑f.toBoundedLattice
Hom = f
参数：f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toBoundedLatticeHom (f : CompleteLatticeHom α β) : ⇑f.toBoundedLatticeHom = f := rfl
/-
**CompleteLatticeHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : sInfHom α β)   (hf : ∀ (s : Set α), f.toFun (sSup s) = sSup (
f.toFun '' s)), ⇑{ tosInfHom := f, map_sSup' := hf } = ⇑f
参数：f : sInfHom α β；hf : ∀ (s : Set α), f.toFun (sSup s) = sSup (f.toFun '' s)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : sInfHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[ext]
/-
**CompleteLatticeHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：ext {f g : CompleteLatticeHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `CompleteLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**CompleteLatticeHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : CompleteLattice α] →      
 [inst_1 : CompleteLattice β] → (f : CompleteLatticeHom α β) → (f' : α → β) → f'
 = ⇑f → CompleteLatticeHom α β
参数：f : CompleteLatticeHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CompleteLatticeHom` with a new `toFun` equal to the old one. Useful t
o fix
definitional equalities.
-/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with tosInfHom := f.tosInfHom.copy f' h }

@[simp]
/-
**CompleteLatticeHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：coe_copy (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.cop
y f' h) = f'
参数：f : CompleteLatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CompleteLatticeHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：copy_eq (f : CompleteLatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f
' h = f
参数：f : CompleteLatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `CompleteLatticeHom`. -/
/-
**CompleteLatticeHom.id** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：(α : Type u_2) → [inst : CompleteLattice α] → CompleteLatticeHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `CompleteLatticeHom`.
-/
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }
/-
**CompleteLatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

@[simp, norm_cast]
/-
**CompleteLatticeHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：coe_id : ⇑(CompleteLatticeHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl

variable {α}
@[simp]
/-
**CompleteLatticeHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：id_apply (a : α) : CompleteLatticeHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl

/-- Composition of `CompleteLatticeHom`s as a `CompleteLatticeHom`. -/
/-
**CompleteLatticeHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteL
atticeHom α γ
参数：f : CompleteLatticeHom β γ；g : CompleteLatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `CompleteLatticeHom`s as a `CompleteLatticeHom`.
-/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with tosInfHom := f.tosInfHom.comp g.tosInfHom }

@[simp]
/-
**CompleteLatticeHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.c
omp g) = f ∘ g
参数：f : CompleteLatticeHom β γ；g : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**CompleteLatticeHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : 
α) : (f.comp g) a = f (g a)
参数：f : CompleteLatticeHom β γ；g : CompleteLatticeHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
/-
**CompleteLatticeHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ) (h : 
CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : CompleteLatticeHom γ δ；g : CompleteLatticeHom β γ；h : CompleteLatticeHom 
α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**CompleteLatticeHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = 
f
参数：f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLatticeHom.ext`：ext {f g : CompleteLatticeHom α β} (h : forall a
, f a = g a) : f = g
-/
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**CompleteLatticeHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = 
f
参数：f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLatticeHom.ext`：ext {f g : CompleteLatticeHom α β} (h : forall a
, f a = g a) : f = g
-/
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**CompleteLatticeHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`
。
形式化陈述：cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
 (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLatticeHom.ext`：ext {f g : CompleteLatticeHom α β} (h : forall a
, f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
/-
**CompleteLatticeHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β} 
(hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLatticeHom.ext`：ext {f g : CompleteLatticeHom α β} (h : forall a
, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompleteLatticeHom.comp_apply`：comp_apply (f : CompleteLatticeHom β γ) (
g : CompleteLatticeHom α β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[to_dual (attr := simps)
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/]
/-
**sSupHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `sSupHom`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : SupSet α] → [inst_1 : SupSet β] 
→ sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `sSupHom.map_sSup'`：∀ {α : Type u_8} {β : Type u_9} [inst : SupSet α] [in
st_1 : SupSet β] (self : sSupHom α β) (s : Set α),   self.toFun (sSup s) = sSup 
(self.t…
-/
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_sSup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_sInf'⟩

@[to_dual (attr := simp)]
/-
**sSupHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : sSupHom.dual (sSupHom.id α) = sInfHom.id _ :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：dual_comp (g : sSupHom β γ) (f : sSupHom α β) : sSupHom.dual (g.comp f) = 
(sSupHom.dual g).comp (sSupHom.dual f)
参数：g : sSupHom β γ；f : sSupHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) :
    sSupHom.dual (g.comp f) = (sSupHom.dual g).comp (sSupHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl

@[to_dual (attr := simp)]
/-
**sSupHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `sSupHom`。
形式化陈述：symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) : sSupHom.dual.
symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f)
参数：g : sInfHom βᵒᵈ γᵒᵈ；f : sInfHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
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
/-
**CompleteLatticeHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : CompleteLattice α] → [inst
_1 : CompleteLattice β] → CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a complete lattice homomorphism as a complete lattice homomorphism b
etween the dual
lattices.
-/
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩
  invFun f := ⟨sSupHom.dual f.tosSupHom, fun s ↦ f.map_sInf' s⟩

@[simp]
/-
**CompleteLatticeHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatt
iceHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : CompleteLatticeHom.dual (CompleteLatticeHom.id α) = CompleteLatticeHom.id _ :=
  rfl

@[simp]
/-
**CompleteLatticeHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) : Comp
leteLatticeHom.dual (g.comp f) = (CompleteLatticeHom.dual g).comp (CompleteLatti
ceHom.dual f)
参数：g : CompleteLatticeHom β γ；f : CompleteLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    CompleteLatticeHom.dual (g.comp f) =
      (CompleteLatticeHom.dual g).comp (CompleteLatticeHom.dual f) :=
  rfl

@[simp]
/-
**CompleteLatticeHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`
。
形式化陈述：symm_dual_id : CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = Co
mpleteLatticeHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl

@[simp]
/-
**CompleteLatticeHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHo
m`。
形式化陈述：symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒ
ᵈ βᵒᵈ) : CompleteLatticeHom.dual.symm (g.comp f) = (CompleteLatticeHom.dual.symm
 g).comp (CompleteLatticeHom.dual.symm f)
参数：g : CompleteLatticeHom βᵒᵈ γᵒᵈ；f : CompleteLatticeHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/-- `Set.preimage` as a complete lattice homomorphism.

See also `sSupHom.setImage`. -/
/-
**CompleteLatticeHom.setPreimage** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：setPreimage (f : α -> β) : CompleteLatticeHom (Set β) (Set α) where toFun
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.preimage` as a complete lattice homomorphism.

See also `sSupHom.setImage`.
-/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α) where
  toFun := preimage f
  map_sSup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_sInf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]

@[simp]
/-
**CompleteLatticeHom.coe_setPreimage** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeH
om`。
形式化陈述：coe_setPreimage (f : α -> β) : ⇑(setPreimage f) = preimage f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl

@[simp]
/-
**CompleteLatticeHom.setPreimage_apply** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLattic
eHom`。
形式化陈述：setPreimage_apply (f : α -> β) (s : Set β) : setPreimage f s = s.preimage 
f
参数：f : α -> β；s : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.preimage f :=
  rfl

@[simp]
/-
**CompleteLatticeHom.setPreimage_id** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHo
m`。
形式化陈述：setPreimage_id : setPreimage (id : α -> α) = CompleteLatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl

-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` syntactically)
/-
**CompleteLatticeHom.setPreimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLattice
Hom`。
形式化陈述：setPreimage_comp (g : β -> γ) (f : α -> β) : setPreimage (g ∘ f) = (setPre
image f).comp (setPreimage g)
参数：g : β -> γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl

end CompleteLatticeHom

/-
**Set.image_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.image_sSup {f : α -> β} (s : Set (Set α)) : f '' sSup s = sSup (image 
f '' s)
参数：s : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sUnion`：image_sUnion {f : α -> β} {s : Set (Set α)} : (f '' ⋃₀
 s) = ⋃₀ (image f '' s)
-/
theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  Set.image_sUnion

/-- Using `Set.image`, a function between types yields a `sSupHom` between their lattices of
subsets.

See also `CompleteLatticeHom.setPreimage`. -/
@[simps]
/-
**sSupHom.setImage** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sSupHom.setImage (f : α -> β) : sSupHom (Set α) (Set β) where toFun
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sSup`：Set.image_sSup {f : α -> β} (s : Set (Set α)) : f '' sSu
p s = sSup (image f '' s)

--- 原说明 ---
Using `Set.image`, a function between types yields a `sSupHom` between their lat
tices of
subsets.

See also `CompleteLatticeHom.setPreimage`.
-/
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β) where
  toFun := image f
  map_sSup' := Set.image_sSup

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
/-
**Equiv.toOrderIsoSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β where toFun s
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence of types yields an order isomorphism between their lattices of su
bsets.
-/
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β where
  toFun s := e '' s
  invFun s := e.symm '' s
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id, image_id']
  map_rel_iff' :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩

variable [CompleteLattice α] (x : α × α)

/-- The map `(a, b) ↦ a ⊔ b` as a `sSupHom`. -/
/-
**supsSupHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：supsSupHom : sSupHom (α × α) α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `(a, b) ↦ a ⊔ b` as a `sSupHom`.
-/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_sSup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]

/-- The map `(a, b) ↦ a ⊓ b` as an `sInfHom`. -/
/-
**infsInfHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：infsInfHom : sInfHom (α × α) α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `(a, b) ↦ a ⊓ b` as an `sInfHom`.
-/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_sInf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]

@[simp, norm_cast]
/-
**supsSupHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl

@[simp, norm_cast]
/-
**infsInfHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
