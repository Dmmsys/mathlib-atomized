/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Set.Functor
public import Mathlib.Order.Sublattice
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete Sublattices

This file defines complete sublattices. These are subsets of complete lattices which are closed
under arbitrary suprema and infima. As a standard example one could take the complete sublattice of
invariant submodules of some module with respect to a linear map.

## Main definitions:
* `CompleteSublattice`: the definition of a complete sublattice
* `CompleteSublattice.mk'`: an alternate constructor for a complete sublattice, demanding fewer
  hypotheses
* `CompleteSublattice.instCompleteLattice`: a complete sublattice is a complete lattice
* `CompleteSublattice.map`: complete sublattices push forward under complete lattice morphisms.
* `CompleteSublattice.comap`: complete sublattices pull back under complete lattice morphisms.

-/

@[expose] public section

open Function Set

variable (α β : Type*) [CompleteLattice α] [CompleteLattice β] (f : CompleteLatticeHom α β)

/-- A complete sublattice is a subset of a complete lattice that is closed under arbitrary suprema
and infima. -/
/-
**CompleteSublattice** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [CompleteLattice α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete sublattice is a subset of a complete lattice that is closed under arb
itrary suprema
and infima.
-/
structure CompleteSublattice extends Sublattice α where
  sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier
  sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier

variable {α β}

namespace CompleteSublattice

/-- To check that a subset is a complete sublattice, one does not need to check that it is closed
under binary `Sup` since this follows from the stronger `sSup` condition. Likewise for infima. -/
/-
**CompleteSublattice.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CompleteSublattice`。
形式化陈述：{α : Type u_1} →   [inst : CompleteLattice α] →     (carrier : Set α) →   
    (∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier) →         (∀ ⦃s : Set α⦄, s 
⊆ carrier → sInf s ∈ carrier) → CompleteSublattice α
参数：carrier : Set α；∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier；∀ ⦃s : Set α⦄, 
s ⊆ carrier → sInf s ∈ carrier。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To check that a subset is a complete sublattice, one does not need to check that
 it is closed
under binary `Sup` since this follows from the stronger `sSup` condition. Likewi
se for infima.
-/
@[simps] def mk' (carrier : Set α)
    (sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier)
    (sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier) :
    CompleteSublattice α where
  carrier := carrier
  sSupClosed' := sSupClosed'
  sInfClosed' := sInfClosed'
  supClosed' := fun x hx y hy ↦ by
    suffices x ⊔ y = sSup {x, y} by exact this ▸ sSupClosed' (fun z hz ↦ by aesop)
    simp [sSup_singleton]
  infClosed' := fun x hx y hy ↦ by
    suffices x ⊓ y = sInf {x, y} by exact this ▸ sInfClosed' (fun z hz ↦ by aesop)
    simp [sInf_singleton]

variable {L : CompleteSublattice α}
/-
**CompleteSublattice.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
形式化陈述：instSetLike : SetLike (CompleteSublattice α) α where coe L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (CompleteSublattice α) α where
  coe L := L.carrier
  coe_injective L M h := by cases L; cases M; congr; exact SetLike.coe_injective h
/-
**CompleteSublattice.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (CompleteSublattice α) := .ofSetLike (CompleteSublattice α) α
/-
**CompleteSublattice.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：top_mem : ⊤ in L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_empty`：∀ {α : Type u_1} [inst : CompleteLattice α], sInf ∅ = ⊤
· 使用定理 `CompleteSublattice.sInfClosed'`：∀ {α : Type u_1} [inst : CompleteLattice
 α] (self : CompleteSublattice α) ⦃s : Set α⦄,   s ⊆ self.carrier → sInf s ∈ sel
f.carrier
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem top_mem : ⊤ ∈ L := by simpa using! L.sInfClosed' <| empty_subset _
/-
**CompleteSublattice.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：bot_mem : ⊥ in L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `CompleteSublattice.sSupClosed'`：∀ {α : Type u_1} [inst : CompleteLattice
 α] (self : CompleteSublattice α) ⦃s : Set α⦄,   s ⊆ self.carrier → sSup s ∈ sel
f.carrier
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem bot_mem : ⊥ ∈ L := by simpa using! L.sSupClosed' <| empty_subset _
/-
**CompleteSublattice.instBot** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
形式化陈述：instBot : Bot L where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.bot_mem`：bot_mem : ⊥ in L
-/
instance instBot : Bot L where
  bot := ⟨⊥, bot_mem⟩
/-
**CompleteSublattice.instTop** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
形式化陈述：instTop : Top L where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.top_mem`：top_mem : ⊤ in L
-/
instance instTop : Top L where
  top := ⟨⊤, top_mem⟩
/-
**CompleteSublattice.instSupSet** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
形式化陈述：instSupSet : SupSet L where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSupSet : SupSet L where
  sSup s := ⟨sSup <| (↑) '' s, L.sSupClosed' image_val_subset⟩
/-
**CompleteSublattice.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
形式化陈述：instInfSet : InfSet L where sInf s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfSet : InfSet L where
  sInf s := ⟨sInf <| (↑) '' s, L.sInfClosed' image_val_subset⟩
/-
**CompleteSublattice.sSupClosed** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：sSupClosed {s : Set α} (h : s subseteq L) : sSup s in L
参数：h : s subseteq L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.sSupClosed'`：∀ {α : Type u_1} [inst : CompleteLattice
 α] (self : CompleteSublattice α) ⦃s : Set α⦄,   s ⊆ self.carrier → sSup s ∈ sel
f.carrier
-/
theorem sSupClosed {s : Set α} (h : s ⊆ L) : sSup s ∈ L := L.sSupClosed' h
/-
**CompleteSublattice.sInfClosed** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：sInfClosed {s : Set α} (h : s subseteq L) : sInf s in L
参数：h : s subseteq L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.sInfClosed'`：∀ {α : Type u_1} [inst : CompleteLattice
 α] (self : CompleteSublattice α) ⦃s : Set α⦄,   s ⊆ self.carrier → sInf s ∈ sel
f.carrier
-/
theorem sInfClosed {s : Set α} (h : s ⊆ L) : sInf s ∈ L := L.sInfClosed' h
/-
**CompleteSublattice.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α}, ↑⊥
 = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_bot : (↑(⊥ : L) : α) = ⊥ := rfl
/-
**CompleteSublattice.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α}, ↑⊤
 = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_top : (↑(⊤ : L) : α) = ⊤ := rfl
/-
**CompleteSublattice.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} (S 
: Set ↥L),   ↑(sSup S) = sSup {x | ∃ s ∈ S, ↑s = x}
参数：S : Set ↥L；sSup S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_sSup (S : Set L) : (↑(sSup S) : α) = sSup {(s : α) | s ∈ S} := rfl
/-
**CompleteSublattice.coe_sSup'** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：coe_sSup' (S : Set L) : (↑(sSup S) : α) = ⨆ N in S, (N : α)
参数：S : Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteSublattice.coe_sSup`：∀ {α : Type u_1} [inst : CompleteLattice α]
 {L : CompleteSublattice α} (S : Set ↥L),   ↑(sSup S) = sSup {x | ∃ s ∈ S, ↑s = 
x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
theorem coe_sSup' (S : Set L) : (↑(sSup S) : α) = ⨆ N ∈ S, (N : α) := by
  rw [coe_sSup, ← Set.image, sSup_image]
/-
**CompleteSublattice.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} (S 
: Set ↥L),   ↑(sInf S) = sInf {x | ∃ s ∈ S, ↑s = x}
参数：S : Set ↥L；sInf S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_sInf (S : Set L) : (↑(sInf S) : α) = sInf {(s : α) | s ∈ S} := rfl
/-
**CompleteSublattice.coe_sInf'** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：coe_sInf' (S : Set L) : (↑(sInf S) : α) = ⨅ N in S, (N : α)
参数：S : Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteSublattice.coe_sInf`：∀ {α : Type u_1} [inst : CompleteLattice α]
 {L : CompleteSublattice α} (S : Set ↥L),   ↑(sInf S) = sInf {x | ∃ s ∈ S, ↑s = 
x}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem coe_sInf' (S : Set L) : (↑(sInf S) : α) = ⨅ N ∈ S, (N : α) := by
  rw [coe_sInf, ← Set.image, sInf_image]
/-
**CompleteSublattice.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} {ι 
: Sort u_3} (f : ι → ↥L),   ↑(iSup f) = ⨆ i, ↑(f i)
参数：f : ι → ↥L；iSup f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `CompleteSublattice.coe_sSup'`：coe_sSup' (S : Set L) : (↑(sSup S) : α) = 
⨆ N in S, (N : α)
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
@[simp] theorem coe_iSup {ι} (f : ι → L) : (↑(iSup f) : α) = ⨆ i, (f i : α) := by
  rw [iSup, coe_sSup', iSup_range]
/-
**CompleteSublattice.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} {ι 
: Sort u_3} (f : ι → ↥L),   ↑(iInf f) = ⨅ i, ↑(f i)
参数：f : ι → ↥L；iInf f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `CompleteSublattice.coe_sInf'`：coe_sInf' (S : Set L) : (↑(sInf S) : α) = 
⨅ N in S, (N : α)
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
@[simp] theorem coe_iInf {ι} (f : ι → L) : (↑(iInf f) : α) = ⨅ i, (f i : α) := by
  rw [iInf, coe_sInf', iInf_range]

-- Redeclaring to get proper keys for these instances
/-
**CompleteSublattice.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max {x // x ∈ L} := Sublattice.instSupCoe
/-
**CompleteSublattice.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min {x // x ∈ L} := Sublattice.instInfCoe
/-
**CompleteSublattice.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSubl
attice`。
形式化陈述：instCompleteLattice : CompleteLattice L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSublattice.coe_sSup'`：coe_sSup' (S : Set L) : (↑(sSup S) : α) = 
⨆ N in S, (N : α)
· 使用定理 `CompleteSublattice.coe_sInf'`：coe_sInf' (S : Set L) : (↑(sInf S) : α) = 
⨅ N in S, (N : α)
· 使用定理 `CompleteSublattice.coe_top`：∀ {α : Type u_1} [inst : CompleteLattice α] 
{L : CompleteSublattice α}, ↑⊤ = ⊤
· 使用定理 `CompleteSublattice.coe_bot`：∀ {α : Type u_1} [inst : CompleteLattice α] 
{L : CompleteSublattice α}, ↑⊥ = ⊥
-/
instance instCompleteLattice : CompleteLattice L :=
  Subtype.coe_injective.completeLattice _ .rfl .rfl
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

/-- The natural complete lattice hom from a complete sublattice to the original lattice. -/
/-
**CompleteSublattice.subtype** 是 Mathlib 中的一个定义，位于命名空间 `CompleteSublattice`。
形式化陈述：subtype (L : CompleteSublattice α) : CompleteLatticeHom L α where toFun
参数：L : CompleteSublattice α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural complete lattice hom from a complete sublattice to the original latt
ice.
-/
def subtype (L : CompleteSublattice α) : CompleteLatticeHom L α where
  toFun := Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl
/-
**CompleteSublattice.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] (L : CompleteSublattice α), ⇑L
.subtype = Subtype.val
参数：L : CompleteSublattice α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_subtype (L : CompleteSublattice α) : L.subtype = ((↑) : L → α) := rfl
/-
**CompleteSublattice.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `CompleteSublattice
`。
形式化陈述：subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a
参数：L : Sublattice α；a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl
/-
**CompleteSublattice.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `CompleteSublat
tice`。
形式化陈述：subtype_injective (L : CompleteSublattice α) : Injective subtype L
参数：L : CompleteSublattice α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective (L : CompleteSublattice α) :
    Injective <| subtype L := Subtype.coe_injective

/-- The push forward of a complete sublattice under a complete lattice hom is a complete
sublattice. -/
/-
**CompleteSublattice.map** 是 Mathlib 中的一个定义，位于命名空间 `CompleteSublattice`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : CompleteLattice α] →      
 [inst_1 : CompleteLattice β] → CompleteLatticeHom α β → CompleteSublattice α → 
CompleteSublattice β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The push forward of a complete sublattice under a complete lattice hom is a comp
lete
sublattice.
-/
@[simps] def map (L : CompleteSublattice α) : CompleteSublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
  sSupClosed' := fun s hs ↦ by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sSup]
    exact mem_image_of_mem f (sSupClosed ht)
  sInfClosed' := fun s hs ↦ by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sInf]
    exact mem_image_of_mem f (sInfClosed ht)
/-
**CompleteSublattice.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : CompleteLatticeHom α β)   {L : CompleteSublattice α} {b : β},
 b ∈ CompleteSublattice.map f L ↔ ∃ a ∈ L, f a = b
参数：f : CompleteLatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := Iff.rfl

/-- The pull back of a complete sublattice under a complete lattice hom is a complete sublattice. -/
/-
**CompleteSublattice.comap** 是 Mathlib 中的一个定义，位于命名空间 `CompleteSublattice`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : CompleteLattice α] →      
 [inst_1 : CompleteLattice β] → CompleteLatticeHom α β → CompleteSublattice β → 
CompleteSublattice α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pull back of a complete sublattice under a complete lattice hom is a complet
e sublattice.
-/
@[simps] def comap (L : CompleteSublattice β) : CompleteSublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage f
  infClosed' := L.infClosed.preimage f
  sSupClosed' s hs := by
    simpa only [mem_preimage, map_sSup, SetLike.mem_coe] using sSupClosed
      <| mapsTo_iff_image_subset.mp hs
  sInfClosed' s hs := by
    simpa only [mem_preimage, map_sInf, SetLike.mem_coe] using sInfClosed
      <| mapsTo_iff_image_subset.mp hs
/-
**CompleteSublattice.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] [inst_1 : Compl
eteLattice β] (f : CompleteLatticeHom α β)   {L : CompleteSublattice β} {a : α},
 a ∈ CompleteSublattice.comap f L ↔ f a ∈ L
参数：f : CompleteLatticeHom α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_comap {L : CompleteSublattice β} {a : α} : a ∈ L.comap f ↔ f a ∈ L := Iff.rfl
/-
**CompleteSublattice.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`
。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} {a 
b : ↥L}, Disjoint a b ↔ Disjoint ↑a ↑b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sublattice.coe_inf`：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice 
α} (a b : ↥L), ↑(a ⊓ b) = ↑a ⊓ ↑b
· 使用定理 `CompleteSublattice.coe_bot`：∀ {α : Type u_1} [inst : CompleteLattice α] 
{L : CompleteSublattice α}, ↑⊥ = ⊥
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma disjoint_iff {a b : L} :
    Disjoint a b ↔ Disjoint (a : α) (b : α) := by
  rw [disjoint_iff, disjoint_iff, ← Sublattice.coe_inf, ← coe_bot (L := L),
    Subtype.coe_injective.eq_iff]
/-
**CompleteSublattice.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattic
e`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} {a 
b : ↥L}, Codisjoint a b ↔ Codisjoint ↑a ↑b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sublattice.coe_sup`：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattice 
α} (a b : ↥L), ↑(a ⊔ b) = ↑a ⊔ ↑b
· 使用定理 `CompleteSublattice.coe_top`：∀ {α : Type u_1} [inst : CompleteLattice α] 
{L : CompleteSublattice α}, ↑⊤ = ⊤
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma codisjoint_iff {a b : L} :
    Codisjoint a b ↔ Codisjoint (a : α) (b : α) := by
  rw [codisjoint_iff, codisjoint_iff, ← Sublattice.coe_sup, ← coe_top (L := L),
    Subtype.coe_injective.eq_iff]
/-
**CompleteSublattice.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] {L : CompleteSublattice α} {a 
b : ↥L}, IsCompl a b ↔ IsCompl ↑a ↑b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `CompleteSublattice.disjoint_iff`：∀ {α : Type u_1} [inst : CompleteLattic
e α] {L : CompleteSublattice α} {a b : ↥L}, Disjoint a b ↔ Disjoint ↑a ↑b
· 使用定理 `CompleteSublattice.codisjoint_iff`：∀ {α : Type u_1} [inst : CompleteLatt
ice α] {L : CompleteSublattice α} {a b : ↥L}, Codisjoint a b ↔ Codisjoint ↑a ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isCompl_iff {a b : L} :
    IsCompl a b ↔ IsCompl (a : α) (b : α) := by
  rw [isCompl_iff, isCompl_iff, CompleteSublattice.disjoint_iff, CompleteSublattice.codisjoint_iff]
/-
**CompleteSublattice.isComplemented_iff** 是 Mathlib 中的一个引理，位于命名空间 `CompleteSubla
ttice`。
形式化陈述：isComplemented_iff : ComplementedLattice L ↔ forall a in L, exists b in L,
 IsCompl a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompleteSublattice.isCompl_iff`：∀ {α : Type u_1} [inst : CompleteLattice
 α] {L : CompleteSublattice α} {a b : ↥L}, IsCompl a b ↔ IsCompl ↑a ↑b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma isComplemented_iff : ComplementedLattice L ↔ ∀ a ∈ L, ∃ b ∈ L, IsCompl a b := by
  refine ⟨fun ⟨h⟩ a ha ↦ ?_, fun h ↦ ⟨fun ⟨a, ha⟩ ↦ ?_⟩⟩
  · obtain ⟨b, hb⟩ := h ⟨a, ha⟩
    exact ⟨b, b.property, CompleteSublattice.isCompl_iff.mp hb⟩
  · obtain ⟨b, hb, hb'⟩ := h a ha
    exact ⟨⟨b, hb⟩, CompleteSublattice.isCompl_iff.mpr hb'⟩
/-
**CompleteSublattice.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteSublattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (CompleteSublattice α) := ⟨mk' univ (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _)⟩

variable (L)

/-- Copy of a complete sublattice with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
/-
**CompleteSublattice.copy** 是 Mathlib 中的一个定义，位于命名空间 `CompleteSublattice`。
形式化陈述：{α : Type u_1} → [inst : CompleteLattice α] → (L : CompleteSublattice α) →
 (s : Set α) → s = ↑L → CompleteSublattice α
参数：L : CompleteSublattice α；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a complete sublattice with a new `carrier` equal to the old one. Useful 
to fix
definitional equalities.
-/
protected def copy (s : Set α) (hs : s = L) : CompleteSublattice α :=
  mk' s (hs ▸ L.sSupClosed') (hs ▸ L.sInfClosed')
/-
**CompleteSublattice.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CompleteSublattice`。
形式化陈述：∀ {α : Type u_1} [inst : CompleteLattice α] (L : CompleteSublattice α) (s 
: Set α) (hs : s = ↑L), ↑(L.copy s hs) = s
参数：L : CompleteSublattice α；s : Set α；hs : s = ↑L；L.copy s hs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_copy (s : Set α) (hs) : L.copy s hs = s := rfl
/-
**CompleteSublattice.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `CompleteSublattice`。
形式化陈述：copy_eq (s : Set α) (hs) : L.copy s hs = L
参数：s : Set α；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma copy_eq (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

end CompleteSublattice

namespace CompleteLatticeHom

/-- The range of a `CompleteLatticeHom` is a `CompleteSublattice`.

See Note [range copy pattern]. -/
/-
**CompleteLatticeHom.range** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLatticeHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : CompleteLattice α] → [inst
_1 : CompleteLattice β] → CompleteLatticeHom α β → CompleteSublattice β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a `CompleteLatticeHom` is a `CompleteSublattice`.

See Note [range copy pattern].
-/
protected def range : CompleteSublattice β :=
  (CompleteSublattice.map f ⊤).copy (range f) image_univ.symm
/-
**CompleteLatticeHom.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLatticeHom`。
形式化陈述：range_coe : (f.range : Set β) = range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_coe : (f.range : Set β) = range f := rfl

/-- We can regard a complete lattice homomorphism as an order equivalence to its range. -/
/-
**CompleteLatticeHom.toOrderIsoRangeOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Compl
eteLatticeHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : CompleteLattice α] →      
 [inst_1 : CompleteLattice β] → (f : CompleteLatticeHom α β) → Function.Injectiv
e ⇑f → α ≃o ↥f.range
参数：f : CompleteLatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can regard a complete lattice homomorphism as an order equivalence to its ran
ge.
-/
@[simps! apply] noncomputable def toOrderIsoRangeOfInjective (hf : Injective f) : α ≃o f.range :=
  (orderEmbeddingOfInjective f hf).orderIso

end CompleteLatticeHom

