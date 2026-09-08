/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Group.Action

/-!
# A.e. stabilizer of a set

In this file we define the a.e. stabilizer of a set under a measure-preserving group action.

The a.e. stabilizer `MulAction.aestabilizer G μ s` of a set `s`
is the set of the elements `g : G` such that `s` is a.e.-invariant under `(g • ·)`.

For a measure-preserving group action, this set is a subgroup of `G`.
If the set is null or conull, then this subgroup is the whole group.
The converse is true for an ergodic action and a null-measurable set.

## Implementation notes

We define the a.e. stabilizer as a bundled `Subgroup`,
thus we do not deal with monoid actions.

Also, many lemmas in this file are true for a *quasi-measure-preserving* action,
but we don't have the corresponding typeclass.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Pointwise

variable (G : Type*) {α : Type*} [Group G] [MulAction G α]
  {_ : MeasurableSpace α} (μ : Measure α) [SMulInvariantMeasure G α μ]

namespace MulAction

set_option backward.isDefEq.respectTransparency false in
/-- A.e. stabilizer of a set under a group action. -/
@[to_additive (attr := simps) /-- A.e. stabilizer of a set under an additive group action. -/]
/-
**MulAction.aestabilizer** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：aestabilizer (s : Set α) : Subgroup G where carrier
参数：s : Set α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
A.e. stabilizer of a set under a group action.
-/
def aestabilizer (s : Set α) : Subgroup G where
  carrier := {g | g • s =ᵐ[μ] s}
  one_mem' := by simp
  -- TODO: `calc` would be more readable but fails because of defeq abuse
  mul_mem' {g₁ g₂} h₁ h₂ := by simpa only [smul_smul] using! ((smul_set_ae_eq g₁).2 h₂).trans h₁
  inv_mem' {g} h := by simpa using! (smul_set_ae_eq g⁻¹).2 h.out.symm

variable {G μ}
variable {g : G} {s t : Set α}

@[to_additive (attr := simp)]
/-
**MulAction.mem_aestabilizer** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：mem_aestabilizer : g in aestabilizer G μ s ↔ g • s =ᵐ[μ] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_aestabilizer : g ∈ aestabilizer G μ s ↔ g • s =ᵐ[μ] s := .rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MulAction.stabilizer_le_aestabilizer** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_le_aestabilizer (s : Set α) : stabilizer G s <= aestabilizer G 
μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma stabilizer_le_aestabilizer (s : Set α) : stabilizer G s ≤ aestabilizer G μ s := by
  intro g hg
  simp_all

@[to_additive (attr := simp)]
/-
**MulAction.aestabilizer_empty** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：aestabilizer_empty : aestabilizer G μ ∅ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aestabilizer_empty : aestabilizer G μ ∅ = ⊤ := top_unique fun _ _ ↦ by simp

@[to_additive (attr := simp)]
/-
**MulAction.aestabilizer_univ** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：aestabilizer_univ : aestabilizer G μ univ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma aestabilizer_univ : aestabilizer G μ univ = ⊤ := top_unique fun _ _ ↦ by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MulAction.aestabilizer_congr** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：aestabilizer_congr (h : s =ᵐ[μ] t) : aestabilizer G μ s = aestabilizer G μ
 t
参数：h : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.mem_aestabilizer`：mem_aestabilizer : g in aestabilizer G μ s ↔
 g • s =ᵐ[μ] s
· 使用定理 `Filter.EventuallyEq.congr_right`：∀ {α : Type u} {β : Type v} {l : Filter
 α} {f g h : α → β}, g =ᶠ[l] h → (f =ᶠ[l] g ↔ f =ᶠ[l] h)
· 使用定理 `Filter.EventuallyEq.congr_left`：∀ {α : Type u} {β : Type v} {l : Filter 
α} {f g h : α → β}, f =ᶠ[l] g → (f =ᶠ[l] h ↔ g =ᶠ[l] h)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.smul_set_ae_eq`：smul_set_ae_eq (c : G) {s t : Set α} : c •
 s =ᵐ[μ] c • t ↔ s =ᵐ[μ] t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma aestabilizer_congr (h : s =ᵐ[μ] t) : aestabilizer G μ s = aestabilizer G μ t := by
  ext g
  rw [mem_aestabilizer, mem_aestabilizer, h.congr_right, ((smul_set_ae_eq g).2 h).congr_left]
/-
**MulAction.aestabilizer_of_aeconst** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：aestabilizer_of_aeconst (hs : EventuallyConst s (ae μ)) : aestabilizer G μ
 s = ⊤
参数：hs : EventuallyConst s (ae μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventuallyConst_set'`：eventuallyConst_set' {s : Set α} : Eventual
lyConst s l ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.aestabilizer_congr`：aestabilizer_congr (h : s =ᵐ[μ] t) : aesta
bilizer G μ s = aestabilizer G μ t
· 使用引理 `MulAction.aestabilizer_empty`：aestabilizer_empty : aestabilizer G μ ∅ = 
⊤
· 使用引理 `MulAction.aestabilizer_univ`：aestabilizer_univ : aestabilizer G μ univ =
 ⊤
-/
lemma aestabilizer_of_aeconst (hs : EventuallyConst s (ae μ)) : aestabilizer G μ s = ⊤ := by
  refine top_unique fun g _ ↦ ?_
  cases eventuallyConst_set'.mp hs with
  | inl h => simp [aestabilizer_congr h]
  | inr h => simp [aestabilizer_congr h]

end MulAction

variable {G μ}
variable {x y : G} {s : Set α}

namespace MeasureTheory

@[to_additive]
/-
**MeasureTheory.smul_ae_eq_self_of_mem_zpowers** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：smul_ae_eq_self_of_mem_zpowers (hs : (x • s : Set α) =ᵐ[μ] s) (hy : y in S
ubgroup.zpowers x) : (y • s : Set α) =ᵐ[μ] s
参数：hs : (x • s : Set α) =ᵐ[μ] s；hy : y in Subgroup.zpowers x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.zpowers_le`：zpowers_le {g : G} {H : Subgroup G} : zpowers g <= 
H ↔ g in H
· 使用引理 `MulAction.mem_aestabilizer`：mem_aestabilizer : g in aestabilizer G μ s ↔
 g • s =ᵐ[μ] s
-/
theorem smul_ae_eq_self_of_mem_zpowers (hs : (x • s : Set α) =ᵐ[μ] s)
    (hy : y ∈ Subgroup.zpowers x) : (y • s : Set α) =ᵐ[μ] s := by
  rw [← MulAction.mem_aestabilizer, ← Subgroup.zpowers_le] at hs
  exact hs hy

@[to_additive]
/-
**MeasureTheory.inv_smul_ae_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：inv_smul_ae_eq_self (hs : (x • s : Set α) =ᵐ[μ] s) : (x⁻¹ • s : Set α) =ᵐ[
μ] s
参数：hs : (x • s : Set α) =ᵐ[μ] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem inv_smul_ae_eq_self (hs : (x • s : Set α) =ᵐ[μ] s) : (x⁻¹ • s : Set α) =ᵐ[μ] s :=
  inv_mem (s := MulAction.aestabilizer G μ s) hs

end MeasureTheory

