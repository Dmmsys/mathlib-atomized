/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Module.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Pointwise operations on sets of reals

This file relates `sInf (a • s)`/`sSup (a • s)` with `a • sInf s`/`a • sSup s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

## TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/

public section

assert_not_exists Finset

open Set

open scoped Pointwise

variable {ι : Sort*} {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [IsOrderedModule α ℝ] {a : α}

/-
**Real.sInf_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.sInf_smul_of_nonneg (ha : 0 <= a) (s : Set Real) : sInf (a • s) = a •
 sInf s
参数：ha : 0 <= a；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `csInf_singleton`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOr
derInf α] (a : α), sInf {a} = a
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用定理 `OrderIso.map_csInf'`：map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddBelow s) : e (sInf s) = sInf (e '' s)
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddBelow_smul_iff_of_pos`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst
_4 : MulAction…
-/
theorem Real.sInf_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]
/-
**Real.smul_iInf_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.smul_iInf_of_nonneg (ha : 0 <= a) (f : ι -> Real) : (a • ⨅ i, f i) = 
⨅ i, a • f i
参数：ha : 0 <= a；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sInf_smul_of_nonneg`：Real.sInf_smul_of_nonneg (ha : 0 <= a) (s : Se
t Real) : sInf (a • s) = a • sInf s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem Real.smul_iInf_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonneg ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
/-
**Real.sSup_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.sSup_smul_of_nonneg (ha : 0 <= a) (s : Set Real) : sSup (a • s) = a •
 sSup s
参数：ha : 0 <= a；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `csSup_singleton`：csSup_singleton (a : α) : sSup {a} = a
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用定理 `OrderIso.map_csSup'`：map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s)
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddAbove_smul_iff_of_pos`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst
_4 : MulAction…
-/
theorem Real.sSup_smul_of_nonneg (ha : 0 ≤ a) (s : Set ℝ) : sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]
/-
**Real.smul_iSup_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.smul_iSup_of_nonneg (ha : 0 <= a) (f : ι -> Real) : (a • ⨆ i, f i) = 
⨆ i, a • f i
参数：ha : 0 <= a；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sSup_smul_of_nonneg`：Real.sSup_smul_of_nonneg (ha : 0 <= a) (s : Se
t Real) : sSup (a • s) = a • sSup s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem Real.smul_iSup_of_nonneg (ha : 0 ≤ a) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonneg ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end MulActionWithZero

section Module

variable [Module α ℝ] [IsOrderedModule α ℝ] {a : α}

/-
**Real.sInf_smul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.sInf_smul_of_nonpos (ha : a <= 0) (s : Set Real) : sInf (a • s) = a •
 sSup s
参数：ha : a <= 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `csInf_singleton`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOr
derInf α] (a : α), sInf {a} = a
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `OrderIso.map_csSup'`：map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s)
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddBelow_smul_iff_of_neg`：∀ {α : Type u_1} {β : Type u_2} [inst : Field 
α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] 
[inst_4 : Part…
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
-/
theorem Real.sInf_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sInf (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csSup' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]
/-
**Real.smul_iSup_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.smul_iSup_of_nonpos (ha : a <= 0) (f : ι -> Real) : (a • ⨆ i, f i) = 
⨅ i, a • f i
参数：ha : a <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sInf_smul_of_nonpos`：Real.sInf_smul_of_nonpos (ha : a <= 0) (s : Se
t Real) : sInf (a • s) = a • sSup s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem Real.smul_iSup_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (Real.sInf_smul_of_nonpos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm
/-
**Real.sSup_smul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.sSup_smul_of_nonpos (ha : a <= 0) (s : Set Real) : sSup (a • s) = a •
 sInf s
参数：ha : a <= 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `Real.sSup_empty`：sSup_empty : sSup (∅ : Set Real) = 0
· 使用定理 `Real.sInf_empty`：sInf_empty : sInf (∅ : Set Real) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Set.zero_smul_set`：∀ {α : Type u_1} {β : Type u_2} [inst : Zero α] [inst
_1 : Zero β] [inst_2 : SMulWithZero α β] {s : Set β},   s.Nonempty → 0 • s = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `csSup_singleton`：csSup_singleton (a : α) : sSup {a} = a
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `OrderIso.map_csInf'`：map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddBelow s) : e (sInf s) = sInf (e '' s)
· 使用引理 `Real.sSup_of_not_bddAbove`：sSup_of_not_bddAbove (hs : ¬BddAbove s) : sSu
p s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddAbove_smul_iff_of_neg`：∀ {α : Type u_1} {β : Type u_2} [inst : Field 
α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] 
[inst_4 : Part…
· 使用定理 `Real.sInf_of_not_bddBelow`：sInf_of_not_bddBelow (hs : ¬BddBelow s) : sIn
f s = 0
-/
theorem Real.sSup_smul_of_nonpos (ha : a ≤ 0) (s : Set ℝ) : sSup (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual ℝ ha').map_csInf' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]
/-
**Real.smul_iInf_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.smul_iInf_of_nonpos (ha : a <= 0) (f : ι -> Real) : (a • ⨅ i, f i) = 
⨆ i, a • f i
参数：ha : a <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sSup_smul_of_nonpos`：Real.sSup_smul_of_nonpos (ha : a <= 0) (s : Se
t Real) : sSup (a • s) = a • sInf s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem Real.smul_iInf_of_nonpos (ha : a ≤ 0) (f : ι → ℝ) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (Real.sSup_smul_of_nonpos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : ℝ}

/-
**Real.mul_iInf_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.mul_iInf_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (r * ⨅ i, f i) = ⨅
 i, r * f i
参数：ha : 0 <= r；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.smul_iInf_of_nonneg`：Real.smul_iInf_of_nonneg (ha : 0 <= a) (f : ι 
-> Real) : (a • ⨅ i, f i) = ⨅ i, a • f i
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem Real.mul_iInf_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_iInf_of_nonneg ha f
/-
**Real.mul_iSup_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (r * ⨆ i, f i) = ⨆
 i, r * f i
参数：ha : 0 <= r；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.smul_iSup_of_nonneg`：Real.smul_iSup_of_nonneg (ha : 0 <= a) (f : ι 
-> Real) : (a • ⨆ i, f i) = ⨆ i, a • f i
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem Real.mul_iSup_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_iSup_of_nonneg ha f
/-
**Real.mul_iInf_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.mul_iInf_of_nonpos (ha : r <= 0) (f : ι -> Real) : (r * ⨅ i, f i) = ⨆
 i, r * f i
参数：ha : r <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.smul_iInf_of_nonpos`：Real.smul_iInf_of_nonpos (ha : a <= 0) (f : ι 
-> Real) : (a • ⨅ i, f i) = ⨆ i, a • f i
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem Real.mul_iInf_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_iInf_of_nonpos ha f
/-
**Real.mul_iSup_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.mul_iSup_of_nonpos (ha : r <= 0) (f : ι -> Real) : (r * ⨆ i, f i) = ⨅
 i, r * f i
参数：ha : r <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.smul_iSup_of_nonpos`：Real.smul_iSup_of_nonpos (ha : a <= 0) (f : ι 
-> Real) : (a • ⨆ i, f i) = ⨅ i, a • f i
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
-/
theorem Real.mul_iSup_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_iSup_of_nonpos ha f
/-
**Real.iInf_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.iInf_mul_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (⨅ i, f i) * r = ⨅
 i, f i * r
参数：ha : 0 <= r；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.mul_iInf_of_nonneg`：Real.mul_iInf_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨅ i, f i) = ⨅ i, r * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.iInf_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]
/-
**Real.iSup_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.iSup_mul_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (⨆ i, f i) * r = ⨆
 i, f i * r
参数：ha : 0 <= r；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.mul_iSup_of_nonneg`：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨆ i, r * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.iSup_mul_of_nonneg (ha : 0 ≤ r) (f : ι → ℝ) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]
/-
**Real.iInf_mul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.iInf_mul_of_nonpos (ha : r <= 0) (f : ι -> Real) : (⨅ i, f i) * r = ⨆
 i, f i * r
参数：ha : r <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.mul_iInf_of_nonpos`：Real.mul_iInf_of_nonpos (ha : r <= 0) (f : ι ->
 Real) : (r * ⨅ i, f i) = ⨆ i, r * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.iInf_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]
/-
**Real.iSup_mul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.iSup_mul_of_nonpos (ha : r <= 0) (f : ι -> Real) : (⨆ i, f i) * r = ⨅
 i, f i * r
参数：ha : r <= 0；f : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.mul_iSup_of_nonpos`：Real.mul_iSup_of_nonpos (ha : r <= 0) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨅ i, r * f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Real.iSup_mul_of_nonpos (ha : r ≤ 0) (f : ι → ℝ) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]

end Mul

