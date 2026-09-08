/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/
module

public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Properness of the p-adic numbers

In this file, we prove that `ℤ_[p]` is totally bounded and compact,
and that `ℚ_[p]` is proper.

## Main results

- `PadicInt.totallyBounded_univ` : The set of p-adic integers `ℤ_[p]` is totally bounded.
- `PadicInt.compactSpace` : The set of p-adic integers `ℤ_[p]` is a compact topological space.
- `Padic.instProperSpace` : The field of p-adic numbers `ℚ_[p]` is a proper metric space.

## Notation

- `p` : Is a natural prime.

## References

Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing
-/

public section

assert_not_exists FiniteDimensional

open Metric Topology

variable (p : ℕ) [Fact (Nat.Prime p)]

namespace PadicInt

set_option backward.isDefEq.respectTransparency false in
/-- The set of p-adic integers `ℤ_[p]` is totally bounded. -/
/-
**PadicInt.totallyBounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：totallyBounded_univ : TotallyBounded (Set.univ : Set Int_[p])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.totallyBounded_iff`：totallyBounded_iff {s : Set α} : TotallyBound
ed s ↔ forall ε > 0, exists t : Set α, t.Finite ∧ s subseteq ⋃ y in t, ball y ε
· 使用定理 `PadicInt.exists_pow_neg_lt`：exists_pow_neg_lt {ε : Real} (hε : 0 < ε) : 
exists k : Nat, (p : Real) ^ (-(k : Int)) < ε
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `PadicInt.appr_lt`：appr_lt (x : Int_[p]) (n : Nat) : x.appr n < p ^ n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `PadicInt.norm_le_pow_iff_mem_span_pow`：norm_le_pow_iff_mem_span_pow (x :
 Int_[p]) (n : Nat) : ‖x‖ <= (p : Real) ^ (-n : Int) ↔ x in (Ideal.span {(p : In
t_[p]) ^ n} : Ideal Int_[p]…
· 使用定理 `PadicInt.appr_spec`：appr_spec (n : Nat) : forall x : Int_[p], x - appr x
 n in Ideal.span {(p : Int_[p]) ^ n}

--- 原说明 ---
The set of p-adic integers `ℤ_[p]` is totally bounded.
-/
theorem totallyBounded_univ : TotallyBounded (Set.univ : Set ℤ_[p]) := by
  refine Metric.totallyBounded_iff.mpr (fun ε hε ↦ ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ ↦ ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

/-- The set of p-adic integers `ℤ_[p]` is a compact topological space. -/
/-
**PadicInt.compactSpace** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：compactSpace : CompactSpace Int_[p]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
· 使用定理 `PadicInt.totallyBounded_univ`：totallyBounded_univ : TotallyBounded (Set.
univ : Set Int_[p])
· 使用定理 `isComplete_univ`：isComplete_univ {α : Type u} [UniformSpace α] [Complete
Space α] : IsComplete (univ : Set α)

--- 原说明 ---
The set of p-adic integers `ℤ_[p]` is a compact topological space.
-/
instance compactSpace : CompactSpace ℤ_[p] := by
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ p, isComplete_univ⟩

end PadicInt

namespace Padic

/-- The field of p-adic numbers `ℚ_[p]` is a proper metric space. -/
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The field of p-adic numbers `ℚ_[p]` is a proper metric space.
-/
instance : ProperSpace ℚ_[p] := by
  suffices LocallyCompactSpace ℚ_[p] from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  have : closedBall 0 1 ∈ 𝓝 (0 : ℚ_[p]) := closedBall_mem_nhds _ zero_lt_one
  simp only [closedBall, dist_eq_norm_sub, sub_zero] at this
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_ this
  simpa only [isCompact_iff_compactSpace] using! PadicInt.compactSpace p

end Padic

