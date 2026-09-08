/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.Algebra.Group.Ideal
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Order.WellFoundedSet

/-!
# Semigroup ideals in a canonically ordered and well-quasi-ordered monoid

This file proves that in a canonically ordered and well-quasi-ordered monoid, any semigroup ideal is
finitely generated, and the semigroup ideals satisfy the ascending chain condition.

## References

* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

public section

namespace SemigroupIdeal

variable {M : Type*} [CommMonoid M] [PartialOrder M] [WellQuasiOrderedLE M]
  [CanonicallyOrderedMul M]

/-- In a canonically ordered and well-quasi-ordered monoid, any semigroup ideal is finitely
generated. -/
@[to_additive /-- In a canonically ordered and well-quasi-ordered additive monoid, any semigroup
ideal is finitely generated. -/]
/-
**SemigroupIdeal.fg_of_wellQuasiOrderedLE** 是 Mathlib 中的一个定理，位于命名空间 `SemigroupId
eal`。
形式化陈述：fg_of_wellQuasiOrderedLE (I : SemigroupIdeal M) : I.FG
参数：I : SemigroupIdeal M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.isPWO_of_wellQuasiOrderedLE`：isPWO_of_wellQuasiOrderedLE [h : WellQu
asiOrderedLE α] (s : Set α) : s.IsPWO
· 使用定理 `IsAntichain.finite_of_partiallyWellOrderedOn`：∀ {α : Type u_2} {r : α → 
α → Prop} {s : Set α}, IsAntichain r s → s.PartiallyWellOrderedOn r → s.Finite
· 使用定理 `setOfPred_minimal_antichain`：setOfPred_minimal_antichain (P : α -> Prop)
 : IsAntichain (· <= ·) {x | Minimal P x}
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `setOfPred_minimal_subset`：setOfPred_minimal_subset (s : Set α) : {x | Mi
nimal (· in s) x} subseteq s
· 使用定理 `SubMulAction.ext`：ext {p q : SubMulAction R M} (h : forall x, x in p ↔ x
 in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.IsPWO.exists_le_minimal`：∀ {α : Type u_2} [inst : Preorder α] {s : S
et α} {a : α}, s.IsPWO → a ∈ s → ∃ b ≤ a, Minimal (fun x => x ∈ s) b
· 使用定理 `le_iff_exists_mul'`：le_iff_exists_mul' : a <= b ↔ exists c, b = c * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem fg_of_wellQuasiOrderedLE (I : SemigroupIdeal M) : I.FG := by
  have hpwo := Set.isPWO_of_wellQuasiOrderedLE { x | x ∈ I }
  refine ⟨_, (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOfPred_minimal_subset _)), ?_⟩
  ext x
  simp only [mem_closure'', SetLike.setOfPred_mem_eq, SetLike.mem_coe, Set.mem_ofPred_eq]
  constructor
  · intro hx
    rcases hpwo.exists_le_minimal hx with ⟨z, hz, hz'⟩
    rw [le_iff_exists_mul'] at hz
    rcases hz with ⟨y, rfl⟩
    exact ⟨y, z, hz', rfl⟩
  · rintro ⟨y, z, hz, rfl⟩
    apply SubMulAction.smul_mem
    exact hz.1

/-- In a canonically ordered and well-quasi-ordered monoid, the semigroup ideals satisfy the
ascending chain condition. -/
@[to_additive /-- A canonically ordered and well-quasi-ordered additive monoid, the semigroup ideals
satisfy the ascending chain condition. -/]
/-
**SemigroupIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `SemigroupIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedGT (SemigroupIdeal M) := by
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro f
  rcases fg_iff.1 (fg_of_wellQuasiOrderedLE (⨆ i, f i)) with ⟨s, hI⟩
  have hs : ∀ x ∈ s, ∃ i, x ∈ f i := by
    intro x hx
    apply subset_closure (s := (s : Set M)) at hx
    simpa [← hI] using hx
  choose! g hg using hs
  exists s.sup g
  intro n hn
  apply (f.mono hn).antisymm
  apply (le_iSup f n).trans
  intro x hx
  rw [hI, mem_closure''] at hx
  rcases hx with ⟨y, z, hz, rfl⟩
  exact SemigroupIdeal.mul_mem _ _ (f.mono (Finset.le_sup hz) (hg _ hz))

end SemigroupIdeal

