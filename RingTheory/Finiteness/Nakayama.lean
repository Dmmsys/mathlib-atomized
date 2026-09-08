/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Nakayama's lemma

## Main results

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

-/

public section

namespace Submodule

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2. -/
@[stacks 00DV]
/-
**Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul** 是 Mathlib 中的一
个定理，位于命名空间 `Submodule`。
形式化陈述：exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing
 R] {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) 
(hn : N.FG) (hin : N <= I • N) : exists r : R, r - 1 in I ∧ forall n in N, r • n
 = (0 : M)
参数：I : Ideal R；N : Submodule R M；hn : N.FG；hin : N <= I • N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.smul_bot`：smul_bot : I • (⊥ : Submodule R M) = ⊥
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.smul_sup`：smul_sup : I • (N ⊔ P) = I • N ⊔ I • P
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Submodule.mem_smul_span_singleton`：mem_smul_span_singleton [I.IsTwoSided
] {m : M} {x : M} : x in I • span R ({m} : Set M) ↔ exists y in I, y • m = x
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c
 : α), a - b - c = a - c - b
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
**Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2.
-/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have H : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N := by
    refine ⟨1, ?_, ?_, ?_⟩
    · rw [sub_self]
      exact I.zero_mem
    · rw [hs]
      intro n hn
      rw [mem_comap]
      change (1 : R) • n ∈ I • N
      rw [one_smul]
      exact hin hn
    · rw [← span_le, hs]
  clear hin hs
  induction s, hfs using Set.Finite.induction_on with
  | empty =>
    rcases H with ⟨r, hr1, hrn, _⟩
    refine ⟨r, hr1, fun n hn => ?_⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  | @insert i s _ _ ih =>
  apply ih
  rcases H with ⟨r, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset_iff] at hs
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s := by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨c, hci, rfl⟩
    use r - c
    constructor
    · rw [sub_right_comm]
      exact I.sub_mem hr1 hci
    · rw [sub_smul, ← hyz, add_sub_cancel_left]
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  refine ⟨c * r, ?_, ?_, hs.2⟩
  · simpa only [mul_sub, mul_one, sub_add_sub_cancel] using I.add_mem (I.mul_mem_left c hr1) hc1
  · intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    dsimp at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, _, rfl⟩
    simp only [mem_comap, LinearMap.lsmul_apply]
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)
/-
**Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul** 是 Mathlib 中的一个定理，位于命名
空间 `Submodule`。
形式化陈述：exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M :
 Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.
FG) (hin : N <= I • N) : exists r in I, forall n in N, r • n = n
参数：I : Ideal R；N : Submodule R M；hn : N.FG；hin : N <= I • N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`：exists_s
ub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*
} [AddCommGroup M] [Module R M] (I : Ideal R) (N : S…
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.FG) (hin : N ≤ I • N) :
    ∃ r ∈ I, ∀ n ∈ N, r • n = n := by
  obtain ⟨r, hr, hr'⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hn hin
  exact ⟨-(r - 1), I.neg_mem hr, fun n hn => by simpa [sub_smul] using hr' n hn⟩

end Submodule

