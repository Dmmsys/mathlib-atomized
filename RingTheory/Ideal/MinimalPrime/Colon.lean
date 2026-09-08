/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# Minimal primes over a colon ideal

We prove that a minimal prime over an ideal of the form `N.colon {x}` in a Noetherian ring is
itself an ideal of the form `N.colon {x'}`.

-/

public section

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Submodule R M}
  {I : Ideal R} {x : M}

/-- A minimal prime over an ideal of the form `N.colon {x}` in a Noetherian ring is
itself an ideal of the form `N.colon {x'}`. -/
/-
**Submodule.exists_eq_colon_of_mem_minimalPrimes** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：exists_eq_colon_of_mem_minimalPrimes [IsNoetherianRing R] (hI : I in (N.co
lon {x}).minimalPrimes) : exists x' : M, I = N.colon {x'}
参数：hI : I in (N.colon {x}).minimalPrimes。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.minimalPrimes_top`：Ideal.minimalPrimes_top : (⊤ : Ideal R).minimal
Primes = ∅
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.exists_radical_pow_le_of_fg`：exists_radical_pow_le_of_fg {R : Type
*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) : exists n : Nat, I.radical
 ^ n <= I
· 使用引理 `Ideal.fg_of_isNoetherianRing`：Ideal.fg_of_isNoetherianRing {R : Type*} [
Semiring R] [IsNoetherianRing R] (I : Ideal R) : I.FG
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用引理 `Ideal.finite_minimalPrimes_of_isNoetherianRing`：Ideal.finite_minimalPrim
es_of_isNoetherianRing (I : Ideal R) : I.minimalPrimes.Finite
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.instIsOrderedRing`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A],   IsOrderedRing (Submodul
e R A)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `Ideal.mul_le_inf`：mul_le_inf [I.IsTwoSided] : I * J <= I ⊓ J
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
A minimal prime over an ideal of the form `N.colon {x}` in a Noetherian ring is
itself an ideal of the form `N.colon {x'}`.
-/
theorem exists_eq_colon_of_mem_minimalPrimes [IsNoetherianRing R]
    (hI : I ∈ (N.colon {x}).minimalPrimes) : ∃ x' : M, I = N.colon {x'} := by
  by_cases hx : x ∈ N
  · simp [show (colon N {x}) = ⊤ by simpa, Ideal.minimalPrimes_top] at hI
  classical
  -- `I` is a minimal prime over `ann = colon N {x}`
  set ann := colon N {x}
  -- there exists an integer `n ≠ 0` and an ideal `J` satisfying `I ^ n * J ≤ ann` and `¬ J ≠ I`
  have key : ∃ n ≠ 0, ∃ J : Ideal R, I ^ n * J ≤ ann ∧ ¬ J ≤ I := by
    -- let `n` be large enough so that `ann.radical ^ n ≤ ann` (uses Noetherian)
    obtain ⟨n, hn⟩ := ann.exists_radical_pow_le_of_fg ann.radical.fg_of_isNoetherianRing
    have hn0 : n ≠ 0 := by contrapose hn; simpa [hn, ann]
    -- then take `J` to be the product of the other minimal primes raised to the `n`th power
    have h := ann.finite_minimalPrimes_of_isNoetherianRing R
    rw [← ann.sInf_minimalPrimes, ← h.coe_toFinset, ← h.toFinset.inf_id_eq_sInf,
      ← Finset.insert_erase (h.mem_toFinset.mpr hI), Finset.inf_insert, id_eq] at hn
    grw [← Ideal.mul_le_inf, mul_pow] at hn
    refine ⟨n, hn0, ((h.toFinset.erase I).inf id) ^ n, hn, ?_⟩
    have (K : Ideal R) (hKI : K ≤ I) (hK : K ∈ ann.minimalPrimes) : K = I :=
      le_antisymm hKI (hI.2 hK.1 hKI)
    simpa [hI.isPrime.pow_le_iff hn0, hI.isPrime.inf_le', imp_not_comm, not_imp_not]
  obtain ⟨hn0, J, hJ, hJI⟩ := Nat.find_spec key
  -- let `n` be minimal such that there exists an ideal `J` with `I ^ n * J ≤ ann` and `¬ J ≠ I`
  set n := Nat.find key
  -- the minimality of `n` will allow us to pick `x'` from the ideal `K = I ^ (n - 1) * J`
  let K := I ^ (n - 1) * J
  -- we want `I = colon N {x'}`, and we have `I ≤ colon N {y • x}` for every `y ∈ K` (uses `n ≠ 0`)
  have step1 : ∀ y ∈ K, I ≤ colon N {y • x} := by
    intro y hy p hp
    rw [mem_colon_singleton, smul_smul, ← mem_colon_singleton]
    apply hJ
    simpa [K, ← mul_assoc, mul_pow_sub_one hn0] using mul_mem_mul hp hy
  clear hn0
  -- so it suffices to find a single `y ∈ K` with `colon N {y • x} ≤ I`
  suffices step2 : ∃ y : K, colon N {y • x} ≤ I by
    obtain ⟨y, hyI⟩ := step2
    exact ⟨y • x, le_antisymm (step1 y y.2) hyI⟩
  -- if not, then for every `y ∈ K`, there exists an `f y ∈ colon N {y • x}` with `f y ∉ I`
  by_contra! h'
  simp only [SetLike.not_le_iff_exists] at h'
  choose f g h using h'
  -- let `s` be a finite generating set for `K`
  obtain ⟨s, hs⟩ : (⊤ : Submodule R K).FG := Module.Finite.fg_top
  -- let `z` be the product of these finitely many `f y`'s
  let z := ∏ y ∈ s, f y
  -- then `z ∉ I`
  have hz : z ∉ I := by simp [z, hI.isPrime.prod_mem_iff, h]
  -- and `K ≤ colon N {z • x}`
  have hz' : K ≤ colon N {z • x} := by
    rw [← (map_injective_of_injective K.subtype_injective).eq_iff, map_subtype_top] at hs
    rw [← hs, map_span, span_le, Set.image_subset_iff]
    intro i hi
    rw [Set.mem_preimage, SetLike.mem_coe, mem_colon_singleton, smul_comm, ← mem_colon_singleton]
    obtain ⟨y, hy : z = f i * y⟩ := Finset.dvd_prod_of_mem f hi
    exact hy ▸ Ideal.mul_mem_right y _ (g i)
  -- or equivalently `K * Ideal.span {z} ≤ ann`
  replace hz' : K * Ideal.span {z} ≤ ann := by
    rw [mul_comm, Ideal.span_singleton_mul_le_iff]
    intro i hi
    simpa only [ann, mem_colon_singleton, mul_comm, mul_smul] using hz' hi
  -- but now `K = I ^ (n - 1) * J` contradicts the minimality of `n`
  have hK : I ^ (n - 1) * (J * Ideal.span {z}) ≤ ann ∧ ¬ J * Ideal.span {z} ≤ I := by
    rw [← mul_assoc, hI.isPrime.mul_le, not_or, Ideal.span_singleton_le_iff_mem]
    exact ⟨hz', hJI, hz⟩
  by_cases hn' : n - 1 = 0
  · simp [K, show n = 1 by grind] at hz'
    exact (hK.2 (hz'.trans hI.le)).elim
  · grind [Nat.find_min' key ⟨hn', J * Ideal.span {z}, hK⟩]

end Submodule

