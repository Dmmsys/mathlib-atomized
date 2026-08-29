/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  radical of the annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a Noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a Noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## Implementation details

The presence of the radical in the definition of `IsAssociatedPrime` is slightly nonstandard but
gives the correct characterization of the prime ideals of any minimal primary decomposition in the
non-Noetherian setting (see Theorem 4.5 in Atiyah-Macdonald). If the ring `R` is assumed to be
Noetherian, then the radical can be dropped from the definition (see `isAssociatedPrime_iff`).

See also [Stacks: Lemma 0566](https://stacks.math.columbia.edu/tag/0566) which states that a
prime `p` is minimal among primes containing an annihilator an element of `M` if and only if
`p R_p` is an associated prime of `M_p` (including the radical).

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
-/

@[expose] public section

open LinearMap Submodule

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M)
  (I : Ideal R) (x : M)

/--
Definition of `IsAssociatedPrime` / `IsAssociatedPrime` 的定义

English:
structure IsAssociatedPrime
  parameters: : Prop extends I.IsPrime where
  extends: I.IsPrime
  axioms and operations (1):
    - eq_radical_colon : exists x, I = (colon N {x}).radical

中文:
结构 是AssociatedPrime
  参数: : 命题 extends I.是素 where
  继承: I.是素
  公理与运算 (1 个):
    - eq_radical_colon : 存在 x, I = (colon N {x}).radical
-/
protected structure IsAssociatedPrime : Prop extends I.IsPrime where
  eq_radical_colon : exists x, I = (colon N {x}).radical

/--
Definition of `associatedPrimes` / `associatedPrimes` 的定义

English:
definition associatedPrimes
  signature: : Set (Ideal R)
  body: { I | N.IsAssociatedPrime I }

中文:
定义 associatedPrimes
  签名: : 集合 (理想 R)
  定义体: { I | N.IsAssociatedPrime I }
-/
protected def associatedPrimes : Set (Ideal R) :=
  { I | N.IsAssociatedPrime I }

variable {N I}

/--
theorem `isAssociatedPrime_def` / 定理 `isAssociatedPrime_def`

English:
theorem isAssociatedPrime_def
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isAssociatedPrime_def
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
protected theorem isAssociatedPrime_def :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ exists x, I = (colon N {x}).radical :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/--
theorem `isAssociatedPrime_iff` / 定理 `isAssociatedPrime_iff`

English:
theorem isAssociatedPrime_iff
  given: [IsNoetherianRing R]
  proof: by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes (x := x) ?_⟩
    rw [← Ideal.radical_minimalPrimes]; rw [Ideal.minimalPrimes_eq_subsingleton_self]; rw [Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩

中文:
定理 isAssociatedPrime_iff
  条件: [是Noether环 R]
  证明: by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes (x := x) ?_⟩
    rw [← Ideal.radical_minimalPrimes]; rw [Ideal.minimalPrimes_eq_subsingleton_self]; rw [Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩
-/
protected theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ exists x, I = colon N {x} := by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes (x := x) ?_⟩
    rw [← Ideal.radical_minimalPrimes]; rw [Ideal.minimalPrimes_eq_subsingleton_self]; rw [Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩

instance (I : N.associatedPrimes) : I.1.IsPrime := I.2.1

/--
theorem `AssociatePrimes.mem_iff` / 定理 `AssociatePrimes.mem_iff`

English:
theorem AssociatePrimes.mem_iff
  statement: I in N.associatedPrimes ↔ N.IsAssociatedPrime I
  proof: .rfl

中文:
定理 AssociatePrimes.mem_iff
  结论: I in N.associatedPrimes ↔ N.是AssociatedPrime I
  证明: .rfl
-/
protected theorem AssociatePrimes.mem_iff : I in N.associatedPrimes ↔ N.IsAssociatedPrime I :=
  .rfl

end Submodule

section Semiring

variable {R : Type*} [CommSemiring R] (I J : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M]

/--
Definition of `IsAssociatedPrime` / `IsAssociatedPrime` 的定义

English:
definition IsAssociatedPrime
  signature: : Prop
  body: (⊥ : Submodule R M).IsAssociatedPrime I

中文:
定义 是AssociatedPrime
  签名: : 命题
  定义体: (⊥ : Submodule R M).IsAssociatedPrime I

Depends on / 依赖: IsAssociatedPrime, Submodule
-/
def IsAssociatedPrime : Prop :=
  (⊥ : Submodule R M).IsAssociatedPrime I

variable (R) in
/--
Definition of `associatedPrimes` / `associatedPrimes` 的定义

English:
definition associatedPrimes
  signature: : Set (Ideal R)
  body: { I | IsAssociatedPrime I M }

中文:
定义 associatedPrimes
  签名: : 集合 (理想 R)
  定义体: { I | IsAssociatedPrime I M }

Depends on / 依赖: IsAssociatedPrime
-/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M} {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M ->ₗ[R] M')

/--
theorem `AssociatedPrimes.mem_iff` / 定理 `AssociatedPrimes.mem_iff`

English:
theorem AssociatedPrimes.mem_iff
  statement: I in associatedPrimes R M ↔ IsAssociatedPrime I M
  proof: Iff.rfl

中文:
定理 AssociatedPrimes.mem_iff
  结论: I in associatedPrimes R M ↔ 是AssociatedPrime I M
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem AssociatedPrimes.mem_iff : I in associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl

/--
theorem `IsAssociatedPrime.isPrime` / 定理 `IsAssociatedPrime.isPrime`

English:
theorem IsAssociatedPrime.isPrime
  given: (h : IsAssociatedPrime I M)
  statement: I.IsPrime
  proof: h.1

中文:
定理 是AssociatedPrime.isPrime
  条件: (h : 是AssociatedPrime I M)
  结论: I.是素
  证明: h.1

Depends on / 依赖: Countable, Countable.to_separableSpace, SeparableSpace, to_separableSpace
-/
theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1

instance (I : associatedPrimes R M) : I.1.IsPrime := I.2.1

/--
theorem `isAssociatedPrime_iff` / 定理 `isAssociatedPrime_iff`

English:
theorem isAssociatedPrime_iff
  given: [IsNoetherianRing R]
  proof: (⊥ : Submodule R M).isAssociatedPrime_iff

中文:
定理 isAssociatedPrime_iff
  条件: [是Noether环 R]
  证明: (⊥ : Submodule R M).isAssociatedPrime_iff

Depends on / 依赖: Submodule, isAssociatedPrime_iff
-/
theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x} :=
  (⊥ : Submodule R M).isAssociatedPrime_iff

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsAssociatedPrime.map_of_injective` / 定理 `IsAssociatedPrime.map_of_injective`

English:
theorem IsAssociatedPrime.map_of_injective
  given: (h : IsAssociatedPrime I M) (hf : Function.Injective f)
  proof: by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot, ← map_smul, map_eq_zero_iff f hf]

中文:
定理 是AssociatedPrime.map_of_injective
  条件: (h : 是AssociatedPrime I M) (hf : 函数.单射 f)
  证明: by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot, ← map_smul, map_eq_zero_iff f hf]

Depends on / 依赖: Ideal.mem_radical_iff, map_eq_zero_iff, map_smul, mem_bot, mem_colon_singleton, mem_radical_iff, simp_rw
-/
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot, ← map_smul, map_eq_zero_iff f hf]

/--
theorem `LinearEquiv.isAssociatedPrime_iff` / 定理 `LinearEquiv.isAssociatedPrime_iff`

English:
theorem LinearEquiv.isAssociatedPrime_iff
  given: (l : M ≃ₗ[R] M')
  proof: ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

中文:
定理 线性等价.isAssociatedPrime_iff
  条件: (l : M ≃ₗ[R] M')
  证明: ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

Depends on / 依赖: h.map_of_injective, injective, l.injective, l.symm, l.symm.injective, map_of_injective
-/
theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

/--
theorem `not_isAssociatedPrime_of_subsingleton` / 定理 `not_isAssociatedPrime_of_subsingleton`

English:
theorem not_isAssociatedPrime_of_subsingleton
  given: [Subsingleton M]
  statement: ¬IsAssociatedPrime I M
  proof: by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simp [hx, Subsingleton.elim x 0]

中文:
定理 not_isAssociatedPrime_of_subsingleton
  条件: [子单例 M]
  结论: ¬是AssociatedPrime I M
  证明: by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simp [hx, Subsingleton.elim x 0]

Depends on / 依赖: Subsingleton, Subsingleton.elim, hI.ne_top, ne_top
-/
theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simp [hx, Subsingleton.elim x 0]

variable (R) in
/--
theorem `exists_le_isAssociatedPrime_of_isNoetherianRing` / 定理 `exists_le_isAssociatedPrime_of_isNoetherianRing`

English:
theorem exists_le_isAssociatedPrime_of_isNoetherianRing
  statement: [H : IsNoetherianRing R] (x : M)
  proof: by
  simp only [isAssociatedPrime_iff]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (⊥ : Submodule R M).colon {x} <= P ∧ P != ⊤ ∧ exists y : M, P = (⊥ : Submodule R M).colon {y} }
      ⟨_, rfl.le, by simpa, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  i

中文:
定理 存在_le_isAssociatedPrime_of_isNoetherianRing
  结论: [H : 是Noether环 R] (x : M)
  证明: by
  simp only [isAssociatedPrime_iff]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (⊥ : Submodule R M).colon {x} <= P ∧ P != ⊤ ∧ exists y : M, P = (⊥ : Submodule R M).colon {y} }
      ⟨_, rfl.le, by simpa, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  i

Depends on / 依赖: Submodule, isAssociatedPrime_iff, mem_bot, mem_colon_singleton, or_iff_not_imp_left, rfl.le, set_has_maximal_iff_noetherian, set_has_maximal_iff_noetherian.mpr
-/
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x != 0) : exists P : Ideal R, IsAssociatedPrime P M ∧ (⊥ : Submodule R M).colon {x} <= P := by
  simp only [isAssociatedPrime_iff]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (⊥ : Submodule R M).colon {x} <= P ∧ P != ⊤ ∧ exists y : M, P = (⊥ : Submodule R M).colon {y} }
      ⟨_, rfl.le, by simpa, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  intro a b hab
  rw [or_iff_not_imp_left]
  intro ha
  rw [mem_colon_singleton] at ha hab
  have H₁ : (⊥ : Submodule R M).colon {y} <= (⊥ : Submodule R M).colon {a • y} := by
    intro c hc
    rw [mem_colon_singleton]; rw [mem_bot] at hc ⊢
    rw [smul_comm]; rw [hc]; rw [smul_zero]
  rwa [H₁.eq_of_not_lt (h₃ _ ⟨l.trans H₁, by simpa, _, rfl⟩),
    mem_colon_singleton, smul_comm, smul_smul]

namespace associatedPrimes

variable {f} {M'' : Type*} [AddCommMonoid M''] [Module R M''] {g : M' ->ₗ[R] M''}

/-- If `M → M'` is injective, then the set of associated primes of `M` is
contained in that of `M'`. -/
@[stacks 02M3 "first part"]
/--
theorem `subset_of_injective` / 定理 `subset_of_injective`

English:
theorem subset_of_injective
  given: (hf : Function.Injective f)
  proof: fun _I h => h.map_of_injective f hf

中文:
定理 subset_of_injective
  条件: (hf : 函数.单射 f)
  证明: fun _I h => h.map_of_injective f hf

Depends on / 依赖: h.map_of_injective, map_of_injective
-/
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M subseteq associatedPrimes R M' := fun _I h => h.map_of_injective f hf

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
/--
theorem `subset_union_of_exact` / 定理 `subset_union_of_exact`

English:
theorem subset_union_of_exact
  given: (hf : Function.Injective f) (hfg : Function.Exact f g)
  proof: by
  rintro p ⟨_, x, hx⟩
  by_cases! h : exists a in p.primeCompl, exists y : M, exists k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb => ?_) (fun b ⟨n, hb⟩ => ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_

中文:
定理 subset_union_of_exact
  条件: (hf : 函数.单射 f) (hfg : 函数.正合 f g)
  证明: by
  rintro p ⟨_, x, hx⟩
  by_cases! h : exists a in p.primeCompl, exists y : M, exists k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb => ?_) (fun b ⟨n, hb⟩ => ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_

Depends on / 依赖: Finset, apply_fun, classical, countable_range, dense_iff_inter_open, exists_countable_dense, inhabit, isOpen_pi_iff, le_antisymm, map_smul, map_zero, mem_bot, mem_colon_singleton, nontriviality, p.primeCompl, primeCompl, smul_comm, smul_zero, to_subtype
-/
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' subseteq associatedPrimes R M union associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  by_cases! h : exists a in p.primeCompl, exists y : M, exists k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb => ?_) (fun b ⟨n, hb⟩ => ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_singleton]; rw [mem_bot] at hb ⊢
      apply_fun _ using hf
      rw [map_smul]; rw [h]; rw [smul_comm]; rw [hb]; rw [smul_zero]; rw [map_zero]
    · rw [mem_colon_singleton, mem_bot] at hb
      apply_fun f at hb
      rw [map_smul]; rw [map_zero]; rw [h]; rw [← mul_smul]; rw [← mem_bot R]; rw [← mem_colon_singleton] at hb
      replace hb := hx.ge (Ideal.le_radical hb)
      contrapose hb
      exact p.primeCompl.mul_mem (p.primeCompl.pow_mem hb n) (p.primeCompl.pow_mem ha k)
  · right
    refine ⟨‹_›, g x, le_antisymm (fun b hb => ?_) (fun b ⟨n, hb⟩ => ?_)⟩
    · rw [hx] at hb
      refine Ideal.radical_mono (fun b hb => ?_) hb
      rw [mem_colon_singleton]; rw [mem_bot] at hb ⊢
      rw [← map_smul]; rw [hb]; rw [map_zero]
    · rw [mem_colon_singleton, mem_bot, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra H
      exact h b H y n hy

variable (R M M') in
/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  statement: associatedPrimes R (M × M') = associatedPrimes R M union associatedPrimes R M'
  proof: (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

中文:
定理 乘积
  结论: associatedPrimes R (M × M') = associatedPrimes R M union associatedPrimes R M'
  证明: (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

Depends on / 依赖: LinearMap, LinearMap.inl_injective, LinearMap.inr_injective, Set.union_subset_iff, antisymm, inl_injective, inl_snd, inr_injective, subset_of_injective, subset_union_of_exact, union_subset_iff
-/
theorem prod : associatedPrimes R (M × M') = associatedPrimes R M union associatedPrimes R M' :=
  (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

end associatedPrimes

/--
theorem `LinearEquiv.AssociatedPrimes.eq` / 定理 `LinearEquiv.AssociatedPrimes.eq`

English:
theorem LinearEquiv.AssociatedPrimes.eq
  given: (l : M ≃ₗ[R] M')
  proof: le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)

中文:
定理 线性等价.AssociatedPrimes.eq
  条件: (l : M ≃ₗ[R] M')
  证明: le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)

Depends on / 依赖: associatedPrimes, associatedPrimes.subset_of_injective, injective, l.injective, l.symm.injective, le_antisymm, subset_of_injective
-/
theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)

/--
theorem `associatedPrimes.eq_empty_of_subsingleton` / 定理 `associatedPrimes.eq_empty_of_subsingleton`

English:
theorem associatedPrimes.eq_empty_of_subsingleton
  given: [Subsingleton M]
  statement: associatedPrimes R M = ∅
  proof: by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

中文:
定理 associatedPrimes.eq_empty_of_subsingleton
  条件: [子单例 M]
  结论: associatedPrimes R M = ∅
  证明: by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

Depends on / 依赖: Set.mem_empty_iff_false, iff_false, mem_empty_iff_false, not_isAssociatedPrime_of_subsingleton
-/
theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

variable (R M)

/--
theorem `associatedPrimes.nonempty` / 定理 `associatedPrimes.nonempty`

English:
theorem associatedPrimes.nonempty
  given: [IsNoetherianRing R] [Nontrivial M]
  proof: by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

中文:
定理 associatedPrimes.nonempty
  条件: [是Noether环 R] [非平凡 M]
  证明: by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

Depends on / 依赖: exists_le_isAssociatedPrime_of_isNoetherianRing, exists_ne
-/
theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

/--
theorem `biUnion_associatedPrimes_eq_zero_divisors` / 定理 `biUnion_associatedPrimes_eq_zero_divisors`

English:
theorem biUnion_associatedPrimes_eq_zero_divisors
  given: [IsNoetherianRing R]
  proof: by
  simp only [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    exact ⟨x, by simpa using h.ne_top, by simpa using h'⟩
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing

中文:
定理 biUnion_associatedPrimes_eq_zero_divisors
  条件: [是Noether环 R]
  证明: by
  simp only [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    exact ⟨x, by simpa using h.ne_top, by simpa using h'⟩
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing

Depends on / 依赖: AssociatedPrimes, AssociatedPrimes.mem_iff, Set.iUnion, Set.mem_iUnion, exists_le_isAssociatedPrime_of_isNoetherianRing, h.ne_top, isAssociatedPrime_iff, mem_colon_singleton, mem_iff, ne_top, subset_antisymm
-/
theorem biUnion_associatedPrimes_eq_zero_divisors [IsNoetherianRing R] :
    ⋃ p in associatedPrimes R M, p = { r : R | exists x : M, x != 0 ∧ r • x = 0 } := by
  simp only [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    exact ⟨x, by simpa using h.ne_top, by simpa using h'⟩
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h
    rw [isAssociatedPrime_iff] at hP
    exact Set.mem_iUnion₂_of_mem hP (hx (by rwa [mem_colon_singleton]))

/--
theorem `biUnion_associatedPrimes_eq_compl_nonZeroDivisors` / 定理 `biUnion_associatedPrimes_eq_compl_nonZeroDivisors`

English:
theorem biUnion_associatedPrimes_eq_compl_nonZeroDivisors
  given: [IsNoetherianRing R]
  proof: (biUnion_associatedPrimes_eq_zero_divisors R R).trans by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

中文:
定理 biUnion_associatedPrimes_eq_compl_nonZeroDivisors
  条件: [是Noether环 R]
  证明: (biUnion_associatedPrimes_eq_zero_divisors R R).trans by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

Depends on / 依赖: and_comm, biUnion_associatedPrimes_eq_zero_divisors, nonZeroDivisorsLeft_eq_nonZeroDivisors
-/
theorem biUnion_associatedPrimes_eq_compl_nonZeroDivisors [IsNoetherianRing R] :
    ⋃ p in associatedPrimes R R, p = (nonZeroDivisors R : Set R)ᶜ :=
(biUnion_associatedPrimes_eq_zero_divisors R R).trans by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

variable {R M}

/--
theorem `IsAssociatedPrime.annihilator_le` / 定理 `IsAssociatedPrime.annihilator_le`

English:
theorem IsAssociatedPrime.annihilator_le
  given: (h : IsAssociatedPrime I M)
  proof: by
  obtain ⟨hI, x, rfl⟩ := h
  rw [bot_colon']
  exact (annihilator_mono le_top).trans Ideal.le_radical

中文:
定理 是AssociatedPrime.annihilator_le
  条件: (h : 是AssociatedPrime I M)
  证明: by
  obtain ⟨hI, x, rfl⟩ := h
  rw [bot_colon']
  exact (annihilator_mono le_top).trans Ideal.le_radical

Depends on / 依赖: Ideal.le_radical, annihilator_mono, bot_colon, le_radical, le_top
-/
theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator <= I := by
  obtain ⟨hI, x, rfl⟩ := h
  rw [bot_colon']
  exact (annihilator_mono le_top).trans Ideal.le_radical

end Semiring

variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/--
theorem `isAssociatedPrime_iff_exists_injective_linearMap` / 定理 `isAssociatedPrime_iff_exists_injective_linearMap`

English:
theorem isAssociatedPrime_iff_exists_injective_linearMap
  given: [IsNoetherianRing R]
  proof: by
  rw [isAssociatedPrime_iff]; rw [and_congr_right_iff]
  refine fun _ => ⟨fun ⟨x, h⟩ => ?_, fun ⟨f, h⟩ => ⟨(f ∘ₗ mkQ I) 1, ?_⟩⟩
  · replace h : I = ker (toSpanSingleton R M x) := by simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ h.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ h)⟩
  · conv_lhs => rw [←

中文:
定理 isAssociatedPrime_iff_存在_injective_linearMap
  条件: [是Noether环 R]
  证明: by
  rw [isAssociatedPrime_iff]; rw [and_congr_right_iff]
  refine fun _ => ⟨fun ⟨x, h⟩ => ?_, fun ⟨f, h⟩ => ⟨(f ∘ₗ mkQ I) 1, ?_⟩⟩
  · replace h : I = ker (toSpanSingleton R M x) := by simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ h.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ h)⟩
  · conv_lhs => rw [←

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, I.ker_mkQ, Ideal.Quotient.algebraMap_eq, Quotient, SetLike, SetLike.ext_iff, algebraMap_eq, algebraMap_eq_smul_one, and_congr_right_iff, conv_lhs, ext_iff, h.le, isAssociatedPrime_iff, ker_comp_of_ker_eq_bot, ker_eq_bot, ker_eq_bot.mp, ker_eq_bot_of_injective, ker_liftQ_eq_bot, ker_mkQ
-/
theorem isAssociatedPrime_iff_exists_injective_linearMap [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ exists (f : R ⧸ I ->ₗ[R] M), Function.Injective f := by
  rw [isAssociatedPrime_iff]; rw [and_congr_right_iff]
  refine fun _ => ⟨fun ⟨x, h⟩ => ?_, fun ⟨f, h⟩ => ⟨(f ∘ₗ mkQ I) 1, ?_⟩⟩
  · replace h : I = ker (toSpanSingleton R M x) := by simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ h.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ h)⟩
  · conv_lhs => rw [← I.ker_mkQ, ← ker_comp_of_ker_eq_bot (mkQ I) (ker_eq_bot_of_injective h)]
    simp [SetLike.ext_iff, ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

variable {I J M}

/--
theorem `IsAssociatedPrime.eq_radical` / 定理 `IsAssociatedPrime.eq_radical`

English:
theorem IsAssociatedPrime.eq_radical
  given: (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I))
  proof: by
  obtain ⟨hJ, x, e⟩ := h
  have : x != 0 := by
    rintro rfl
    apply hJ.1
    rwa [colon_singleton_zero, Ideal.radical_top] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  have h {y} : y in colon ⊥ {(Ideal.Quotient.mk I) x} ↔ Ideal.Quotient.mk I (y * x) = 0 := by
    rw [mem_co

中文:
定理 是AssociatedPrime.eq_radical
  条件: (hI : I.是准素) (h : 是AssociatedPrime J (R ⧸ I))
  证明: by
  obtain ⟨hJ, x, e⟩ := h
  have : x != 0 := by
    rintro rfl
    apply hJ.1
    rwa [colon_singleton_zero, Ideal.radical_top] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  have h {y} : y in colon ⊥ {(Ideal.Quotient.mk I) x} ↔ Ideal.Quotient.mk I (y * x) = 0 := by
    rw [mem_co

Depends on / 依赖: Algebra, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk, Ideal.radi, Ideal.radical_top, Quotient, algebraMap_eq, colon_singleton_zero, eq_zero_iff_mem, le_antisymm, map_mul, mem_bot, mem_colon_singleton, ne_eq, radical_top, smul_def
-/
theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x != 0 := by
    rintro rfl
    apply hJ.1
    rwa [colon_singleton_zero, Ideal.radical_top] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  have h {y} : y in colon ⊥ {(Ideal.Quotient.mk I) x} ↔ Ideal.Quotient.mk I (y * x) = 0 := by
    rw [mem_colon_singleton]; rw [Algebra.smul_def]; rw [Ideal.Quotient.algebraMap_eq]; rw [← map_mul]; rw [mem_bot]
  simp only [e, Ideal.Quotient.mkₐ_eq_mk, ne_eq, Ideal.Quotient.eq_zero_iff_mem] at this h ⊢
  refine le_antisymm (Ideal.radical_le_radical_iff.mpr fun y hy => ?_)
    (Ideal.radical_mono fun y => h.mpr ∘ I.mul_mem_right x)
  rw [← I.colon_univ]; rw [← Set.top_eq_univ]
  exact (hI.mem_or_mem (h.mp hy)).resolve_left this

/--
theorem `associatedPrimes.eq_singleton_of_isPrimary` / 定理 `associatedPrimes.eq_singleton_of_isPrimary`

English:
theorem associatedPrimes.eq_singleton_of_isPrimary
  given: [IsNoetherianRing R] (hI : I.IsPrimary)
  proof: by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  have : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne]; rw [Ideal.Quotient.eq]; rw [sub_zero]; rw [← Ideal.eq_top_iff_one]
    exact hI.1
 

中文:
定理 associatedPrimes.eq_singleton_of_isPrimary
  条件: [是Noether环 R] (hI : I.是准素)
  证明: by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  have : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne]; rw [Ideal.Quotient.eq]; rw [sub_zero]; rw [← Ideal.eq_top_iff_one]
    exact hI.1
 

Depends on / 依赖: Ideal.Quotient.eq, Ideal.Quotient.mk, Ideal.eq_top_iff_one, IsAssociatedPrime, IsAssociatedPrime.eq_radical, Nontrivial, Quotient, Set.mem_singleton_iff, associatedPrimes, associatedPrimes.nonempty, eq_radical, eq_top_iff_one, ha.eq_radical, mem_singleton_iff, nonempty, sub_zero
-/
theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  have : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne]; rw [Ideal.Quotient.eq]; rw [sub_zero]; rw [← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
