/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
@[wikidata Q1203540]
/--
Definition of `IsMaximal` / `IsMaximal` 的定义

English:
class IsMaximal
  parameters: (I : Ideal α)
  axioms and operations (1):
    - out : IsCoatom I

中文:
类 是极大
  参数: (I : 理想 α)
  公理与运算 (1 个):
    - out : IsCoatom I
-/
class IsMaximal (I : Ideal α) : Prop where
  /-- The maximal ideal is a coatom in the ordering on ideals; that is, it is not the entire ring,
  and there are no other proper ideals strictly containing it. -/
  out : IsCoatom I

/--
theorem `isMaximal_def` / 定理 `isMaximal_def`

English:
theorem isMaximal_def
  given: {I : Ideal α}
  statement: I.IsMaximal ↔ IsCoatom I
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 isMaximal_def
  条件: {I : 理想 α}
  结论: I.是极大 ↔ IsCoatom I
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `IsMaximal.ne_top` / 定理 `IsMaximal.ne_top`

English:
theorem IsMaximal.ne_top
  given: {I : Ideal α} (h : I.IsMaximal)
  statement: I != ⊤
  proof: (isMaximal_def.1 h).1

中文:
定理 是极大.ne_top
  条件: {I : 理想 α} (h : I.是极大)
  结论: I != ⊤
  证明: (isMaximal_def.1 h).1

Depends on / 依赖: isMaximal_def
-/
theorem IsMaximal.ne_top {I : Ideal α} (h : I.IsMaximal) : I != ⊤ :=
  (isMaximal_def.1 h).1

/--
theorem `IsMaximal.lt_top` / 定理 `IsMaximal.lt_top`

English:
theorem IsMaximal.lt_top
  given: {I : Ideal α} (h : I.IsMaximal)
  statement: I < ⊤
  proof: h.ne_top.lt_top

中文:
定理 是极大.lt_top
  条件: {I : 理想 α} (h : I.是极大)
  结论: I < ⊤
  证明: h.ne_top.lt_top

Depends on / 依赖: h.ne_top.lt_top, lt_top, ne_top
-/
theorem IsMaximal.lt_top {I : Ideal α} (h : I.IsMaximal) : I < ⊤ :=
  h.ne_top.lt_top

/--
theorem `isMaximal_iff` / 定理 `isMaximal_iff`

English:
theorem isMaximal_iff
  given: {I : Ideal α}
  proof: by
  simp_rw [isMaximal_def, SetLike.isCoatom_iff, Ideal.ne_top_iff_one, ← Ideal.eq_top_iff_one]

中文:
定理 isMaximal_iff
  条件: {I : 理想 α}
  证明: by
  simp_rw [isMaximal_def, SetLike.isCoatom_iff, Ideal.ne_top_iff_one, ← Ideal.eq_top_iff_one]

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.ne_top_iff_one, SetLike, SetLike.isCoatom_iff, eq_top_iff_one, isCoatom_iff, isMaximal_def, ne_top_iff_one, simp_rw
-/
theorem isMaximal_iff {I : Ideal α} :
    I.IsMaximal ↔ (1 : α) ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J := by
  simp_rw [isMaximal_def, SetLike.isCoatom_iff, Ideal.ne_top_iff_one, ← Ideal.eq_top_iff_one]

/--
theorem `IsMaximal.eq_of_le` / 定理 `IsMaximal.eq_of_le`

English:
theorem IsMaximal.eq_of_le
  given: {I J : Ideal α} (hI : I.IsMaximal) (hJ : J != ⊤) (IJ : I <= J)
  statement: I = J
  proof: eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩

中文:
定理 是极大.eq_of_le
  条件: {I J : 理想 α} (hI : I.是极大) (hJ : J != ⊤) (IJ : I <= J)
  结论: I = J
  证明: eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩

Depends on / 依赖: eq_iff_le_not_lt
-/
theorem IsMaximal.eq_of_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J != ⊤) (IJ : I <= J) : I = J :=
  eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩

/--
theorem `IsMaximal.eq_iff_le` / 定理 `IsMaximal.eq_iff_le`

English:
theorem IsMaximal.eq_iff_le
  given: {I J : Ideal α} (hI : I.IsMaximal) (hJ : J != ⊤)
  statement: I = J ↔ I <= J
  proof: ⟨by aesop, Ideal.IsMaximal.eq_of_le hI hJ⟩

中文:
定理 是极大.eq_iff_le
  条件: {I J : 理想 α} (hI : I.是极大) (hJ : J != ⊤)
  结论: I = J ↔ I <= J
  证明: ⟨by aesop, Ideal.IsMaximal.eq_of_le hI hJ⟩

Depends on / 依赖: Ideal.IsMaximal.eq_of_le, IsMaximal, eq_of_le
-/
theorem IsMaximal.eq_iff_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J != ⊤) : I = J ↔ I <= J :=
  ⟨by aesop, Ideal.IsMaximal.eq_of_le hI hJ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCoatomic (Ideal α)
  body: CompleteLattice.coatomic_of_top_compact isCompactElement_top

中文:
实例 :
  签名: 是余原子的 (理想 α)
  定义体: CompleteLattice.coatomic_of_top_compact isCompactElement_top

Depends on / 依赖: CompleteLattice, CompleteLattice.coatomic_of_top_compact, coatomic_of_top_compact, isCompactElement_top
-/
instance : IsCoatomic (Ideal α) := CompleteLattice.coatomic_of_top_compact isCompactElement_top

/--
theorem `IsMaximal.coprime_of_ne` / 定理 `IsMaximal.coprime_of_ne`

English:
theorem IsMaximal.coprime_of_ne
  statement: {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
  proof: by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

中文:
定理 是极大.coprime_of_ne
  结论: {M M' : 理想 α} (hM : M.是极大) (hM' : M'.是极大)
  证明: by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

Depends on / 依赖: contrapose, eq_of_le, hM.eq_of_le, le_sup_left, le_sup_left.trans_eq, le_sup_right, ne_top, trans_eq
-/
theorem IsMaximal.coprime_of_ne {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
    (hne : M != M') : M ⊔ M' = ⊤ := by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

/--
theorem `exists_le_maximal` / 定理 `exists_le_maximal`

English:
theorem exists_le_maximal
  given: (I : Ideal α) (hI : I != ⊤)
  statement: exists M : Ideal α, M.IsMaximal ∧ I <= M
  proof: let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

中文:
定理 存在_le_maximal
  条件: (I : 理想 α) (hI : I != ⊤)
  结论: 存在 M : 理想 α, M.是极大 ∧ I <= M
  证明: let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

Depends on / 依赖: eq_top_or_exists_le_coatom, resolve_left
-/
theorem exists_le_maximal (I : Ideal α) (hI : I != ⊤) : exists M : Ideal α, M.IsMaximal ∧ I <= M :=
  let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

variable (α) in
/--
theorem `exists_maximal` / 定理 `exists_maximal`

English:
theorem exists_maximal
  given: [Nontrivial α]
  statement: exists M : Ideal α, M.IsMaximal
  proof: let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩

中文:
定理 存在_maximal
  条件: [非平凡 α]
  结论: 存在 M : 理想 α, M.是极大
  证明: let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩

Depends on / 依赖: bot_ne_top, exists_le_maximal
-/
theorem exists_maximal [Nontrivial α] : exists M : Ideal α, M.IsMaximal :=
  let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩

/--
theorem `ne_top_iff_exists_maximal` / 定理 `ne_top_iff_exists_maximal`

English:
theorem ne_top_iff_exists_maximal
  given: {I : Ideal α}
  statement: I != ⊤ ↔ exists M : Ideal α, M.IsMaximal ∧ I <= M
  proof: by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl _ hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax

中文:
定理 ne_top_iff_存在_maximal
  条件: {I : 理想 α}
  结论: I != ⊤ ↔ 存在 M : 理想 α, M.是极大 ∧ I <= M
  证明: by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl _ hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax

Depends on / 依赖: IsMaximal, IsMaximal.ne_top, contrapose, exists_le_maximal, ne_top, top_le_iff
-/
theorem ne_top_iff_exists_maximal {I : Ideal α} : I != ⊤ ↔ exists M : Ideal α, M.IsMaximal ∧ I <= M := by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl _ hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial (Ideal α)
  body: by
  rcases @exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

中文:
实例 [非平凡
  签名: α] : 非平凡 (理想 α)
  定义体: by
  rcases @exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

Depends on / 依赖: exists_maximal, nontrivial_of_ne
-/
instance [Nontrivial α] : Nontrivial (Ideal α) := by
  rcases @exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

/--
theorem `maximal_of_no_maximal` / 定理 `maximal_of_no_maximal`

English:
theorem maximal_of_no_maximal
  statement: {P : Ideal α}
  proof: by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1

中文:
定理 maximal_of_no_maximal
  结论: {P : 理想 α}
  证明: by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1

Depends on / 依赖: exists_le_maximal, hnonmax, lt_of_lt_of_le
-/
theorem maximal_of_no_maximal {P : Ideal α}
    (hmax : forall m : Ideal α, P < m -> ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤ := by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1

/--
theorem `IsMaximal.exists_inv` / 定理 `IsMaximal.exists_inv`

English:
theorem IsMaximal.exists_inv
  given: {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I)
  proof: by
  obtain ⟨H₁, H₂⟩ := isMaximal_iff.1 hI
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]

中文:
定理 是极大.存在_inv
  条件: {I : 理想 α} (hI : I.是极大) {x} (hx : x ∉ I)
  证明: by
  obtain ⟨H₁, H₂⟩ := isMaximal_iff.1 hI
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]

Depends on / 依赖: Set.Subset.trans, Subset, hy.symm, insert, isMaximal_iff, mem_insert, mem_span_insert, span_eq, subset_insert, subset_span
-/
theorem IsMaximal.exists_inv {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I) :
    exists y, exists i in I, y * x + i = 1 := by
  obtain ⟨H₁, H₂⟩ := isMaximal_iff.1 hI
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]

/--
theorem `sInf_isPrime_of_isChain` / 定理 `sInf_isPrime_of_isChain`

English:
theorem sInf_isPrime_of_isChain
  statement: {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· <= ·) s)
  proof: ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push Not at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
· exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' h x⟩

中文:
定理 sInf_isPrime_of_isChain
  结论: {s : 集合 (理想 α)} (hs : s.非空) (hs' : IsChain (· <= ·) s)
  证明: ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push Not at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
· exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' h x⟩

Depends on / 依赖: Ideal.mem_sInf, e.symm.trans_le, eq_top_iff, eq_top_iff.mpr, mem_or_mem, mem_sInf, ne_top, or_iff_not_imp_left, or_iff_not_imp_left.mpr, resolve_left, sInf_le, trans_le
-/
theorem sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· <= ·) s)
    (H : forall p in s, p.IsPrime) : (sInf s).IsPrime :=
  ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push Not at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
· exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' h x⟩

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/--
theorem `span_singleton_prime` / 定理 `span_singleton_prime`

English:
theorem span_singleton_prime
  given: {p : α} (hp : p != 0)
  statement: IsPrime (span ({p} : Set α)) ↔ Prime p
  proof: by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]

中文:
定理 span_singleton_prime
  条件: {p : α} (hp : p != 0)
  结论: 是素 (span ({p} : 集合 α)) ↔ 素 p
  证明: by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]

Depends on / 依赖: isPrime_iff, mem_span_singleton, span_singleton_eq_top
-/
theorem span_singleton_prime {p : α} (hp : p != 0) : IsPrime (span ({p} : Set α)) ↔ Prime p := by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]

/--
theorem `isPrime_span_singleton_of_prime` / 定理 `isPrime_span_singleton_of_prime`

English:
theorem isPrime_span_singleton_of_prime
  given: {p : α} (hp : Prime p)
  statement: (span {p}).IsPrime
  proof: by
  simp [Ideal.span_singleton_prime hp.ne_zero, hp]

中文:
定理 isPrime_span_singleton_of_prime
  条件: {p : α} (hp : 素 p)
  结论: (span {p}).是素
  证明: by
  simp [Ideal.span_singleton_prime hp.ne_zero, hp]

Depends on / 依赖: Ideal.span_singleton_prime, hp.ne_zero, ne_zero, span_singleton_prime
-/
theorem isPrime_span_singleton_of_prime {p : α} (hp : Prime p) : (span {p}).IsPrime := by
  simp [Ideal.span_singleton_prime hp.ne_zero, hp]

/--
theorem `IsMaximal.isPrime` / 定理 `IsMaximal.isPrime`

English:
theorem IsMaximal.isPrime
  given: {I : Ideal α} (H : I.IsMaximal)
  statement: I.IsPrime
  proof: ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I <= J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x in J := Ideal.subset_span (Set.mem_insert x I)
      obtain ⟨_, oJ⟩ := isMaximal_iff.1 H
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y]; rw [F]; rw [mul_add]; rw [mul_comm]; rw [smul_eq_mul]; rw [mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

中文:
定理 是极大.isPrime
  条件: {I : 理想 α} (H : I.是极大)
  结论: I.是素
  证明: ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I <= J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x in J := Ideal.subset_span (Set.mem_insert x I)
      obtain ⟨_, oJ⟩ := isMaximal_iff.1 H
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y]; rw [F]; rw [mul_add]; rw [mul_comm]; rw [smul_eq_mul]; rw [mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

Depends on / 依赖: Ideal.subset_span, Set.Subset.trans, Set.mem_insert, Submodule, Submodule.mem_span_insert.mp, Submodule.span, Subset, congr_arg, insert, isMaximal_iff, mem_insert, mem_span_insert, mul_add, mul_comm, mul_one, or_iff_not_imp_left, smul_eq_mul, specialize, subset_insert, subset_span
-/
theorem IsMaximal.isPrime {I : Ideal α} (H : I.IsMaximal) : I.IsPrime :=
  ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I <= J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x in J := Ideal.subset_span (Set.mem_insert x I)
      obtain ⟨_, oJ⟩ := isMaximal_iff.1 H
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y]; rw [F]; rw [mul_add]; rw [mul_comm]; rw [smul_eq_mul]; rw [mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

-- see Note [lower instance priority]
instance (priority := 100) IsMaximal.isPrime' (I : Ideal α) : forall [_H : I.IsMaximal], I.IsPrime :=
  @IsMaximal.isPrime _ _ _

/--
theorem `exists_disjoint_powers_of_span_eq_top` / 定理 `exists_disjoint_powers_of_span_eq_top`

English:
theorem exists_disjoint_powers_of_span_eq_top
  statement: (s : Set α) (hs : span s = ⊤) (I : Ideal α)
  proof: by
  have ⟨M, hM, le⟩ := exists_le_maximal I hI
  have := hM.1.1
  rw [Ne]; rw [eq_top_iff]; rw [← hs]; rw [span_le]; rw [Set.not_subset] at this
  have ⟨a, has, haM⟩ := this
  exact ⟨a, has, Set.disjoint_left.mpr fun x hx ⟨n, hn⟩ =>
    haM (hM.isPrime.mem_of_pow_mem _ (le <| hn ▸ hx))⟩

中文:
定理 存在_disjoint_powers_of_span_eq_top
  结论: (s : 集合 α) (hs : span s = ⊤) (I : 理想 α)
  证明: by
  have ⟨M, hM, le⟩ := exists_le_maximal I hI
  have := hM.1.1
  rw [Ne]; rw [eq_top_iff]; rw [← hs]; rw [span_le]; rw [Set.not_subset] at this
  have ⟨a, has, haM⟩ := this
  exact ⟨a, has, Set.disjoint_left.mpr fun x hx ⟨n, hn⟩ =>
    haM (hM.isPrime.mem_of_pow_mem _ (le <| hn ▸ hx))⟩

Depends on / 依赖: Set.disjoint_left.mpr, Set.not_subset, disjoint_left, eq_top_iff, exists_le_maximal, hM.isPrime.mem_of_pow_mem, isPrime, mem_of_pow_mem, not_subset, span_le
-/
theorem exists_disjoint_powers_of_span_eq_top (s : Set α) (hs : span s = ⊤) (I : Ideal α)
    (hI : I != ⊤) : exists r in s, Disjoint (I : Set α) (Submonoid.powers r) := by
  have ⟨M, hM, le⟩ := exists_le_maximal I hI
  have := hM.1.1
  rw [Ne]; rw [eq_top_iff]; rw [← hs]; rw [span_le]; rw [Set.not_subset] at this
  have ⟨a, has, haM⟩ := this
  exact ⟨a, has, Set.disjoint_left.mpr fun x hx ⟨n, hn⟩ =>
    haM (hM.isPrime.mem_of_pow_mem _ (le <| hn ▸ hx))⟩

/--
theorem `span_singleton_lt_span_singleton` / 定理 `span_singleton_lt_span_singleton`

English:
theorem span_singleton_lt_span_singleton
  given: [IsDomain α] {x y : α}
  proof: by
  rw [lt_iff_le_not_ge]; rw [span_singleton_le_span_singleton]; rw [span_singleton_le_span_singleton]; rw [dvd_and_not_dvd_iff]

中文:
定理 span_singleton_lt_span_singleton
  条件: [是整环 α] {x y : α}
  证明: by
  rw [lt_iff_le_not_ge]; rw [span_singleton_le_span_singleton]; rw [span_singleton_le_span_singleton]; rw [dvd_and_not_dvd_iff]

Depends on / 依赖: dvd_and_not_dvd_iff, lt_iff_le_not_ge, span_singleton_le_span_singleton
-/
theorem span_singleton_lt_span_singleton [IsDomain α] {x y : α} :
    span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_ge]; rw [span_singleton_le_span_singleton]; rw [span_singleton_le_span_singleton]; rw [dvd_and_not_dvd_iff]

/--
lemma `isPrime_of_maximally_disjoint` / 引理 `isPrime_of_maximally_disjoint`

English:
lemma isPrime_of_maximally_disjoint
  statement: (I : Ideal α)
  proof: by
    rintro rfl
    have : 1 in (S : Set α) := S.one_mem
    simp_all
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_notMem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_notMem.mpr rid.2)
    simp only [Set.not_disjoint_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁]; rw [← hr₂]
    ring

中文:
引理 isPrime_of_maximally_disjoint
  结论: (I : 理想 α)
  证明: by
    rintro rfl
    have : 1 in (S : Set α) := S.one_mem
    simp_all
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_notMem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_notMem.mpr rid.2)
    simp only [Set.not_disjoint_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁]; rw [← hr₂]
    ring

Depends on / 依赖: S.one_mem, Set.not_disjoint_iff, SetLike, SetLike.mem_coe, Submodule, Submodule.lt_sup_iff_notMem.mpr, Submodule.mem_sup, disjoint, disjoint.ne_, lt_sup_iff_notMem, maximally_disjoint, mem_coe, mem_or_mem, mem_span_singleton, mem_sup, not_disjoint_iff, one_mem
-/
lemma isPrime_of_maximally_disjoint (I : Ideal α)
    (S : Submonoid α)
    (disjoint : Disjoint (I : Set α) S)
    (maximally_disjoint : forall (J : Ideal α), I < J -> ¬ Disjoint (J : Set α) S) :
    I.IsPrime where
  ne_top' := by
    rintro rfl
    have : 1 in (S : Set α) := S.one_mem
    simp_all
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_notMem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_notMem.mpr rid.2)
    simp only [Set.not_disjoint_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁]; rw [← hr₂]
    ring

/--
theorem `exists_le_prime_disjoint` / 定理 `exists_le_prime_disjoint`

English:
theorem exists_le_prime_disjoint
  given: (S : Submonoid α) (disjoint : Disjoint (I : Set α) S)
  proof: by
  have ⟨p, hIp, hp⟩ := zorn_le_nonempty₀ {p : Ideal α | Disjoint (p : Set α) S}
    (fun c hc hc' x hx => ?_) I disjoint
  · exact ⟨p, isPrime_of_maximally_disjoint _ _ hp.1 (fun _ => hp.not_prop_of_gt), hIp, hp.1⟩
  cases isEmpty_or_nonempty c
  · exact ⟨I, disjoint, fun J hJ => isEmptyElim (⟨J, hJ⟩ : c)⟩
  refine ⟨sSup c, Set.disjoint_left.mpr fun x hx => ?_, fun _ => le_sSup⟩
  have ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hx)
  exact Set.disjoint_left.mp (hc p.2) hp

中文:
定理 存在_le_prime_disjoint
  条件: (S : 子幺半群 α) (disjoint : Disjoint (I : 集合 α) S)
  证明: by
  have ⟨p, hIp, hp⟩ := zorn_le_nonempty₀ {p : Ideal α | Disjoint (p : Set α) S}
    (fun c hc hc' x hx => ?_) I disjoint
  · exact ⟨p, isPrime_of_maximally_disjoint _ _ hp.1 (fun _ => hp.not_prop_of_gt), hIp, hp.1⟩
  cases isEmpty_or_nonempty c
  · exact ⟨I, disjoint, fun J hJ => isEmptyElim (⟨J, hJ⟩ : c)⟩
  refine ⟨sSup c, Set.disjoint_left.mpr fun x hx => ?_, fun _ => le_sSup⟩
  have ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hx)
  exact Set.disjoint_left.mp (hc p.2) hp

Depends on / 依赖: Disjoint, Set.disjoint_left.mp, Set.disjoint_left.mpr, Submodule, Submodule.mem_iSup_of_directed, directed, disjoint, disjoint_left, hp.not_prop_of_gt, isEmptyElim, isEmpty_or_nonempty, isPrime_of_maximally_disjoint, le_sSup, mem_iSup_of_directed, not_prop_of_gt, sSup_eq_iSup
-/
theorem exists_le_prime_disjoint (S : Submonoid α) (disjoint : Disjoint (I : Set α) S) :
    exists p : Ideal α, p.IsPrime ∧ I <= p ∧ Disjoint (p : Set α) S := by
  have ⟨p, hIp, hp⟩ := zorn_le_nonempty₀ {p : Ideal α | Disjoint (p : Set α) S}
    (fun c hc hc' x hx => ?_) I disjoint
  · exact ⟨p, isPrime_of_maximally_disjoint _ _ hp.1 (fun _ => hp.not_prop_of_gt), hIp, hp.1⟩
  cases isEmpty_or_nonempty c
  · exact ⟨I, disjoint, fun J hJ => isEmptyElim (⟨J, hJ⟩ : c)⟩
  refine ⟨sSup c, Set.disjoint_left.mpr fun x hx => ?_, fun _ => le_sSup⟩
  have ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hx)
  exact Set.disjoint_left.mp (hc p.2) hp

/--
theorem `exists_le_prime_notMem_of_isIdempotentElem` / 定理 `exists_le_prime_notMem_of_isIdempotentElem`

English:
theorem exists_le_prime_notMem_of_isIdempotentElem
  given: (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I)
  proof: have : Disjoint (I : Set α) (Submonoid.powers a) := Set.disjoint_right.mpr by
    rw [ha.coe_powers]
    rintro _ (rfl | rfl)
    exacts [I.ne_top_iff_one.mp (ne_of_mem_of_not_mem' Submodule.mem_top haI).symm, haI]
  have ⟨p, h1, h2, h3⟩ := exists_le_prime_disjoint _ _ this
  ⟨p, h1, h2, Set.disjoint_right.mp h3 (Submonoid.mem_powers a)⟩

中文:
定理 存在_le_prime_notMem_of_isIdempotentElem
  条件: (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I)
  证明: have : Disjoint (I : Set α) (Submonoid.powers a) := Set.disjoint_right.mpr by
    rw [ha.coe_powers]
    rintro _ (rfl | rfl)
    exacts [I.ne_top_iff_one.mp (ne_of_mem_of_not_mem' Submodule.mem_top haI).symm, haI]
  have ⟨p, h1, h2, h3⟩ := exists_le_prime_disjoint _ _ this
  ⟨p, h1, h2, Set.disjoint_right.mp h3 (Submonoid.mem_powers a)⟩

Depends on / 依赖: Disjoint, I.ne_top_iff_one.mp, Set.disjoint_right.mp, Set.disjoint_right.mpr, Submodule, Submodule.mem_top, Submonoid, Submonoid.mem_powers, Submonoid.powers, coe_powers, disjoint_right, exacts, exists_le_prime_disjoint, ha.coe_powers, mem_powers, mem_top, ne_of_mem_of_not_mem, ne_top_iff_one, powers
-/
theorem exists_le_prime_notMem_of_isIdempotentElem (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I) :
    exists p : Ideal α, p.IsPrime ∧ I <= p ∧ a ∉ p :=
have : Disjoint (I : Set α) (Submonoid.powers a) := Set.disjoint_right.mpr by
    rw [ha.coe_powers]
    rintro _ (rfl | rfl)
    exacts [I.ne_top_iff_one.mp (ne_of_mem_of_not_mem' Submodule.mem_top haI).symm, haI]
  have ⟨p, h1, h2, h3⟩ := exists_le_prime_disjoint _ _ this
  ⟨p, h1, h2, Set.disjoint_right.mp h3 (Submonoid.mem_powers a)⟩

/--
theorem `irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem` / 定理 `irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem`

English:
theorem irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem
  statement: {a : α}
  proof: by
  constructor
  · intro ha
    apply max.ne_top
    rw [span_singleton_eq_top.2 ha]
  · intro u v ha
    by_contra! huv
    have hu : span {u} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.1)
        (span_singleton_le_span_singleton.2 ((dvd_mul_right u v).trans ha.symm.dvd))).ge
    have hv : span {v} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.2)
        (span_singleton_le_span_singleton.2 ((dvd_mul_left v u).trans ha.symm.dvd))).ge
    rw [span_singleton_le_span_singleton] at hu hv
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    refine idem (a * (c * d)) ?_ ?_
    · apply le_antisymm <;> rw [span_singleton_le_span_singleton]
      · exact (dvd_mul_right (a * (c * d)) a).trans (ha.trans (by ring)).symm.dvd
      · apply dvd_mul_right
    · rw [isIdempotentElem_iff]
      refine Eq.trans ?_ (congrArg (· * (c * d)) ha.symm)
      ring

中文:
定理 irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem
  结论: {a : α}
  证明: by
  constructor
  · intro ha
    apply max.ne_top
    rw [span_singleton_eq_top.2 ha]
  · intro u v ha
    by_contra! huv
    have hu : span {u} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.1)
        (span_singleton_le_span_singleton.2 ((dvd_mul_right u v).trans ha.symm.dvd))).ge
    have hv : span {v} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.2)
        (span_singleton_le_span_singleton.2 ((dvd_mul_left v u).trans ha.symm.dvd))).ge
    rw [span_singleton_le_span_singleton] at hu hv
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    refine idem (a * (c * d)) ?_ ?_
    · apply le_antisymm <;> rw [span_singleton_le_span_singleton]
      · exact (dvd_mul_right (a * (c * d)) a).trans (ha.trans (by ring)).symm.dvd
      · apply dvd_mul_right
    · rw [isIdempotentElem_iff]
      refine Eq.trans ?_ (congrArg (· * (c * d)) ha.symm)
      ring

Depends on / 依赖: dvd_mul_left, dvd_mul_right, eq_of_le, ha.symm.dvd, max.eq_of_le, max.ne_top, ne_top, span_singleton_eq_top, span_singleton_le_span_singleton, span_singleton_ne_top
-/
theorem irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem {a : α}
    (max : (Ideal.span {a}).IsMaximal)
    (idem : forall x, Ideal.span {a} = Ideal.span {x} -> ¬IsIdempotentElem x) :
    Irreducible a := by
  constructor
  · intro ha
    apply max.ne_top
    rw [span_singleton_eq_top.2 ha]
  · intro u v ha
    by_contra! huv
    have hu : span {u} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.1)
        (span_singleton_le_span_singleton.2 ((dvd_mul_right u v).trans ha.symm.dvd))).ge
    have hv : span {v} <= span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.2)
        (span_singleton_le_span_singleton.2 ((dvd_mul_left v u).trans ha.symm.dvd))).ge
    rw [span_singleton_le_span_singleton] at hu hv
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    refine idem (a * (c * d)) ?_ ?_
    · apply le_antisymm <;> rw [span_singleton_le_span_singleton]
      · exact (dvd_mul_right (a * (c * d)) a).trans (ha.trans (by ring)).symm.dvd
      · apply dvd_mul_right
    · rw [isIdempotentElem_iff]
      refine Eq.trans ?_ (congrArg (· * (c * d)) ha.symm)
      ring

/--
theorem `irreducible_of_isMaximal_span_singleton` / 定理 `irreducible_of_isMaximal_span_singleton`

English:
theorem irreducible_of_isMaximal_span_singleton
  statement: [IsDomain α] {a : α}
  proof: ((Ideal.span_singleton_prime ha).1 max.isPrime).irreducible

中文:
定理 irreducible_of_isMaximal_span_singleton
  结论: [是整环 α] {a : α}
  证明: ((Ideal.span_singleton_prime ha).1 max.isPrime).irreducible

Depends on / 依赖: Ideal.span_singleton_prime, irreducible, isPrime, max.isPrime, span_singleton_prime
-/
theorem irreducible_of_isMaximal_span_singleton [IsDomain α] {a : α}
    (ha : a != 0) (max : (Ideal.span {a}).IsMaximal) :
    Irreducible a :=
  ((Ideal.span_singleton_prime ha).1 max.isPrime).irreducible

section IsPrincipalIdealRing

variable [IsPrincipalIdealRing α]

/--
theorem `isPrime_iff_of_isPrincipalIdealRing` / 定理 `isPrime_iff_of_isPrincipalIdealRing`

English:
theorem isPrime_iff_of_isPrincipalIdealRing
  given: {P : Ideal α} (hP : P != ⊥)
  proof: by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal P
    exact ⟨p, (span_singleton_prime (by simp [·] at hP)).mp h, rfl⟩
  mpr := by
    rintro ⟨p, hp, rfl⟩
    rwa [span_singleton_prime (by simp [hp.ne_zero])]

中文:
定理 isPrime_iff_of_isPrincipalIdealRing
  条件: {P : 理想 α} (hP : P != ⊥)
  证明: by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal P
    exact ⟨p, (span_singleton_prime (by simp [·] at hP)).mp h, rfl⟩
  mpr := by
    rintro ⟨p, hp, rfl⟩
    rwa [span_singleton_prime (by simp [hp.ne_zero])]

Depends on / 依赖: IsPrincipal, Submodule, Submodule.IsPrincipal.principal, hp.ne_zero, ne_zero, principal, span_singleton_prime
-/
theorem isPrime_iff_of_isPrincipalIdealRing {P : Ideal α} (hP : P != ⊥) :
    P.IsPrime ↔ exists p, Prime p ∧ P = span {p} where
  mp h := by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal P
    exact ⟨p, (span_singleton_prime (by simp [·] at hP)).mp h, rfl⟩
  mpr := by
    rintro ⟨p, hp, rfl⟩
    rwa [span_singleton_prime (by simp [hp.ne_zero])]

/--
theorem `isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors` / 定理 `isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors`

English:
theorem isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors
  statement: [NoZeroDivisors α] [Nontrivial α]
  proof: by
  rw [or_iff_not_imp_left]; rw [← forall_congr' isPrime_iff_of_isPrincipalIdealRing]; rw [← or_iff_not_imp_left]; rw [or_iff_right_of_imp]
  rintro rfl; exact isPrime_bot

中文:
定理 isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors
  结论: [无零因子 α] [非平凡 α]
  证明: by
  rw [or_iff_not_imp_left]; rw [← forall_congr' isPrime_iff_of_isPrincipalIdealRing]; rw [← or_iff_not_imp_left]; rw [or_iff_right_of_imp]
  rintro rfl; exact isPrime_bot

Depends on / 依赖: forall_congr, isPrime_bot, isPrime_iff_of_isPrincipalIdealRing, or_iff_not_imp_left, or_iff_right_of_imp
-/
theorem isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors [NoZeroDivisors α] [Nontrivial α]
    {P : Ideal α} : P.IsPrime ↔ P = ⊥ ∨ exists p, Prime p ∧ P = span {p} := by
  rw [or_iff_not_imp_left]; rw [← forall_congr' isPrime_iff_of_isPrincipalIdealRing]; rw [← or_iff_not_imp_left]; rw [or_iff_right_of_imp]
  rintro rfl; exact isPrime_bot

end IsPrincipalIdealRing

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/--
theorem `bot_isMaximal` / 定理 `bot_isMaximal`

English:
theorem bot_isMaximal
  statement: IsMaximal (⊥ : Ideal K)
  proof: ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

中文:
定理 bot_isMaximal
  结论: 是极大 (⊥ : 理想 K)
  证明: ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

Depends on / 依赖: absurd, eq_bot_or_top, eq_top_iff_one, ne_of_gt, or_iff_not_imp_left, or_iff_not_imp_left.mp
-/
theorem bot_isMaximal : IsMaximal (⊥ : Ideal K) :=
  ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

end Ideal

end DivisionSemiring
