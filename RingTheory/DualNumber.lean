/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`: The dual numbers over a field `K` form a local ring.
* `DualNumber.instPrincipalIdealRing`: The dual numbers over a field `K` form a principal ideal
  ring.

-/

public section

namespace TrivSqZeroExt

variable {R M : Type*}

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

/--
lemma `isNilpotent_iff_isNilpotent_fst` / 引理 `isNilpotent_iff_isNilpotent_fst`

English:
lemma isNilpotent_iff_isNilpotent_fst
  given: {x : TrivSqZeroExt R M}
  proof: by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow]; rw [hn]; rw [fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_a

中文:
引理 isNilpotent_iff_isNilpotent_fst
  条件: {x : TrivSqZeroExt R M}
  证明: by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow]; rw [hn]; rw [fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_a

Depends on / 依赖: MulOpposite, MulOpposite.op_zero, fst_pow, fst_zero, op_zero, pow_mul, pow_two, snd_mul, snd_zero, two_ne_zero, zero_add, zero_pow, zero_smul
-/
lemma isNilpotent_iff_isNilpotent_fst {x : TrivSqZeroExt R M} :
    IsNilpotent x ↔ IsNilpotent x.fst := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow]; rw [hn]; rw [fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_add,
        snd_zero]

@[simp]
/--
lemma `isNilpotent_inl_iff` / 引理 `isNilpotent_inl_iff`

English:
lemma isNilpotent_inl_iff
  given: (r : R)
  statement: IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ IsNilpotent r
  proof: by
  rw [isNilpotent_iff_isNilpotent_fst]; rw [fst_inl]

@[simp]

中文:
引理 isNilpotent_inl_iff
  条件: (r : R)
  结论: IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ IsNilpotent r
  证明: by
  rw [isNilpotent_iff_isNilpotent_fst]; rw [fst_inl]

@[simp]

Depends on / 依赖: fst_inl, isNilpotent_iff_isNilpotent_fst
-/
lemma isNilpotent_inl_iff (r : R) : IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ IsNilpotent r := by
  rw [isNilpotent_iff_isNilpotent_fst]; rw [fst_inl]

@[simp]
/--
lemma `isNilpotent_inr` / 引理 `isNilpotent_inr`

English:
lemma isNilpotent_inr
  given: (x : M)
  statement: IsNilpotent (.inr x : TrivSqZeroExt R M)
  proof: by
  refine ⟨2, by simp [pow_two]⟩

中文:
引理 isNilpotent_inr
  条件: (x : M)
  结论: IsNilpotent (.inr x : TrivSqZeroExt R M)
  证明: by
  refine ⟨2, by simp [pow_two]⟩

Depends on / 依赖: Encodable, Encodable.encode, S.cons, S.nat, encodableT_toS, encode, pow_two
-/
lemma isNilpotent_inr (x : M) : IsNilpotent (.inr x : TrivSqZeroExt R M) := by
  refine ⟨2, by simp [pow_two]⟩

end Semiring

/--
lemma `isUnit_or_isNilpotent_of_isMaximal_isNilpotent` / 引理 `isUnit_or_isNilpotent_of_isMaximal_isNilpotent`

English:
lemma isUnit_or_isNilpotent_of_isMaximal_isNilpotent
  statement: [CommSemiring R] [AddCommGroup M]
  proof: by
  rw [isUnit_iff_isUnit_fst]; rw [isNilpotent_iff_isNilpotent_fst]
  refine (em _).imp_right fun ha => ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn => ?_
  exact hn.le (Ideal.pow_mem_pow haI _)

中文:
引理 isUnit_or_isNilpotent_of_isMaximal_isNilpotent
  结论: [CommSemiring R] [AddCommGroup M]
  证明: by
  rw [isUnit_iff_isUnit_fst]; rw [isNilpotent_iff_isNilpotent_fst]
  refine (em _).imp_right fun ha => ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn => ?_
  exact hn.le (Ideal.pow_mem_pow haI _)

Depends on / 依赖: Encodable, Encodable.ofLeftInjection, Ideal.pow_mem_pow, S.cons, constructors, encodableT, encodableT_fromS, encodableT_toS, encoded, exists_max_ideal_of_mem_nonunits, hn.le, imp_right, isNilpotent_iff_isNilpotent_fst, isUnit_iff_isUnit_fst, linked, mem_nonunits_iff, mem_nonunits_iff.mpr, ofLeftInjection, pow_mem_pow, tagged
-/
lemma isUnit_or_isNilpotent_of_isMaximal_isNilpotent [CommSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (h : forall I : Ideal R, I.IsMaximal -> IsNilpotent I)
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  rw [isUnit_iff_isUnit_fst]; rw [isNilpotent_iff_isNilpotent_fst]
  refine (em _).imp_right fun ha => ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn => ?_
  exact hn.le (Ideal.pow_mem_pow haI _)

/--
lemma `isUnit_or_isNilpotent` / 引理 `isUnit_or_isNilpotent`

English:
lemma isUnit_or_isNilpotent
  statement: [DivisionSemiring R] [AddCommGroup M]
  proof: by
  simp [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst, em']

中文:
引理 isUnit_or_isNilpotent
  结论: [DivisionSemiring R] [AddCommGroup M]
  证明: by
  simp [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst, em']

Depends on / 依赖: isNilpotent_iff_isNilpotent_fst, isUnit_iff_isUnit_fst
-/
lemma isUnit_or_isNilpotent [DivisionSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  simp [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst, em']

end TrivSqZeroExt

namespace DualNumber
variable {R : Type*}

/--
lemma `fst_eq_zero_iff_eps_dvd` / 引理 `fst_eq_zero_iff_eps_dvd`

English:
lemma fst_eq_zero_iff_eps_dvd
  given: [Semiring R] {x : R[ε]}
  proof: by
  simp_rw [dvd_def, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
    fst_eps, snd_eps, zero_mul, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, exists_and_left, iff_self_and]
  intro
  exact ⟨.inl x.snd, rfl⟩

中文:
引理 fst_eq_zero_iff_eps_dvd
  条件: [Semiring R] {x : R[ε]}
  证明: by
  simp_rw [dvd_def, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
    fst_eps, snd_eps, zero_mul, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, exists_and_left, iff_self_and]
  intro
  exact ⟨.inl x.snd, rfl⟩

Depends on / 依赖: MulOpposite, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, TrivSqZeroExt, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, dvd_def, exists_and_left, ext_iff, fst_eps, fst_mul, iff_self_and, one_mul, simp_rw, smul_eq_mul_unop, snd_eps, snd_mul, unop_op, x.snd
-/
lemma fst_eq_zero_iff_eps_dvd [Semiring R] {x : R[ε]} :
    x.fst = 0 ↔ ε ∣ x := by
  simp_rw [dvd_def, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
    fst_eps, snd_eps, zero_mul, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, exists_and_left, iff_self_and]
  intro
  exact ⟨.inl x.snd, rfl⟩

/--
lemma `isNilpotent_eps` / 引理 `isNilpotent_eps`

English:
lemma isNilpotent_eps
  given: [Semiring R]
  proof: TrivSqZeroExt.isNilpotent_inr 1

中文:
引理 isNilpotent_eps
  条件: [Semiring R]
  证明: TrivSqZeroExt.isNilpotent_inr 1

Depends on / 依赖: TrivSqZeroExt, TrivSqZeroExt.isNilpotent_inr, isNilpotent_inr
-/
lemma isNilpotent_eps [Semiring R] :
    IsNilpotent (ε : R[ε]) :=
  TrivSqZeroExt.isNilpotent_inr 1

open TrivSqZeroExt

/--
lemma `isNilpotent_iff_eps_dvd` / 引理 `isNilpotent_iff_eps_dvd`

English:
lemma isNilpotent_iff_eps_dvd
  given: [DivisionSemiring R] {x : R[ε]}
  proof: by
  simp only [isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero, fst_eq_zero_iff_eps_dvd]

中文:
引理 isNilpotent_iff_eps_dvd
  条件: [DivisionSemiring R] {x : R[ε]}
  证明: by
  simp only [isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero, fst_eq_zero_iff_eps_dvd]

Depends on / 依赖: fst_eq_zero_iff_eps_dvd, isNilpotent_iff_eq_zero, isNilpotent_iff_isNilpotent_fst
-/
lemma isNilpotent_iff_eps_dvd [DivisionSemiring R] {x : R[ε]} :
    IsNilpotent x ↔ ε ∣ x := by
  simp only [isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero, fst_eq_zero_iff_eps_dvd]

section Field

variable {K : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: K] : IsLocalRing K[ε] where
  body: by
    rw [add_comm]; rw [← eq_sub_iff_add_eq] at h
    rcases eq_or_ne (fst a) 0 with ha | ha <;>
    simp [isUnit_iff_isUnit_fst, h, ha]

中文:
实例 [DivisionRing
  签名: K] : IsLocalRing K[ε] where
  定义体: by
    rw [add_comm]; rw [← eq_sub_iff_add_eq] at h
    rcases eq_or_ne (fst a) 0 with ha | ha <;>
    simp [isUnit_iff_isUnit_fst, h, ha]

Depends on / 依赖: add_comm, eq_or_ne, eq_sub_iff_add_eq, isUnit_iff_isUnit_fst
-/
instance [DivisionRing K] : IsLocalRing K[ε] where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [add_comm]; rw [← eq_sub_iff_add_eq] at h
    rcases eq_or_ne (fst a) 0 with ha | ha <;>
    simp [isUnit_iff_isUnit_fst, h, ha]

/--
lemma `ideal_trichotomy` / 引理 `ideal_trichotomy`

English:
lemma ideal_trichotomy
  given: [DivisionRing K] (I : Ideal K[ε])
  proof: by
  refine (eq_or_ne I ⊥).imp_right fun hb => ?_
  refine (eq_or_ne I ⊤).symm.imp_left fun ht => ?_
  have hd : forall x in I, ε ∣ x := by
    intro x hxI
    rcases isUnit_or_isNilpotent x with hx | hx
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxI hx) ht
    · rwa [← isNilpotent_iff_eps_dvd

中文:
引理 ideal_trichotomy
  条件: [DivisionRing K] (I : Ideal K[ε])
  证明: by
  refine (eq_or_ne I ⊥).imp_right fun hb => ?_
  refine (eq_or_ne I ⊤).symm.imp_left fun ht => ?_
  have hd : forall x in I, ε ∣ x := by
    intro x hxI
    rcases isUnit_or_isNilpotent x with hx | hx
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxI hx) ht
    · rwa [← isNilpotent_iff_eps_dvd

Depends on / 依赖: Ideal.eq_top_of_isUnit_mem, absurd, contrapose, eq_or_ne, eq_top_of_isUnit_mem, imp_left, imp_right, isNilpotent_iff_eps_dvd, isUnit_or_isNilpotent, symm.imp_left
-/
lemma ideal_trichotomy [DivisionRing K] (I : Ideal K[ε]) :
    I = ⊥ ∨ I = .span {ε} ∨ I = ⊤ := by
  refine (eq_or_ne I ⊥).imp_right fun hb => ?_
  refine (eq_or_ne I ⊤).symm.imp_left fun ht => ?_
  have hd : forall x in I, ε ∣ x := by
    intro x hxI
    rcases isUnit_or_isNilpotent x with hx | hx
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxI hx) ht
    · rwa [← isNilpotent_iff_eps_dvd]
  have hd' : forall x in I, x != 0 -> exists r, ε = r * x := by
    intro x hxI hx0
    obtain ⟨r, rfl⟩ := hd _ hxI
    have : ε * r = (fst r) • ε := by ext <;> simp
    rw [this] at hxI hx0 ⊢
    have hr : fst r != 0 := by
      contrapose hx0
      simp [hx0]
    refine ⟨r⁻¹, ?_⟩
    simp [TrivSqZeroExt.ext_iff, inv_mul_cancel₀ hr]
  refine le_antisymm ?_ ?_ <;> intro x <;>
    simp_rw [Ideal.mem_span_singleton', (commute_eps_right _).eq, eq_comm, ← dvd_def]
  · intro hx
    simp_rw [hd _ hx]
  · intro hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨r, hr⟩ := hd' _ hyI hy0
    rw [(commute_eps_left _).eq]; rw [hr]; rw [← mul_assoc]
    exact Ideal.mul_mem_left _ _ hyI

/--
lemma `isMaximal_span_singleton_eps` / 引理 `isMaximal_span_singleton_eps`

English:
lemma isMaximal_span_singleton_eps
  given: [DivisionRing K]
  proof: by
  refine ⟨?_, fun I hI => ?_⟩
  · simp [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff]
  · rcases ideal_trichotomy I with rfl | rfl | rfl <;>
    first | simp at hI | simp

中文:
引理 isMaximal_span_singleton_eps
  条件: [DivisionRing K]
  证明: by
  refine ⟨?_, fun I hI => ?_⟩
  · simp [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff]
  · rcases ideal_trichotomy I with rfl | rfl | rfl <;>
    first | simp at hI | simp

Depends on / 依赖: Ideal.eq_top_iff_one, Ideal.mem_span_singleton, TrivSqZeroExt, TrivSqZeroExt.ext_iff, eq_top_iff_one, ext_iff, ideal_trichotomy, mem_span_singleton, ne_eq
-/
lemma isMaximal_span_singleton_eps [DivisionRing K] :
    (Ideal.span {ε} : Ideal K[ε]).IsMaximal := by
  refine ⟨?_, fun I hI => ?_⟩
  · simp [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff]
  · rcases ideal_trichotomy I with rfl | rfl | rfl <;>
    first | simp at hI | simp

/--
lemma `maximalIdeal_eq_span_singleton_eps` / 引理 `maximalIdeal_eq_span_singleton_eps`

English:
lemma maximalIdeal_eq_span_singleton_eps
  given: [Field K]
  proof: (IsLocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm

中文:
引理 maximalIdeal_eq_span_singleton_eps
  条件: [Field K]
  证明: (IsLocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm

Depends on / 依赖: IsLocalRing, IsLocalRing.eq_maximalIdeal, eq_maximalIdeal, isMaximal_span_singleton_eps
-/
lemma maximalIdeal_eq_span_singleton_eps [Field K] :
    IsLocalRing.maximalIdeal K[ε] = Ideal.span {ε} :=
  (IsLocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: K] : IsPrincipalIdealRing K[ε] where
  body: by
    rcases ideal_trichotomy I with rfl | rfl | rfl
    · exact bot_isPrincipal
    · exact ⟨_, rfl⟩
    · exact top_isPrincipal

中文:
实例 [DivisionRing
  签名: K] : IsPrincipalIdealRing K[ε] where
  定义体: by
    rcases ideal_trichotomy I with rfl | rfl | rfl
    · exact bot_isPrincipal
    · exact ⟨_, rfl⟩
    · exact top_isPrincipal

Depends on / 依赖: bot_isPrincipal, ideal_trichotomy, top_isPrincipal
-/
instance [DivisionRing K] : IsPrincipalIdealRing K[ε] where
  principal I := by
    rcases ideal_trichotomy I with rfl | rfl | rfl
    · exact bot_isPrincipal
    · exact ⟨_, rfl⟩
    · exact top_isPrincipal

/--
lemma `exists_mul_left_or_mul_right` / 引理 `exists_mul_left_or_mul_right`

English:
lemma exists_mul_left_or_mul_right
  given: [DivisionRing K] (a b : K[ε])
  proof: by
  rcases isUnit_or_isNilpotent a with ha | ha
  · lift a to K[ε]ˣ using ha
    exact ⟨a⁻¹ * b, by simp⟩
  rcases isUnit_or_isNilpotent b with hb | hb
  · lift b to K[ε]ˣ using hb
    exact ⟨b⁻¹ * a, by simp⟩
  rw [isNilpotent_iff_eps_dvd] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
 

中文:
引理 exists_mul_left_or_mul_right
  条件: [DivisionRing K] (a b : K[ε])
  证明: by
  rcases isUnit_or_isNilpotent a with ha | ha
  · lift a to K[ε]ˣ using ha
    exact ⟨a⁻¹ * b, by simp⟩
  rcases isUnit_or_isNilpotent b with hb | hb
  · lift b to K[ε]ˣ using hb
    exact ⟨b⁻¹ * a, by simp⟩
  rw [isNilpotent_iff_eps_dvd] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
 

Depends on / 依赖: Or.inr, TrivSqZeroExt, TrivSqZeroExt.ext_iff, eq_or_ne, ext_iff, isNilpotent_iff_eps_dvd, isUnit_or_isNilpotent
-/
lemma exists_mul_left_or_mul_right [DivisionRing K] (a b : K[ε]) :
    exists c, a * c = b ∨ b * c = a := by
  rcases isUnit_or_isNilpotent a with ha | ha
  · lift a to K[ε]ˣ using ha
    exact ⟨a⁻¹ * b, by simp⟩
  rcases isUnit_or_isNilpotent b with hb | hb
  · lift b to K[ε]ˣ using hb
    exact ⟨b⁻¹ * a, by simp⟩
  rw [isNilpotent_iff_eps_dvd] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  suffices exists c, fst x * fst c = fst y ∨ fst y * fst c = fst x by
    simpa [TrivSqZeroExt.ext_iff] using this
  rcases eq_or_ne (fst x) 0 with hx | hx
  · refine ⟨ε, Or.inr ?_⟩
    simp [hx]
  refine ⟨inl ((fst x)⁻¹ * fst y), ?_⟩
  simp [← mul_assoc, mul_inv_cancel₀ hx]

end Field

end DualNumber
