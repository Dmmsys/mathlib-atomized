/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Almost integral elements -/

@[expose] public section

section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- An element `s` in an `R`-algebra is almost integral if there exists `r ∈ R⁰` such that
`r • s ^ n ∈ R` for all `n`. -/
@[stacks 00GW]
/--
Definition of `IsAlmostIntegral` / `IsAlmostIntegral` 的定义

English:
definition IsAlmostIntegral
  signature: (s : S)
  body: exists r in R⁰, forall n, r • s ^ n in (algebraMap R S).range

中文:
定义 IsAlmost整数egral
  签名: (s : S)
  定义体: exists r in R⁰, forall n, r • s ^ n in (algebraMap R S).range

Depends on / 依赖: algebraMap
-/
def IsAlmostIntegral (s : S) : Prop := exists r in R⁰, forall n, r • s ^ n in (algebraMap R S).range

variable (R S) in
/-- The complete integral closure is the subalgebra of almost integral elements. -/
@[stacks 00GX "Part 1"]
/--
Definition of `completeIntegralClosure` / `completeIntegralClosure` 的定义

English:
definition completeIntegralClosure
  signature: : Subalgebra R S where
  body: { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n => ?_⟩
    rw [mul_pow]; rw [mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs,

中文:
定义 complete整数egralClosure
  签名: : 子代数 R S where
  定义体: { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n => ?_⟩
    rw [mul_pow]; rw [mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs,

Depends on / 依赖: IsAlmostIntegral
-/
def completeIntegralClosure : Subalgebra R S where
  carrier := { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n => ?_⟩
    rw [mul_pow]; rw [mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n => ?_⟩
    simp only [add_pow, Finset.smul_sum, ← smul_mul_assoc _ (_ * _),
      ← smul_mul_smul_comm _ (a ^ _)]
    exact sum_mem fun i _ => mul_mem (mul_mem (hr' _) (hs' _)) (by simp)
  algebraMap_mem' r := ⟨1, one_mem _, by simp [← map_pow]⟩

/--
lemma `mem_completeIntegralClosure` / 引理 `mem_completeIntegralClosure`

English:
lemma mem_completeIntegralClosure
  given: {x : S}
  proof: .rfl

中文:
引理 mem_complete整数egralClosure
  条件: {x : S}
  证明: .rfl
-/
lemma mem_completeIntegralClosure {x : S} :
    x in completeIntegralClosure R S ↔ IsAlmostIntegral R x := .rfl

/--
lemma `IsIntegral.isAlmostIntegral_of_exists_smul_mem_range` / 引理 `IsIntegral.isAlmostIntegral_of_exists_smul_mem_range`

English:
lemma IsIntegral.isAlmostIntegral_of_exists_smul_mem_range
  proof: by
  obtain ⟨b, hb', hb⟩ :
      exists b in R⁰, forall i < (minpoly R s).natDegree, (b • s ^ i) in (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi => ?_⟩
    rw [← Nat.sub_add_cancel hi.le]; rw [pow_add]; rw [mul_smul]; rw [←

中文:
引理 是整.isAlmost整数egral_of_存在_smul_mem_range
  证明: by
  obtain ⟨b, hb', hb⟩ :
      exists b in R⁰, forall i < (minpoly R s).natDegree, (b • s ^ i) in (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi => ?_⟩
    rw [← Nat.sub_add_cancel hi.le]; rw [pow_add]; rw [mul_smul]; rw [←

Depends on / 依赖: AlgHom, AlgHom.range, Algebra, Algebra.ofId, Nat.strong_induction_on, Nat.sub_add_cancel, Subalgebra, Subalgebra.pow_mem, algebraMap, hi.le, lt_or_ge, minpoly, mul_smul, natDegree, pow_add, pow_mem, smul_mem, smul_pow, strong_induction_on, sub_add_cancel
-/
lemma IsIntegral.isAlmostIntegral_of_exists_smul_mem_range
    {s : S} (H : IsIntegral R s) (h : exists t in R⁰, t • s in (algebraMap R S).range) :
    IsAlmostIntegral R s := by
  obtain ⟨b, hb', hb⟩ :
      exists b in R⁰, forall i < (minpoly R s).natDegree, (b • s ^ i) in (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi => ?_⟩
    rw [← Nat.sub_add_cancel hi.le]; rw [pow_add]; rw [mul_smul]; rw [← smul_pow]
    exact (AlgHom.range (Algebra.ofId _ _)).smul_mem (Subalgebra.pow_mem _ ht' _) _
  refine ⟨b, hb', fun n => ?_⟩
  induction n using Nat.strong_induction_on with | h n IH =>
  obtain hn | hn := lt_or_ge n (minpoly R s).natDegree
  · exact hb _ (by simpa)
  have := minpoly.aeval R s
  rw [Polynomial.aeval_eq_sum_range]; rw [Finset.sum_range_succ]; rw [add_eq_zero_iff_eq_neg']; rw [Polynomial.coeff_natDegree]; rw [minpoly.monic H]; rw [one_smul] at this
  rw [← Nat.sub_add_cancel hn]; rw [pow_add]; rw [this]; rw [mul_neg]; rw [smul_neg]; rw [Finset.mul_sum]; rw [Finset.smul_sum]
  simp_rw [mul_smul_comm, ← pow_add, smul_comm b]
  refine neg_mem (sum_mem fun i hi => (AlgHom.range (Algebra.ofId _ _)).smul_mem (IH _ ?_) _)
  simp only [Finset.mem_range] at hi
  lia

/--
lemma `IsIntegral.isAlmostIntegral_of_isLocalization` / 引理 `IsIntegral.isAlmostIntegral_of_isLocalization`

English:
lemma IsIntegral.isAlmostIntegral_of_isLocalization
  proof: by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

@[stacks 00GX "Part 2"]

中文:
引理 是整.isAlmost整数egral_of_isLocalization
  证明: by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

@[stacks 00GX "Part 2"]

Depends on / 依赖: H.isAlmostIntegral_of_exists_smul_mem_range, IsLocalization, IsLocalization.exists_mk, exists_mk, isAlmostIntegral_of_exists_smul_mem_range
-/
lemma IsIntegral.isAlmostIntegral_of_isLocalization
    {s : S} (H : IsIntegral R s) (M : Submonoid R) (hM : M <= R⁰) [IsLocalization M S] :
    IsAlmostIntegral R s := by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

@[stacks 00GX "Part 2"]
/--
lemma `IsIntegral.isAlmostIntegral` / 引理 `IsIntegral.isAlmostIntegral`

English:
lemma IsIntegral.isAlmostIntegral
  statement: [IsFractionRing R S]
  proof: H.isAlmostIntegral_of_isLocalization _ le_rfl

中文:
引理 是整.isAlmost整数egral
  结论: [IsFractionRing R S]
  证明: H.isAlmostIntegral_of_isLocalization _ le_rfl

Depends on / 依赖: H.isAlmostIntegral_of_isLocalization, isAlmostIntegral_of_isLocalization, le_rfl
-/
lemma IsIntegral.isAlmostIntegral [IsFractionRing R S]
    {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s :=
  H.isAlmostIntegral_of_isLocalization _ le_rfl

/--
lemma `integralClosure_le_completeIntegralClosure` / 引理 `integralClosure_le_completeIntegralClosure`

English:
lemma integralClosure_le_completeIntegralClosure
  given: [IsFractionRing R S]
  proof: fun _ h => h.isAlmostIntegral

中文:
引理 integralClosure_le_complete整数egralClosure
  条件: [IsFractionRing R S]
  证明: fun _ h => h.isAlmostIntegral

Depends on / 依赖: h.isAlmostIntegral, isAlmostIntegral
-/
lemma integralClosure_le_completeIntegralClosure [IsFractionRing R S] :
    integralClosure R S <= completeIntegralClosure R S :=
  fun _ h => h.isAlmostIntegral

/--
lemma `IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap` / 引理 `IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap`

English:
lemma IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap
  proof: by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} ->ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
(p := (Algebra.adjoin R {s}).toSubmodule) by
    change (Algebra.a

中文:
引理 IsAlmost整数egral.is整数egral_of_nonZeroDivisors_le_comap
  证明: by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} ->ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
(p := (Algebra.adjoin R {s}).toSubmodule) by
    change (Algebra.a

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_eq_span, IsScalarTower, IsScalarTower.toAlgHom, Localization, Localization.Away, Localization.Away.invSelf, Submodule, Submodule.mem_span_singl, Submodule.span, Submodule.span_le, Submonoid, Submonoid.powers_eq_closure, adjoin, adjoin_eq_span, algebraMap, invSelf, mem_span_singl, powers_eq_closure
-/
lemma IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap
    {s : S} (H : IsAlmostIntegral R s) [IsNoetherianRing R]
    (H' : R⁰ <= S⁰.comap (algebraMap R S)) : IsIntegral R s := by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} ->ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
(p := (Algebra.adjoin R {s}).toSubmodule) by
    change (Algebra.adjoin R {s}).toSubmodule <= (Submodule.span _ _).comap _
    rw [Algebra.adjoin_eq_span]; rw [← Submonoid.powers_eq_closure]; rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := hr' n
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    suffices algebraMap _ _ (s ^ n) * algebraMap _ _ ((algebraMap R S) r) *
        Localization.Away.invSelf ((algebraMap R S) r) = algebraMap S _ (s ^ n) by
      simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away _),
        ha, mul_assoc, mul_left_comm] using this
    simp [mul_assoc, Localization.Away.invSelf, Localization.mk_eq_mk']
  have : Function.Injective f := by
    have : Function.Injective (algebraMap S (Localization.Away (algebraMap R S r))) := by
      apply IsLocalization.injective (M := .powers (algebraMap R S r))
      exact Submonoid.powers_le.mpr (H' hr)
    exact fun x y e => Subtype.ext (this congr($e))
  have : (Algebra.adjoin R {s}).toSubmodule.FG := by
    rw [← Module.Finite.iff_fg]
    exact .of_injective f this
  exact .of_mem_of_fg _ this _ (Algebra.self_mem_adjoin_singleton R s)

@[stacks 00GX "Part 3"]
/--
lemma `IsAlmostIntegral.isIntegral` / 引理 `IsAlmostIntegral.isIntegral`

English:
lemma IsAlmostIntegral.isIntegral
  statement: [IsNoetherianRing R] [IsDomain S] [FaithfulSMul R S]
  proof: by
  have := IsDomain.of_faithfulSMul R S
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ => by simp

中文:
引理 IsAlmost整数egral.is整数egral
  结论: [是Noether环 R] [是整环 S] [忠实标量乘法 R S]
  证明: by
  have := IsDomain.of_faithfulSMul R S
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ => by simp

Depends on / 依赖: H.isIntegral_of_nonZeroDivisors_le_comap, IsDomain, IsDomain.of_faithfulSMul, isIntegral_of_nonZeroDivisors_le_comap, of_faithfulSMul
-/
lemma IsAlmostIntegral.isIntegral [IsNoetherianRing R] [IsDomain S] [FaithfulSMul R S]
    {s : S} (H : IsAlmostIntegral R s) : IsIntegral R s := by
  have := IsDomain.of_faithfulSMul R S
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ => by simp

/--
lemma `isAlmostIntegral_iff_isIntegral` / 引理 `isAlmostIntegral_iff_isIntegral`

English:
lemma isAlmostIntegral_iff_isIntegral
  statement: [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S]
  proof: letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩

中文:
引理 isAlmost整数egral_iff_is整数egral
  结论: [是Noether环 R] [是整环 R] [IsFractionRing R S]
  证明: letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩

Depends on / 依赖: IsAlmostIntegral, IsAlmostIntegral.isIntegral, IsFractionRing, IsFractionRing.isDomain, IsIntegral, IsIntegral.isAlmostIntegral, isAlmostIntegral, isDomain, isIntegral
-/
lemma isAlmostIntegral_iff_isIntegral [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S]
    {s : S} : IsAlmostIntegral R s ↔ IsIntegral R s :=
  letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩

/--
lemma `completeIntegralClosure_eq_integralClosure` / 引理 `completeIntegralClosure_eq_integralClosure`

English:
lemma completeIntegralClosure_eq_integralClosure
  proof: SetLike.ext fun _ => isAlmostIntegral_iff_isIntegral

中文:
引理 complete整数egralClosure_eq_integralClosure
  证明: SetLike.ext fun _ => isAlmostIntegral_iff_isIntegral

Depends on / 依赖: SetLike, SetLike.ext, isAlmostIntegral_iff_isIntegral
-/
lemma completeIntegralClosure_eq_integralClosure
    [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S] :
    completeIntegralClosure R S = integralClosure R S :=
  SetLike.ext fun _ => isAlmostIntegral_iff_isIntegral

end
