/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Order properties of `CFC.rpow`

This file shows that `a ↦ a ^ p` is monotone for `p ∈ [0, 1]`, where `a` is an element of a
C⋆-algebra. The proof makes use of the integral representation of `rpow` in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation`.

## Main declarations

+ `CFC.monotone_nnrpow`, `CFC.monotone_rpow`: `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`
+ `CFC.monotone_sqrt`: `CFC.sqrt` is operator monotone
+ `CFC.concaveOn_nnrpow`, `CFC.concaveOn_rpow`: `a ↦ a ^ p` is operator concave for `p ∈ [0,1]`
+ `CFC.concaveOn_sqrt`: `CFC.sqrt` is operator concave

## TODO

+ Show that `rpow` over `Icc (-1) 0` is operator antitone and operator convex
+ Show operator convexity of `rpow` over `Icc 1 2`

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

public section

open Set
open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

/--
lemma `monotoneOn_nnrpow_Ioo` / 引理 `monotoneOn_nnrpow_Ioo`

English:
lemma monotoneOn_nnrpow_Ioo
  given: {p : Real>=0} (hp : p in Ioo 0 1)
  proof: by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_o

中文:
引理 monotoneOn_nnrpow_Ioo
  条件: {p : 实数>=0} (hp : p in Ioo 0 1)
  证明: by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_o
-/
private lemma monotoneOn_nnrpow_Ioo {p : Real>=0} (hp : p in Ioo 0 1) :
    MonotoneOn (fun a : A => a ^ p) (Ici 0) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_of_integrand_ae ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact monotoneOn_cfcₙ_rpowIntegrand₀₁ hp ht

/--
lemma `monotone_nnrpow` / 引理 `monotone_nnrpow`

English:
lemma monotone_nnrpow
  given: {p : Real>=0} (hp : p in Icc 0 1)
  proof: by
  intro a b hab
  by_cases ha : 0 <= a
  · have hb : 0 <= b := ha.trans hab
    have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    ·

中文:
引理 monotone_nnrpow
  条件: {p : 实数>=0} (hp : p in Icc 0 1)
  证明: by
  intro a b hab
  by_cases ha : 0 <= a
  · have hb : 0 <= b := ha.trans hab
    have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    ·

Depends on / 依赖: ha.trans, mem_singleton_iff, monotoneOn_nnrpow_Ioo, nnrpow_one
-/
lemma monotone_nnrpow {p : Real>=0} (hp : p in Icc 0 1) :
    Monotone (fun a : A => a ^ p) := by
  intro a b hab
  by_cases ha : 0 <= a
  · have hb : 0 <= b := ha.trans hab
    have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    · simp_all [mem_singleton_iff, nnrpow_one a, nnrpow_one b]
  · have : a ^ p = 0 := cfcₙ_apply_of_not_predicate a ha
    simp [this]

/--
lemma `monotone_sqrt` / 引理 `monotone_sqrt`

English:
lemma monotone_sqrt
  statement: Monotone (sqrt : A -> A)
  proof: by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a]; rw [CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

@[gcongr]

中文:
引理 monotone_sqrt
  结论: Monotone (sqrt : A -> A)
  证明: by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a]; rw [CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

@[gcongr]

Depends on / 依赖: CFC.sqrt_eq_nnrpow, monotone_nnrpow, sqrt_eq_nnrpow
-/
lemma monotone_sqrt : Monotone (sqrt : A -> A) := by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a]; rw [CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

@[gcongr]
/--
lemma `nnrpow_le_nnrpow` / 引理 `nnrpow_le_nnrpow`

English:
lemma nnrpow_le_nnrpow
  given: {p : Real>=0} (hp : p in Icc 0 1) {a b : A} (hab : a <= b)
  proof: monotone_nnrpow hp hab

@[gcongr]

中文:
引理 nnrpow_le_nnrpow
  条件: {p : 实数>=0} (hp : p in Icc 0 1) {a b : A} (hab : a <= b)
  证明: monotone_nnrpow hp hab

@[gcongr]

Depends on / 依赖: monotone_nnrpow
-/
lemma nnrpow_le_nnrpow {p : Real>=0} (hp : p in Icc 0 1) {a b : A} (hab : a <= b) :
    a ^ p <= b ^ p := monotone_nnrpow hp hab

@[gcongr]
/--
lemma `sqrt_le_sqrt` / 引理 `sqrt_le_sqrt`

English:
lemma sqrt_le_sqrt
  given: (a b : A) (hab : a <= b)
  statement: sqrt a <= sqrt b
  proof: monotone_sqrt hab

中文:
引理 sqrt_le_sqrt
  条件: (a b : A) (hab : a <= b)
  结论: sqrt a <= sqrt b
  证明: monotone_sqrt hab

Depends on / 依赖: monotone_sqrt
-/
lemma sqrt_le_sqrt (a b : A) (hab : a <= b) : sqrt a <= sqrt b :=
  monotone_sqrt hab

/--
lemma `concaveOn_nnrpow_Ioo` / 引理 `concaveOn_nnrpow_Ioo`

English:
lemma concaveOn_nnrpow_Ioo
  given: {p : Real>=0} (hp : p in Ioo 0 1)
  proof: by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h₃'.symm
  refine integral_concaveOn_of_

中文:
引理 concaveOn_nnrpow_Ioo
  条件: {p : 实数>=0} (hp : p in Ioo 0 1)
  证明: by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h₃'.symm
  refine integral_concaveOn_of_
-/
private lemma concaveOn_nnrpow_Ioo {p : Real>=0} (hp : p in Ioo 0 1) :
    ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h₃'.symm
  refine integral_concaveOn_of_integrand_ae (convex_Ici _) ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact concaveOn_cfcₙ_rpowIntegrand₀₁ hp ht

/--
lemma `concaveOn_nnrpow` / 引理 `concaveOn_nnrpow`

English:
lemma concaveOn_nnrpow
  given: {p : Real>=0} (hp : p in Icc 0 1)
  proof: by
  have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact concaveOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp, nnrpow_zero]
    exact concaveOn_const _ (convex_Ici _)
  · simp only [mem_s

中文:
引理 concaveOn_nnrpow
  条件: {p : 实数>=0} (hp : p in Icc 0 1)
  证明: by
  have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact concaveOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp, nnrpow_zero]
    exact concaveOn_const _ (convex_Ici _)
  · simp only [mem_s

Depends on / 依赖: ConcaveOn, ConcaveOn.congr, concaveOn_const, concaveOn_id, concaveOn_nnrpow_Ioo, convex_Ici, mem_singleton_iff, nnrpow_one_eqOn, nnrpow_one_eqOn.symm, nnrpow_zero
-/
lemma concaveOn_nnrpow {p : Real>=0} (hp : p in Icc 0 1) :
    ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ p) := by
  have hIcc : Icc (0 : Real>=0) 1 = Ioo 0 1 union {0} union {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · exact concaveOn_nnrpow_Ioo hp
  · simp only [mem_singleton_iff] at hp
    simp only [hp, nnrpow_zero]
    exact concaveOn_const _ (convex_Ici _)
  · simp only [mem_singleton_iff] at hp
    simp only [hp]
    exact ConcaveOn.congr (concaveOn_id (convex_Ici _)) nnrpow_one_eqOn.symm

/--
lemma `concaveOn_sqrt` / 引理 `concaveOn_sqrt`

English:
lemma concaveOn_sqrt
  statement: ConcaveOn Real (Ici (0 : A)) (sqrt : A -> A)
  proof: by
  eta_expand
  simp_rw [sqrt_eq_nnrpow]
  exact concaveOn_nnrpow ⟨by norm_num, by norm_num⟩

中文:
引理 concaveOn_sqrt
  结论: ConcaveOn 实数 (Ici (0 : A)) (sqrt : A -> A)
  证明: by
  eta_expand
  simp_rw [sqrt_eq_nnrpow]
  exact concaveOn_nnrpow ⟨by norm_num, by norm_num⟩

Depends on / 依赖: concaveOn_nnrpow, eta_expand, simp_rw, sqrt_eq_nnrpow
-/
lemma concaveOn_sqrt : ConcaveOn Real (Ici (0 : A)) (sqrt : A -> A) := by
  eta_expand
  simp_rw [sqrt_eq_nnrpow]
  exact concaveOn_nnrpow ⟨by norm_num, by norm_num⟩

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
lemma `monotone_rpow` / 引理 `monotone_rpow`

English:
lemma monotone_rpow
  given: {p : Real} (hp : p in Icc 0 1)
  statement: Monotone (fun a : A => a ^ p)
  proof: by
  let q : Real>=0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · rw [hq]
    intro a b hab
    by_cases ha : 0 <= a
    · have hb : 0 <= b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : Real) = 0 := cfc_ap

中文:
引理 monotone_rpow
  条件: {p : 实数} (hp : p in Icc 0 1)
  结论: Monotone (fun a : A => a ^ p)
  证明: by
  let q : Real>=0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · rw [hq]
    intro a b hab
    by_cases ha : 0 <= a
    · have hb : 0 <= b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : Real) = 0 := cfc_ap

Depends on / 依赖: CFC.nnrpow_eq_rpow, CFC.rpow_zero, Monotone, cfc_apply_of_not_predicate, eq_zero_or_pos, ha.trans, monotone_nnrpow, nnrpow_eq_rpow, rpow_zero, simp_rw
-/
lemma monotone_rpow {p : Real} (hp : p in Icc 0 1) : Monotone (fun a : A => a ^ p) := by
  let q : Real>=0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · rw [hq]
    intro a b hab
    by_cases ha : 0 <= a
    · have hb : 0 <= b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : Real) = 0 := cfc_apply_of_not_predicate a ha
      simp [this]
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact monotone_nnrpow hp

@[gcongr]
/--
lemma `rpow_le_rpow` / 引理 `rpow_le_rpow`

English:
lemma rpow_le_rpow
  given: {p : Real} (hp : p in Icc 0 1) {a b : A} (hab : a <= b)
  proof: monotone_rpow hp hab

中文:
引理 rpow_le_rpow
  条件: {p : 实数} (hp : p in Icc 0 1) {a b : A} (hab : a <= b)
  证明: monotone_rpow hp hab

Depends on / 依赖: monotone_rpow
-/
lemma rpow_le_rpow {p : Real} (hp : p in Icc 0 1) {a b : A} (hab : a <= b) :
    a ^ p <= b ^ p := monotone_rpow hp hab

/--
lemma `concaveOn_rpow` / 引理 `concaveOn_rpow`

English:
lemma concaveOn_rpow
  given: {p : Real} (hp : p in Icc 0 1)
  proof: by
  let q : Real>=0 := ⟨p, hp.1⟩
  change ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · simp only [hq, NNReal.coe_zero]
    exact ConcaveOn.congr (concaveOn_const _ (convex_Ici _)) rpow_zero_eqOn.symm
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    ex

中文:
引理 concaveOn_rpow
  条件: {p : 实数} (hp : p in Icc 0 1)
  证明: by
  let q : Real>=0 := ⟨p, hp.1⟩
  change ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · simp only [hq, NNReal.coe_zero]
    exact ConcaveOn.congr (concaveOn_const _ (convex_Ici _)) rpow_zero_eqOn.symm
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    ex

Depends on / 依赖: CFC.nnrpow_eq_rpow, ConcaveOn, ConcaveOn.congr, NNReal, NNReal.coe_zero, coe_zero, concaveOn_const, concaveOn_nnrpow, convex_Ici, eq_zero_or_pos, nnrpow_eq_rpow, rpow_zero_eqOn, rpow_zero_eqOn.symm, simp_rw
-/
lemma concaveOn_rpow {p : Real} (hp : p in Icc 0 1) :
    ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ p) := by
  let q : Real>=0 := ⟨p, hp.1⟩
  change ConcaveOn Real (Ici (0 : A)) (fun a : A => a ^ (q : Real))
  obtain hq | hq := eq_zero_or_pos q
  · simp only [hq, NNReal.coe_zero]
    exact ConcaveOn.congr (concaveOn_const _ (convex_Ici _)) rpow_zero_eqOn.symm
  · simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact concaveOn_nnrpow hp

end UnitalCStarAlgebra

end CFC
