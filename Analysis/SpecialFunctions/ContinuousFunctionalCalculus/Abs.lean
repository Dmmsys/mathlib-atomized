/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric


/-!
# Absolute value defined via the continuous functional calculus

This file defines the absolute value via the non-unital continuous functional calculus
and provides basic API.

## Main declarations

+ `CFC.abs`: The absolute value as `abs a := CFC.sqrt (star a * a)`.

-/

@[expose] public section

variable {𝕜 A : Type*}

open scoped NNReal
open CFC

namespace CFC

section NonUnital

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module Real A] [SMulCommClass Real A A] [IsScalarTower Real A A]
  [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]

/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: (a : A)
  body: sqrt (star a * a)

@[simp, grind =]

中文:
定义 abs
  签名: (a : A)
  定义体: sqrt (star a * a)

@[simp, grind =]
-/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp, grind =]
/--
lemma `abs_neg` / 引理 `abs_neg`

English:
lemma abs_neg
  given: (a : A)
  statement: abs (-a) = abs a
  proof: by
  simp [abs]

@[simp, grind ←]

中文:
引理 abs_neg
  条件: (a : A)
  结论: abs (-a) = abs a
  证明: by
  simp [abs]

@[simp, grind ←]
-/
lemma abs_neg (a : A) : abs (-a) = abs a := by
  simp [abs]

@[simp, grind ←]
/--
lemma `abs_nonneg` / 引理 `abs_nonneg`

English:
lemma abs_nonneg
  given: (a : A)
  statement: 0 <= abs a
  proof: sqrt_nonneg _

中文:
引理 abs_nonneg
  条件: (a : A)
  结论: 0 <= abs a
  证明: sqrt_nonneg _

Depends on / 依赖: sqrt_nonneg
-/
lemma abs_nonneg (a : A) : 0 <= abs a := sqrt_nonneg _

/--
lemma `abs_star` / 引理 `abs_star`

English:
lemma abs_star
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  statement: abs (star a) = abs a
  proof: by
  simp [abs, star_comm_self']

@[simp, grind =]

中文:
引理 abs_star
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  结论: abs (star a) = abs a
  证明: by
  simp [abs, star_comm_self']

@[simp, grind =]

Depends on / 依赖: cfc_tac, star_comm_self
-/
lemma abs_star (a : A) (ha : IsStarNormal a := by cfc_tac) : abs (star a) = abs a := by
  simp [abs, star_comm_self']

@[simp, grind =]
/--
lemma `abs_zero` / 引理 `abs_zero`

English:
lemma abs_zero
  statement: abs (0 : A) = 0
  proof: by
  simp [abs]

中文:
引理 abs_zero
  结论: abs (0 : A) = 0
  证明: by
  simp [abs]
-/
lemma abs_zero : abs (0 : A) = 0 := by
  simp [abs]

variable [IsTopologicalRing A] [T2Space A]

/--
lemma `abs_mul_abs` / 引理 `abs_mul_abs`

English:
lemma abs_mul_abs
  given: (a : A)
  statement: abs a * abs a = star a * a
  proof: sqrt_mul_sqrt_self _ star_mul_self_nonneg _

中文:
引理 abs_mul_abs
  条件: (a : A)
  结论: abs a * abs a = star a * a
  证明: sqrt_mul_sqrt_self _ star_mul_self_nonneg _

Depends on / 依赖: sqrt_mul_sqrt_self, star_mul_self_nonneg
-/
lemma abs_mul_abs (a : A) : abs a * abs a = star a * a :=
sqrt_mul_sqrt_self _ star_mul_self_nonneg _

/--
lemma `_root_.Commute.cfcAbs_left` / 引理 `_root_.Commute.cfcAbs_left`

English:
lemma _root_.Commute.cfcAbs_left
  given: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  proof: .cfcₙ_nnreal (by simp_all [h₂.star_left]) _

中文:
引理 _root_.Commute.cfcAbs_left
  条件: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  证明: .cfcₙ_nnreal (by simp_all [h₂.star_left]) _

Depends on / 依赖: star_left
-/
lemma _root_.Commute.cfcAbs_left {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) b :=
  .cfcₙ_nnreal (by simp_all [h₂.star_left]) _

/--
lemma `_root_.Commute.cfcAbs_right` / 引理 `_root_.Commute.cfcAbs_right`

English:
lemma _root_.Commute.cfcAbs_right
  given: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  proof: .symm h₁.cfcAbs_left h₂

中文:
引理 _root_.Commute.cfcAbs_right
  条件: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  证明: .symm h₁.cfcAbs_left h₂

Depends on / 依赖: cfcAbs_left
-/
lemma _root_.Commute.cfcAbs_right {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute b (abs a) :=
.symm h₁.cfcAbs_left h₂

/--
lemma `_root_.Commute.cfcAbs_cfcAbs` / 引理 `_root_.Commute.cfcAbs_cfcAbs`

English:
lemma _root_.Commute.cfcAbs_cfcAbs
  given: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  proof: .symm .symm.cfcₙ_nnreal _ Commute.cfcₙ_nnreal (by simp_all [h₂.star_left]) _

中文:
引理 _root_.Commute.cfcAbs_cfcAbs
  条件: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  证明: .symm .symm.cfcₙ_nnreal _ Commute.cfcₙ_nnreal (by simp_all [h₂.star_left]) _

Depends on / 依赖: Commute, Commute.cfc, star_left, symm.cfc
-/
lemma _root_.Commute.cfcAbs_cfcAbs {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) (abs b) :=
.symm .symm.cfcₙ_nnreal _ Commute.cfcₙ_nnreal (by simp_all [h₂.star_left]) _

/--
lemma `commute_abs_self` / 引理 `commute_abs_self`

English:
lemma commute_abs_self
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: .cfcAbs_left (.refl a) ha.star_comm_self.symm

中文:
引理 commute_abs_self
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: .cfcAbs_left (.refl a) ha.star_comm_self.symm

Depends on / 依赖: Commute, cfcAbs_left, cfc_tac, ha.star_comm_self.symm, star_comm_self
-/
lemma commute_abs_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    Commute (abs a) a :=
  .cfcAbs_left (.refl a) ha.star_comm_self.symm

/--
lemma `_root_.Commute.cfcAbs_mul_eq` / 引理 `_root_.Commute.cfcAbs_mul_eq`

English:
lemma _root_.Commute.cfcAbs_mul_eq
  given: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  proof: by
  have hab := h₁.cfcAbs_cfcAbs h₂
  rw [abs]; rw [CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (hab.mul_nonneg (abs_nonneg a) (abs_nonneg b))]; rw [hab.eq]; rw [hab.mul_mul_mul_comm]; rw [abs_mul_abs]; rw [abs_mul_abs]; rw [star_mul]; rw [h₂.star_left.symm.mul_mul_mul_comm]; rw [h₁.eq]

中文:
引理 _root_.Commute.cfcAbs_mul_eq
  条件: {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b))
  证明: by
  have hab := h₁.cfcAbs_cfcAbs h₂
  rw [abs]; rw [CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (hab.mul_nonneg (abs_nonneg a) (abs_nonneg b))]; rw [hab.eq]; rw [hab.mul_mul_mul_comm]; rw [abs_mul_abs]; rw [abs_mul_abs]; rw [star_mul]; rw [h₂.star_left.symm.mul_mul_mul_comm]; rw [h₁.eq]

Depends on / 依赖: CFC.sqrt_eq_iff, abs_mul_abs, abs_nonneg, cfcAbs_cfcAbs, hab.eq, hab.mul_mul_mul_comm, hab.mul_nonneg, mul_mul_mul_comm, mul_nonneg, sqrt_eq_iff, star_left, star_left.symm.mul_mul_mul_comm, star_mul, star_mul_self_nonneg
-/
lemma _root_.Commute.cfcAbs_mul_eq {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    abs (a * b) = abs a * abs b := by
  have hab := h₁.cfcAbs_cfcAbs h₂
  rw [abs]; rw [CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (hab.mul_nonneg (abs_nonneg a) (abs_nonneg b))]; rw [hab.eq]; rw [hab.mul_mul_mul_comm]; rw [abs_mul_abs]; rw [abs_mul_abs]; rw [star_mul]; rw [h₂.star_left.symm.mul_mul_mul_comm]; rw [h₁.eq]

/--
lemma `abs_mul_self` / 引理 `abs_mul_self`

English:
lemma abs_mul_self
  given: (a : A) (ha : IsStarNormal a := by cfc_tac)
  proof: by
  rw [Commute.cfcAbs_mul_eq (.refl a) ha.star_comm_self.symm]; rw [abs_mul_abs]

中文:
引理 abs_mul_self
  条件: (a : A) (ha : 是StarNormal a := by cfc_tac)
  证明: by
  rw [Commute.cfcAbs_mul_eq (.refl a) ha.star_comm_self.symm]; rw [abs_mul_abs]

Depends on / 依赖: Commute, Commute.cfcAbs_mul_eq, abs_mul_abs, cfcAbs_mul_eq, cfc_tac, ha.star_comm_self.symm, star_comm_self
-/
lemma abs_mul_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    abs (a * a) = star a * a := by
  rw [Commute.cfcAbs_mul_eq (.refl a) ha.star_comm_self.symm]; rw [abs_mul_abs]

/--
lemma `abs_nnrpow_two` / 引理 `abs_nnrpow_two`

English:
lemma abs_nnrpow_two
  given: (a : A)
  statement: abs a ^ (2 : Real>=0) = star a * a
  proof: by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs

中文:
引理 abs_nnrpow_two
  条件: (a : A)
  结论: abs a ^ (2 : 实数>=0) = star a * a
  证明: by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs

Depends on / 依赖: abs_mul_abs, abs_nonneg, nnrpow_two
-/
lemma abs_nnrpow_two (a : A) : abs a ^ (2 : Real>=0) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs

/--
lemma `abs_nnrpow_two_mul` / 引理 `abs_nnrpow_two_mul`

English:
lemma abs_nnrpow_two_mul
  given: (a : A) (x : Real>=0)
  proof: by rw [← nnrpow_nnrpow, abs_nnrpow_two]

中文:
引理 abs_nnrpow_two_mul
  条件: (a : A) (x : 实数>=0)
  证明: by rw [← nnrpow_nnrpow, abs_nnrpow_two]

Depends on / 依赖: abs_nnrpow_two, nnrpow_nnrpow
-/
lemma abs_nnrpow_two_mul (a : A) (x : Real>=0) :
    abs a ^ (2 * x) = (star a * a) ^ x := by rw [← nnrpow_nnrpow, abs_nnrpow_two]

/--
lemma `abs_nnrpow` / 引理 `abs_nnrpow`

English:
lemma abs_nnrpow
  given: (a : A) (x : Real>=0)
  proof: by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

@[grind =]

中文:
引理 abs_nnrpow
  条件: (a : A) (x : 实数>=0)
  证明: by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

@[grind =]

Depends on / 依赖: OfNat.ofNat_ne_zero, abs_nnrpow_two_mul, div_self, mul_div_left_comm, mul_one, ne_eq, not_false_eq_true, ofNat_ne_zero
-/
lemma abs_nnrpow (a : A) (x : Real>=0) :
    abs a ^ x = (star a * a) ^ (x / 2) := by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

@[grind =]
/--
lemma `abs_of_nonneg` / 引理 `abs_of_nonneg`

English:
lemma abs_of_nonneg
  given: (a : A) (ha : 0 <= a := by cfc_tac)
  statement: abs a = a
  proof: by
  rw [abs]; rw [ha.star_eq]; rw [sqrt_mul_self a ha]

中文:
引理 abs_of_nonneg
  条件: (a : A) (ha : 0 <= a := by cfc_tac)
  结论: abs a = a
  证明: by
  rw [abs]; rw [ha.star_eq]; rw [sqrt_mul_self a ha]

Depends on / 依赖: cfc_tac, generatingMonomorphisms, ha.star_eq, infer_instance, sqrt_mul_self, star_eq
-/
lemma abs_of_nonneg (a : A) (ha : 0 <= a := by cfc_tac) : abs a = a := by
  rw [abs]; rw [ha.star_eq]; rw [sqrt_mul_self a ha]

/--
lemma `abs_of_nonpos` / 引理 `abs_of_nonpos`

English:
lemma abs_of_nonpos
  given: (a : A) (ha : a <= 0 := by cfc_tac)
  statement: abs a = -a
  proof: by
  simpa using abs_of_nonneg (-a)

中文:
引理 abs_of_nonpos
  条件: (a : A) (ha : a <= 0 := by cfc_tac)
  结论: abs a = -a
  证明: by
  simpa using abs_of_nonneg (-a)

Depends on / 依赖: abs_of_nonneg, cfc_tac
-/
lemma abs_of_nonpos (a : A) (ha : a <= 0 := by cfc_tac) : abs a = -a := by
  simpa using abs_of_nonneg (-a)

/--
lemma `abs_eq_cfcₙ_norm` / 引理 `abs_eq_cfcₙ_norm`

English:
lemma abs_eq_cfcₙ_norm
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  conv_lhs =>
    rw [abs]; rw [ha.star_eq]; rw [sqrt_eq_real_sqrt ..]; rw [← cfcₙ_id' Real a]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]

中文:
引理 abs_eq_cfcₙ_norm
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  conv_lhs =>
    rw [abs]; rw [ha.star_eq]; rw [sqrt_eq_real_sqrt ..]; rw [← cfcₙ_id' Real a]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]

Depends on / 依赖: Real.sqrt_sq_eq_abs, cfc_tac, conv_lhs, ha.star_eq, sqrt_eq_real_sqrt, sqrt_sq_eq_abs, star_eq
-/
lemma abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfcₙ (‖·‖) a := by
  conv_lhs =>
    rw [abs]; rw [ha.star_eq]; rw [sqrt_eq_real_sqrt ..]; rw [← cfcₙ_id' Real a]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]

/--
lemma `posPart_add_negPart` / 引理 `posPart_add_negPart`

English:
lemma posPart_add_negPart
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  rw [CFC.posPart_def]; rw [CFC.negPart_def]; rw [← cfcₙ_add ..]; rw [abs_eq_cfcₙ_norm a ha]
  exact cfcₙ_congr fun x hx => posPart_add_negPart x

中文:
引理 posPart_add_negPart
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  rw [CFC.posPart_def]; rw [CFC.negPart_def]; rw [← cfcₙ_add ..]; rw [abs_eq_cfcₙ_norm a ha]
  exact cfcₙ_congr fun x hx => posPart_add_negPart x
-/
protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ + a⁻ = abs a := by
  rw [CFC.posPart_def]; rw [CFC.negPart_def]; rw [← cfcₙ_add ..]; rw [abs_eq_cfcₙ_norm a ha]
  exact cfcₙ_congr fun x hx => posPart_add_negPart x

/--
lemma `abs_sub_self` / 引理 `abs_sub_self`

English:
lemma abs_sub_self
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  statement: abs a - a = 2 • a⁻
  proof: by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) - $(CFC.posPart_sub_negPart a)).symm

中文:
引理 abs_sub_self
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  结论: abs a - a = 2 • a⁻
  证明: by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) - $(CFC.posPart_sub_negPart a)).symm

Depends on / 依赖: CFC.posPart_add_negPart, CFC.posPart_sub_negPart, cfc_tac, posPart_add_negPart, posPart_sub_negPart, two_smul
-/
lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a - a = 2 • a⁻ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) - $(CFC.posPart_sub_negPart a)).symm

/--
lemma `abs_add_self` / 引理 `abs_add_self`

English:
lemma abs_add_self
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  statement: abs a + a = 2 • a⁺
  proof: by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $(CFC.posPart_sub_negPart a)).symm

@[simp, grind =]

中文:
引理 abs_add_self
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  结论: abs a + a = 2 • a⁺
  证明: by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $(CFC.posPart_sub_negPart a)).symm

@[simp, grind =]

Depends on / 依赖: CFC.posPart_add_negPart, CFC.posPart_sub_negPart, cfc_tac, posPart_add_negPart, posPart_sub_negPart, two_smul
-/
lemma abs_add_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a + a = 2 • a⁺ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $(CFC.posPart_sub_negPart a)).symm

@[simp, grind =]
/--
lemma `cfcAbs_cfcAbs` / 引理 `cfcAbs_cfcAbs`

English:
lemma cfcAbs_cfcAbs
  given: (a : A)
  statement: abs (abs a) = abs a
  proof: abs_of_nonneg ..

中文:
引理 cfcAbs_cfcAbs
  条件: (a : A)
  结论: abs (abs a) = abs a
  证明: abs_of_nonneg ..

Depends on / 依赖: abs_of_nonneg
-/
lemma cfcAbs_cfcAbs (a : A) : abs (abs a) = abs a := abs_of_nonneg ..

variable [StarModule Real A]

@[simp, grind =]
/--
lemma `abs_smul_nonneg` / 引理 `abs_smul_nonneg`

English:
lemma abs_smul_nonneg
  statement: {R : Type*} [Semiring R] [SMulWithZero R Real>=0] [SMul R A]
  proof: by
  suffices forall r : Real>=0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs]; rw [sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) (abs_nonneg _))]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs]

中文:
引理 abs_smul_nonneg
  结论: {R : 类型} [半环 R] [带零标量乘法 R 实数>=0] [标量乘法 R A]
  证明: by
  suffices forall r : Real>=0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs]; rw [sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) (abs_nonneg _))]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs]

Depends on / 依赖: abs_mul_abs, abs_nonneg, mul_smul_comm, smul_mul_assoc, smul_nonneg, sqrt_eq_iff, star_mul_self_nonneg
-/
lemma abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZero R Real>=0] [SMul R A]
    [IsScalarTower R Real>=0 A] (r : R) (a : A) :
    abs (r • a) = r • abs a := by
  suffices forall r : Real>=0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs]; rw [sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) (abs_nonneg _))]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs]

end Real

section RCLike

variable {p : A -> Prop} [RCLike 𝕜]
  [NonUnitalRing A] [TopologicalSpace A] [Module 𝕜 A]
  [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]

open ComplexOrder

/--
lemma `_root_.cfcₙ_norm_sq_nonneg` / 引理 `_root_.cfcₙ_norm_sq_nonneg`

English:
lemma _root_.cfcₙ_norm_sq_nonneg
  given: (f : 𝕜 -> 𝕜) (a : A)
  statement: 0 <= cfcₙ (fun z => star (f z) * (f z)) a
  proof: cfcₙ_nonneg fun _ _ => star_mul_self_nonneg _

中文:
引理 _root_.cfcₙ_norm_sq_nonneg
  条件: (f : 𝕜 -> 𝕜) (a : A)
  结论: 0 <= cfcₙ (fun z => star (f z) * (f z)) a
  证明: cfcₙ_nonneg fun _ _ => star_mul_self_nonneg _

Depends on / 依赖: star_mul_self_nonneg
-/
lemma _root_.cfcₙ_norm_sq_nonneg (f : 𝕜 -> 𝕜) (a : A) : 0 <= cfcₙ (fun z => star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ => star_mul_self_nonneg _

/--
lemma `_root_.cfcₙ_norm_nonneg` / 引理 `_root_.cfcₙ_norm_nonneg`

English:
lemma _root_.cfcₙ_norm_nonneg
  given: (f : 𝕜 -> 𝕜) (a : A)
  statement: 0 <= cfcₙ (‖f ·‖ : 𝕜 -> 𝕜) a
  proof: cfcₙ_nonneg fun _ _ => by simp

中文:
引理 _root_.cfcₙ_norm_nonneg
  条件: (f : 𝕜 -> 𝕜) (a : A)
  结论: 0 <= cfcₙ (‖f ·‖ : 𝕜 -> 𝕜) a
  证明: cfcₙ_nonneg fun _ _ => by simp
-/
lemma _root_.cfcₙ_norm_nonneg (f : 𝕜 -> 𝕜) (a : A) : 0 <= cfcₙ (‖f ·‖ : 𝕜 -> 𝕜) a :=
  cfcₙ_nonneg fun _ _ => by simp

variable [Module Real A] [SMulCommClass Real A A] [IsScalarTower Real A A]
  [NonnegSpectrumClass Real A] [IsTopologicalRing A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule Real A] [IsScalarTower Real 𝕜 A] in
@[simp]
/--
lemma `abs_smul` / 引理 `abs_smul`

English:
lemma abs_smul
  given: (r : 𝕜) (a : A)
  statement: abs (r • a) = ‖r‖ • abs a
  proof: by
  trans abs (‖r‖ • a)
  · simp only [abs, mul_smul_comm, smul_mul_assoc, star_smul, ← smul_assoc,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · lift ‖r‖ to Real>=0 using norm_nonneg _ with r
    simp [← NNReal.smul_def]

中文:
引理 abs_smul
  条件: (r : 𝕜) (a : A)
  结论: abs (r • a) = ‖r‖ • abs a
  证明: by
  trans abs (‖r‖ • a)
  · simp only [abs, mul_smul_comm, smul_mul_assoc, star_smul, ← smul_assoc,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · lift ‖r‖ to Real>=0 using norm_nonneg _ with r
    simp [← NNReal.smul_def]

Depends on / 依赖: NNReal, NNReal.smul_def, RCLike, RCLike.conj_mul, RCLike.real_smul_eq_coe_smul, algebraMap_smul, conj_mul, mul_comm, mul_smul_comm, norm_nonneg, real_smul_eq_coe_smul, smul_assoc, smul_def, smul_mul_assoc, starRingEnd, star_smul
-/
lemma abs_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  trans abs (‖r‖ • a)
  · simp only [abs, mul_smul_comm, smul_mul_assoc, star_smul, ← smul_assoc,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · lift ‖r‖ to Real>=0 using norm_nonneg _ with r
    simp [← NNReal.smul_def]

variable (𝕜) in
/--
lemma `abs_eq_cfcₙ_coe_norm` / 引理 `abs_eq_cfcₙ_coe_norm`

English:
lemma abs_eq_cfcₙ_coe_norm
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [abs]; rw [sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _)]; rw [← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul, sq]

中文:
引理 abs_eq_cfcₙ_coe_norm
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [abs]; rw [sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _)]; rw [← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul, sq]

Depends on / 依赖: RCLike, RCLike.conj_mul, cfc_tac, conj_mul, conv_rhs, sqrt_eq_iff
-/
lemma abs_eq_cfcₙ_coe_norm (a : A) (ha : p a := by cfc_tac) :
    abs a = cfcₙ (fun z : 𝕜 => (‖z‖ : 𝕜)) a := by
  rw [abs]; rw [sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _)]; rw [← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul, sq]

/--
lemma `_root_.cfcₙ_comp_norm` / 引理 `_root_.cfcₙ_comp_norm`

English:
lemma _root_.cfcₙ_comp_norm
  statement: (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
  proof: by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (‖·‖) a, ← abs_eq_cfcₙ_coe_norm _ a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0,
      cfcₙ_apply_of_not_map_zero _ (fun h => (hf0 <| by simpa using h).elim)]

中文:
引理 _root_.cfcₙ_comp_norm
  结论: (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
  证明: by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (‖·‖) a, ← abs_eq_cfcₙ_coe_norm _ a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0,
      cfcₙ_apply_of_not_map_zero _ (fun h => (hf0 <| by simpa using h).elim)]

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_tac, quasispectrum
-/
lemma _root_.cfcₙ_comp_norm (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z => (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) := by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (‖·‖) a, ← abs_eq_cfcₙ_coe_norm _ a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0,
      cfcₙ_apply_of_not_map_zero _ (fun h => (hf0 <| by simpa using h).elim)]

/--
lemma `quasispectrum_abs` / 引理 `quasispectrum_abs`

English:
lemma quasispectrum_abs
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a ha]; rw [cfcₙ_map_quasispectrum ..]

中文:
引理 quasispectrum_abs
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a ha]; rw [cfcₙ_map_quasispectrum ..]

Depends on / 依赖: cfc_tac, quasispectrum
-/
lemma quasispectrum_abs (a : A) (ha : p a := by cfc_tac) :
    quasispectrum 𝕜 (abs a) = (fun z => (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a ha]; rw [cfcₙ_map_quasispectrum ..]

end RCLike

end NonUnital

section Unital

section Real

variable [Ring A] [StarRing A] [TopologicalSpace A] [Algebra Real A]
  [ContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
  [IsTopologicalRing A] [T2Space A]

/--
lemma `abs_eq_cfc_norm` / 引理 `abs_eq_cfc_norm`

English:
lemma abs_eq_cfc_norm
  given: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  proof: by
  rw [abs_eq_cfcₙ_norm _]; rw [cfcₙ_eq_cfc]

中文:
引理 abs_eq_cfc_norm
  条件: (a : A) (ha : IsSelfAdjoint a := by cfc_tac)
  证明: by
  rw [abs_eq_cfcₙ_norm _]; rw [cfcₙ_eq_cfc]

Depends on / 依赖: cfc_tac
-/
lemma abs_eq_cfc_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfc (‖·‖) a := by
  rw [abs_eq_cfcₙ_norm _]; rw [cfcₙ_eq_cfc]

/--
theorem `abs_coe_unitary` / 定理 `abs_coe_unitary`

English:
theorem abs_coe_unitary
  given: (U : unitary A)
  statement: abs (U : A) = 1
  proof: by simp [abs]

中文:
定理 abs_coe_unitary
  条件: (U : unitary A)
  结论: abs (U : A) = 1
  证明: by simp [abs]
-/
theorem abs_coe_unitary (U : unitary A) : abs (U : A) = 1 := by simp [abs]

/--
theorem `abs_of_mem_unitary` / 定理 `abs_of_mem_unitary`

English:
theorem abs_of_mem_unitary
  given: {U : A} (hU : U in unitary A)
  statement: abs U = 1
  proof: abs_coe_unitary ⟨U, hU⟩

中文:
定理 abs_of_mem_unitary
  条件: {U : A} (hU : U in unitary A)
  结论: abs U = 1
  证明: abs_coe_unitary ⟨U, hU⟩
-/
@[simp] theorem abs_of_mem_unitary {U : A} (hU : U in unitary A) : abs U = 1 :=
  abs_coe_unitary ⟨U, hU⟩

/--
lemma `abs_one` / 引理 `abs_one`

English:
lemma abs_one
  statement: abs (1 : A) = 1
  proof: by simp

中文:
引理 abs_one
  结论: abs (1 : A) = 1
  证明: by simp
-/
lemma abs_one : abs (1 : A) = 1 := by simp

variable [StarModule Real A]

@[simp]
/--
lemma `abs_algebraMap_nnreal` / 引理 `abs_algebraMap_nnreal`

English:
lemma abs_algebraMap_nnreal
  given: (x : Real>=0)
  statement: abs (algebraMap Real>=0 A x) = algebraMap Real>=0 A x
  proof: by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]

中文:
引理 abs_algebraMap_nnreal
  条件: (x : 实数>=0)
  结论: abs (algebraMap 实数>=0 A x) = algebraMap 实数>=0 A x
  证明: by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
lemma abs_algebraMap_nnreal (x : Real>=0) : abs (algebraMap Real>=0 A x) = algebraMap Real>=0 A x := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
/--
lemma `abs_natCast` / 引理 `abs_natCast`

English:
lemma abs_natCast
  given: (n : Nat)
  statement: abs (n : A) = n
  proof: by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_nnreal (n : Real>=0)

@[simp]

中文:
引理 abs_natCast
  条件: (n : 自然数)
  结论: abs (n : A) = n
  证明: by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_nnreal (n : Real>=0)

@[simp]

Depends on / 依赖: Nat.abs_cast, abs_algebraMap_nnreal, abs_cast, map_natCast
-/
lemma abs_natCast (n : Nat) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_nnreal (n : Real>=0)

@[simp]
/--
lemma `abs_ofNat` / 引理 `abs_ofNat`

English:
lemma abs_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: abs (ofNat(n) : A) = ofNat(n)
  proof: by
  simpa using! abs_natCast n

@[simp]

中文:
引理 abs_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: abs (of自然数(n) : A) = of自然数(n)
  证明: by
  simpa using! abs_natCast n

@[simp]

Depends on / 依赖: abs_natCast
-/
lemma abs_ofNat (n : Nat) [n.AtLeastTwo] : abs (ofNat(n) : A) = ofNat(n) := by
  simpa using! abs_natCast n

@[simp]
/--
lemma `abs_intCast` / 引理 `abs_intCast`

English:
lemma abs_intCast
  given: (n : Int)
  statement: abs (n : A) = |n|
  proof: by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc]; rw [abs_neg]; rw [abs_natCast]; rw [← Int.cast_natCast]
    congr

中文:
引理 abs_intCast
  条件: (n : 整数)
  结论: abs (n : A) = |n|
  证明: by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc]; rw [abs_neg]; rw [abs_natCast]; rw [← Int.cast_natCast]
    congr

Depends on / 依赖: Int.cast_natCast, Int.cast_negSucc, abs_natCast, abs_neg, cast_natCast, cast_negSucc, negSucc
-/
lemma abs_intCast (n : Int) : abs (n : A) = |n| := by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc]; rw [abs_neg]; rw [abs_natCast]; rw [← Int.cast_natCast]
    congr

end Real

section RCLike

variable {p : A -> Prop} [RCLike 𝕜]
  [Ring A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [Algebra Real A] [NonnegSpectrumClass Real A] [IsTopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus Real A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule Real A] [IsScalarTower Real 𝕜 A] in
@[simp]
/--
lemma `abs_algebraMap` / 引理 `abs_algebraMap`

English:
lemma abs_algebraMap
  given: (c : 𝕜)
  statement: abs (algebraMap 𝕜 A c) = algebraMap Real A ‖c‖
  proof: by
  simp [Algebra.algebraMap_eq_smul_one]

中文:
引理 abs_algebraMap
  条件: (c : 𝕜)
  结论: abs (algebraMap 𝕜 A c) = algebraMap 实数 A ‖c‖
  证明: by
  simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
lemma abs_algebraMap (c : 𝕜) : abs (algebraMap 𝕜 A c) = algebraMap Real A ‖c‖ := by
  simp [Algebra.algebraMap_eq_smul_one]

/--
lemma `_root_.cfc_comp_norm` / 引理 `_root_.cfc_comp_norm`

English:
lemma _root_.cfc_comp_norm
  statement: (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [← cfc_comp' ..]

中文:
引理 _root_.cfc_comp_norm
  结论: (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [← cfc_comp' ..]

Depends on / 依赖: ContinuousOn, cfc_comp, cfc_cont_tac, cfc_tac, monoMapFactorizationDataRlp, spectrum
-/
lemma _root_.cfc_comp_norm (f : 𝕜 -> 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z => (‖z‖ : 𝕜)) '' spectrum 𝕜 a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [← cfc_comp' ..]

/--
lemma `abs_sq` / 引理 `abs_sq`

English:
lemma abs_sq
  given: (a : A)
  statement: (abs a) ^ 2 = star a * a
  proof: by
  rw [sq]; rw [abs_mul_abs]

中文:
引理 abs_sq
  条件: (a : A)
  结论: (abs a) ^ 2 = star a * a
  证明: by
  rw [sq]; rw [abs_mul_abs]

Depends on / 依赖: abs_mul_abs, eq_of_tgt, fac.hp, fac.p, injective_iff_rlp_monomorphisms_zero, isZero_zero, monoMapFactorizationDataRlp
-/
lemma abs_sq (a : A) : (abs a) ^ 2 = star a * a := by
  rw [sq]; rw [abs_mul_abs]

/--
lemma `spectrum_abs` / 引理 `spectrum_abs`

English:
lemma spectrum_abs
  given: (a : A) (ha : p a := by cfc_tac)
  proof: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [cfc_map_spectrum ..]

中文:
引理 spectrum_abs
  条件: (a : A) (ha : p a := by cfc_tac)
  证明: by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [cfc_map_spectrum ..]

Depends on / 依赖: cfc_map_spectrum, cfc_tac, spectrum
-/
lemma spectrum_abs (a : A) (ha : p a := by cfc_tac) :
    spectrum 𝕜 (abs a) = (fun z => (‖z‖ : 𝕜)) '' spectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a]; rw [cfcₙ_eq_cfc]; rw [cfc_map_spectrum ..]

end RCLike

end Unital

section Isometric

variable [NonUnitalNormedRing A] [StarRing A] [ContinuousStar A]
  [NormedSpace Real A] [SMulCommClass Real A A] [IsScalarTower Real A A]
  [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] [CompleteSpace A]

/--
lemma `continuous_abs` / 引理 `continuous_abs`

English:
lemma continuous_abs
  statement: Continuous (CFC.abs : A -> A)
  proof: continuousOn_sqrt.comp_continuous (by fun_prop) (by cfc_tac)

中文:
引理 continuous_abs
  结论: 连续 (CFC.abs : A -> A)
  证明: continuousOn_sqrt.comp_continuous (by fun_prop) (by cfc_tac)
-/
protected lemma continuous_abs : Continuous (CFC.abs : A -> A) :=
  continuousOn_sqrt.comp_continuous (by fun_prop) (by cfc_tac)

end Isometric

section CStar

/- This section requires `A` to be a `CStarRing` -/

variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace Real A] [SMulCommClass Real A A] [IsScalarTower Real A A]
  [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]

open CFC

@[simp, grind =]
/--
lemma `abs_eq_zero_iff` / 引理 `abs_eq_zero_iff`

English:
lemma abs_eq_zero_iff
  given: {a : A}
  statement: abs a = 0 ↔ a = 0
  proof: by
  rw [CFC.abs]; rw [sqrt_eq_zero_iff _]; rw [CStarRing.star_mul_self_eq_zero_iff]

@[simp, grind =]

中文:
引理 abs_eq_zero_iff
  条件: {a : A}
  结论: abs a = 0 ↔ a = 0
  证明: by
  rw [CFC.abs]; rw [sqrt_eq_zero_iff _]; rw [CStarRing.star_mul_self_eq_zero_iff]

@[simp, grind =]

Depends on / 依赖: CFC.abs, CStarRing, CStarRing.star_mul_self_eq_zero_iff, infer_instance, sqrt_eq_zero_iff, star_mul_self_eq_zero_iff
-/
lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [CFC.abs]; rw [sqrt_eq_zero_iff _]; rw [CStarRing.star_mul_self_eq_zero_iff]

@[simp, grind =]
/--
lemma `norm_abs` / 引理 `norm_abs`

English:
lemma norm_abs
  given: {a : A}
  statement: ‖abs a‖ = ‖a‖
  proof: by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [(abs_nonneg _).star_eq]; rw [CFC.abs_mul_abs]; rw [CStarRing.norm_star_mul_self]

中文:
引理 norm_abs
  条件: {a : A}
  结论: ‖abs a‖ = ‖a‖
  证明: by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [(abs_nonneg _).star_eq]; rw [CFC.abs_mul_abs]; rw [CStarRing.norm_star_mul_self]

Depends on / 依赖: CFC.abs_mul_abs, CStarRing, CStarRing.norm_star_mul_self, abs_mul_abs, abs_nonneg, norm_nonneg, norm_star_mul_self, star_eq
-/
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [sq]; rw [sq]; rw [← CStarRing.norm_star_mul_self]; rw [(abs_nonneg _).star_eq]; rw [CFC.abs_mul_abs]; rw [CStarRing.norm_star_mul_self]

end CStar

end CFC
