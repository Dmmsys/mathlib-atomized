/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* `IsIntegral`: a predicate expressing that a given Weierstrass equation
  has integral coefficients.
* `IsMinimal`: a predicate expressing that a given Weierstrass equation
  has minimal valuation of discriminant among all isomorphic integral Weierstrass equations.
* `reduction`: the reduction of a Weierstrass curve given by a minimal Weierstrass equation,
  which is a Weierstrass curve over the residue field.
* `IsGoodReduction`: a predicate expressing that a given minimal Weierstrass equation
  has valuation of its discriminant equal to zero.

## Main statements

* `exists_isIntegral`: any Weierstrass curve is isomorphic to one given by
  an integral Weierstrass equation.
* `exists_isMinimal`: any Weierstrass curve is isomorphic to one given by
  a minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, reduction
-/

@[expose] public section

namespace WeierstrassCurve

section Integral

variable (R : Type*) [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

/-- A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the ring `R`. -/
@[mk_iff]
/--
Definition of `IsIntegral` / `IsIntegral` 的定义

English:
class IsIntegral
  parameters: (W : WeierstrassCurve K)
  axioms and operations (1):
    - integral : exists W_int : WeierstrassCurve R, W = W_int⁄K

中文:
类 是整
  参数: (W : WeierstrassCurve K)
  公理与运算 (1 个):
    - integral : 存在 W_int : WeierstrassCurve R, W = W_int⁄K
-/
class IsIntegral (W : WeierstrassCurve K) : Prop where
  integral : exists W_int : WeierstrassCurve R, W = W_int⁄K

/--
Definition of `integralModel` / `integralModel` 的定义

English:
definition integralModel
  signature: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  body: hW.integral.choose

中文:
定义 integralModel
  签名: (W : WeierstrassCurve K) [hW : 是整 R W]
  定义体: hW.integral.choose

Depends on / 依赖: hW.integral.choose, integral
-/
noncomputable def integralModel (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    WeierstrassCurve R :=
  hW.integral.choose

variable (W : WeierstrassCurve K) [hW : IsIntegral R W]

/--
lemma `baseChange_integralModel_eq` / 引理 `baseChange_integralModel_eq`

English:
lemma baseChange_integralModel_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: hW.integral.choose_spec.symm

中文:
引理 baseChange_integralModel_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: hW.integral.choose_spec.symm

Depends on / 依赖: choose_spec, hW.integral.choose_spec.symm, integral
-/
lemma baseChange_integralModel_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    (integralModel R W)⁄K = W :=
  hW.integral.choose_spec.symm

/--
lemma `isIntegral_of_exists_lift` / 引理 `isIntegral_of_exists_lift`

English:
lemma isIntegral_of_exists_lift
  statement: {W : WeierstrassCurve K}
  proof: by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm

中文:
引理 is整数egral_of_存在_lift
  结论: {W : WeierstrassCurve K}
  证明: by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm

Depends on / 依赖: all_goals, baseChange, choose_spec, choose_spec.symm
-/
lemma isIntegral_of_exists_lift {W : WeierstrassCurve K}
    (h₁ : exists r₁, (algebraMap R K) r₁ = W.a₁)
    (h₂ : exists r₂, (algebraMap R K) r₂ = W.a₂)
    (h₃ : exists r₃, (algebraMap R K) r₃ = W.a₃)
    (h₄ : exists r₄, (algebraMap R K) r₄ = W.a₄)
    (h₆ : exists r₆, (algebraMap R K) r₆ = W.a₆) :
    IsIntegral R W := by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm

/--
lemma `Δ_integral_of_isIntegral` / 引理 `Δ_integral_of_isIntegral`

English:
lemma Δ_integral_of_isIntegral
  given: (W : WeierstrassCurve K) [IsIntegral R W]
  proof: by
  obtain ⟨W_int, hW_int⟩ : exists W_int : WeierstrassCurve R, W = W_int⁄K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int]; rw [baseChange]; rw [map_Δ]

中文:
引理 Δ_integral_of_is整数egral
  条件: (W : WeierstrassCurve K) [是整 R W]
  证明: by
  obtain ⟨W_int, hW_int⟩ : exists W_int : WeierstrassCurve R, W = W_int⁄K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int]; rw [baseChange]; rw [map_Δ]

Depends on / 依赖: IsIntegral, IsIntegral.integral, W_int, WeierstrassCurve, baseChange, hW_int, integral
-/
lemma Δ_integral_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    exists r : R, algebraMap R K r = W.Δ := by
  obtain ⟨W_int, hW_int⟩ : exists W_int : WeierstrassCurve R, W = W_int⁄K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int]; rw [baseChange]; rw [map_Δ]

/--
lemma `integralModel_a₁_eq` / 引理 `integralModel_a₁_eq`

English:
lemma integralModel_a₁_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_a₁_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_a₁_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₁ = W.a₁ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_a₂_eq` / 引理 `integralModel_a₂_eq`

English:
lemma integralModel_a₂_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_a₂_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_a₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₂ = W.a₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_a₃_eq` / 引理 `integralModel_a₃_eq`

English:
lemma integralModel_a₃_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_a₃_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_a₃_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₃ = W.a₃ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_a₄_eq` / 引理 `integralModel_a₄_eq`

English:
lemma integralModel_a₄_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_a₄_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_a₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₄ = W.a₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_a₆_eq` / 引理 `integralModel_a₆_eq`

English:
lemma integralModel_a₆_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_a₆_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_a₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₆ = W.a₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_b₂_eq` / 引理 `integralModel_b₂_eq`

English:
lemma integralModel_b₂_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_b₂_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_b₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₂ = W.b₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_b₄_eq` / 引理 `integralModel_b₄_eq`

English:
lemma integralModel_b₄_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_b₄_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_b₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₄ = W.b₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_b₆_eq` / 引理 `integralModel_b₆_eq`

English:
lemma integralModel_b₆_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_b₆_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_b₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₆ = W.b₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_b₈_eq` / 引理 `integralModel_b₈_eq`

English:
lemma integralModel_b₈_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_b₈_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_b₈_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₈ = W.b₈ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_c₄_eq` / 引理 `integralModel_c₄_eq`

English:
lemma integralModel_c₄_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_c₄_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_c₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₄ = W.c₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_c₆_eq` / 引理 `integralModel_c₆_eq`

English:
lemma integralModel_c₆_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_c₆_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_c₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₆ = W.c₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/--
lemma `integralModel_Δ_eq` / 引理 `integralModel_Δ_eq`

English:
lemma integralModel_Δ_eq
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

中文:
引理 integralModel_Δ_eq
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

Depends on / 依赖: baseChange, baseChange_integralModel_eq, conv_rhs
-/
lemma integralModel_Δ_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).Δ = W.Δ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

variable [IsDomain R] [ValuationRing R] [IsFractionRing R K]

open ValuationRing

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_isIntegral` / 定理 `exists_isIntegral`

English:
theorem exists_isIntegral
  given: (W : WeierstrassCurve K)
  proof: by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a => valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax in l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : forall v in l, v <= lmax := fun v hv =>
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax <= 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals simpa [← mem_integer_iff, variableChange_def, Valuation.mem_integer_iff]
      using (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax >= 1 := le_of_not_ge hlmax_le_1
    have h : exists a : K, valuation R K a = lmax := by
      let i : Nat := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a != 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    use ⟨Units.mk0 a ha₀, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

中文:
定理 存在_is整数egral
  条件: (W : WeierstrassCurve K)
  证明: by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a => valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax in l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : forall v in l, v <= lmax := fun v hv =>
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax <= 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals simpa [← mem_integer_iff, variableChange_def, Valuation.mem_integer_iff]
      using (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax >= 1 := le_of_not_ge hlmax_le_1
    have h : exists a : K, valuation R K a = lmax := by
      let i : Nat := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a != 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    use ⟨Units.mk0 a ha₀, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

Depends on / 依赖: List.le_maximum_of_length_pos_of_mem, List.maximum_of_length_pos_mem, Valuation, Valuation.m, ValueGroup, all_goals, hlmax_le_1, hlmax_mem, isIntegral_of_exists_lift, l.maximum_of_length_pos, le_maximum_of_length_pos_of_mem, maximum_of_length_pos, maximum_of_length_pos_mem, mem_integer_iff, valuation, variableChange_def
-/
theorem exists_isIntegral (W : WeierstrassCurve K) :
    exists C : VariableChange K, IsIntegral R (C • W) := by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a => valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax in l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : forall v in l, v <= lmax := fun v hv =>
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax <= 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals simpa [← mem_integer_iff, variableChange_def, Valuation.mem_integer_iff]
      using (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax >= 1 := le_of_not_ge hlmax_le_1
    have h : exists a : K, valuation R K a = lmax := by
      let i : Nat := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a != 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    use ⟨Units.mk0 a ha₀, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

end Integral

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

open scoped Classical in
/--
Definition of `valuation_Δ_aux` / `valuation_Δ_aux` 的定义

English:
definition valuation_Δ_aux
  signature: (W : WeierstrassCurve K)
  body: if h : IsIntegral R W then
    ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  else ⟨⊥, bot_le⟩

中文:
定义 valuation_Δ_aux
  签名: (W : WeierstrassCurve K)
  定义体: if h : IsIntegral R W then
    ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  else ⟨⊥, bot_le⟩

Depends on / 依赖: IsIntegral, bot_le, maximalIdeal, valuation, valuation_le_one
-/
noncomputable def valuation_Δ_aux (W : WeierstrassCurve K) :
    { v : Intᵐ⁰ // v <= 1 } :=
  if h : IsIntegral R W then
    ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  else ⟨⊥, bot_le⟩

/--
lemma `valuation_Δ_aux_eq_of_isIntegral` / 引理 `valuation_Δ_aux_eq_of_isIntegral`

English:
lemma valuation_Δ_aux_eq_of_isIntegral
  given: (W : WeierstrassCurve K) [hW : IsIntegral R W]
  proof: by
  simp [valuation_Δ_aux, hW]

中文:
引理 valuation_Δ_aux_eq_of_is整数egral
  条件: (W : WeierstrassCurve K) [hW : 是整 R W]
  证明: by
  simp [valuation_Δ_aux, hW]
-/
lemma valuation_Δ_aux_eq_of_isIntegral (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    valuation_Δ_aux R W = valuation K (maximalIdeal R) W.Δ := by
  simp [valuation_Δ_aux, hW]

/-- A Weierstrass equation over the fraction field `K` is minimal if the (multiplicative) valuation
of its discriminant is maximal among all isomorphic integral Weierstrass equations.
We still use 'minimal' for the naming, so as to standardize the naming with Silverman's book. -/
@[mk_iff]
/--
Definition of `IsMinimal` / `IsMinimal` 的定义

English:
class IsMinimal
  parameters: (W : WeierstrassCurve K)
  axioms and operations (1):
    - val_Δ_maximal : MaximalFor (fun (C : VariableChange K) => IsIntegral R (C • W)) (fun (C : VariableChange K) => valuation_Δ_aux R (C • W)) (1 : VariableChange K)

中文:
类 是极小
  参数: (W : WeierstrassCurve K)
  公理与运算 (1 个):
    - val_Δ_maximal : MaximalFor (fun (C : VariableChange K) => 是整 R (C • W)) (fun (C : VariableChange K) => valuation_Δ_aux R (C • W)) (1 : VariableChange K)

Depends on / 依赖: KanComplex, KanComplex.hornFilling, hornFilling
-/
class IsMinimal (W : WeierstrassCurve K) : Prop where
  val_Δ_maximal :
    MaximalFor
      (fun (C : VariableChange K) => IsIntegral R (C • W))
      (fun (C : VariableChange K) => valuation_Δ_aux R (C • W))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
instance {W : WeierstrassCurve K} [IsMinimal R W] :
    IsIntegral R W := by simpa using IsMinimal.val_Δ_maximal.1

/--
theorem `exists_isMinimal` / 定理 `exists_isMinimal`

English:
theorem exists_isMinimal
  given: (W : WeierstrassCurve K)
  proof: by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) => IsIntegral R (C • W))
    (fun (C : VariableChange K) => valuation_Δ_aux R (C • W))
    (exists_isIntegral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

中文:
定理 存在_isMinimal
  条件: (W : WeierstrassCurve K)
  证明: by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) => IsIntegral R (C • W))
    (fun (C : VariableChange K) => valuation_Δ_aux R (C • W))
    (exists_isIntegral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

Depends on / 依赖: IsIntegral, VariableChange, exists_isIntegral, exists_maximalFor_of_wellFoundedGT, one_smul, smul_assoc
-/
theorem exists_isMinimal (W : WeierstrassCurve K) :
    exists C : VariableChange K, IsMinimal R (C • W) := by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) => IsIntegral R (C • W))
    (fun (C : VariableChange K) => valuation_Δ_aux R (C • W))
    (exists_isIntegral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

/--
Definition of `minimal` / `minimal` 的定义

English:
definition minimal
  signature: (W : WeierstrassCurve K)
  body: (W.exists_isMinimal R).choose • W

中文:
定义 minimal
  签名: (W : WeierstrassCurve K)
  定义体: (W.exists_isMinimal R).choose • W

Depends on / 依赖: W.exists_isMinimal, exists_isMinimal
-/
noncomputable def minimal (W : WeierstrassCurve K) : WeierstrassCurve K :=
  (W.exists_isMinimal R).choose • W

instance {W : WeierstrassCurve K} :
    IsMinimal R (W.minimal R) := (W.exists_isMinimal R).choose_spec

end Minimal

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

/--
Definition of `reduction` / `reduction` 的定义

English:
definition reduction
  signature: (W : WeierstrassCurve K) [IsMinimal R W]
  body: (integralModel R W).map (residue R)

中文:
定义 reduction
  签名: (W : WeierstrassCurve K) [是极小 R W]
  定义体: (integralModel R W).map (residue R)

Depends on / 依赖: integralModel, residue
-/
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    WeierstrassCurve (ResidueField R) :=
  (integralModel R W).map (residue R)

/-- A minimal Weierstrass equation has good reduction if and only if
the valuation of its discriminant is 1. -/
@[mk_iff]
/--
Definition of `HasGoodReduction` / `HasGoodReduction` 的定义

English:
class HasGoodReduction
  parameters: (W : WeierstrassCurve K)
  extends: IsMinimal R W
  axioms and operations (1):
    - goodReduction : valuation K (maximalIdeal R) W.Δ = 1

中文:
类 有GoodReduction
  参数: (W : WeierstrassCurve K)
  继承: 是极小 R W
  公理与运算 (1 个):
    - goodReduction : valuation K (maximalIdeal R) W.Δ = 1
-/
class HasGoodReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  goodReduction : valuation K (maximalIdeal R) W.Δ = 1

@[deprecated (since := "2026-03-04")] alias IsGoodReduction := HasGoodReduction

/--
lemma `hasGoodReduction_iff_isElliptic_reduction` / 引理 `hasGoodReduction_iff_isElliptic_reduction`

English:
lemma hasGoodReduction_iff_isElliptic_reduction
  given: {W : WeierstrassCurve K} [hW : IsMinimal R W]
  proof: by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
  have h :
      ¬(valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) < 1)
      ↔ (integralModel R W).Δ ∉ IsLocalRing.maximalIdeal R :=
not_iff_not.mpr valuation_lt_one_iff_mem _ _
  refine ((integralModel_Δ_eq R W ▸ hasGoodReduction_iff _ _).trans ?_).trans h
  simpa [hW] using (valuation_le_one (R := R) (K := K) _ _).ge_iff_eq.symm

@[deprecated (since := "2026-03-04")] alias isGoodReduction_iff_isElliptic_reduction :=
  hasGoodReduction_iff_isElliptic_reduction

中文:
引理 hasGoodReduction_iff_isElliptic_reduction
  条件: {W : WeierstrassCurve K} [hW : 是极小 R W]
  证明: by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
  have h :
      ¬(valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) < 1)
      ↔ (integralModel R W).Δ ∉ IsLocalRing.maximalIdeal R :=
not_iff_not.mpr valuation_lt_one_iff_mem _ _
  refine ((integralModel_Δ_eq R W ▸ hasGoodReduction_iff _ _).trans ?_).trans h
  simpa [hW] using (valuation_le_one (R := R) (K := K) _ _).ge_iff_eq.symm

@[deprecated (since := "2026-03-04")] alias isGoodReduction_iff_isElliptic_reduction :=
  hasGoodReduction_iff_isElliptic_reduction

Depends on / 依赖: Iff.trans, IsLocalRing, IsLocalRing.maximalIdeal, W.reduction, algebraMap, ge_iff_eq, ge_iff_eq.symm, hasGoodReduction_iff, integralModel, isElliptic_iff, isElliptic_iff.symm, isUnit_iff_ne_zero, maximalIdeal, ne_eq, not_iff_not, not_iff_not.mpr, reduction, residue_eq_zero_iff, valuation, valuation_le_one
-/
lemma hasGoodReduction_iff_isElliptic_reduction {W : WeierstrassCurve K} [hW : IsMinimal R W] :
    HasGoodReduction R W ↔ (W.reduction R).IsElliptic := by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
  have h :
      ¬(valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) < 1)
      ↔ (integralModel R W).Δ ∉ IsLocalRing.maximalIdeal R :=
not_iff_not.mpr valuation_lt_one_iff_mem _ _
  refine ((integralModel_Δ_eq R W ▸ hasGoodReduction_iff _ _).trans ?_).trans h
  simpa [hW] using (valuation_le_one (R := R) (K := K) _ _).ge_iff_eq.symm

@[deprecated (since := "2026-03-04")] alias isGoodReduction_iff_isElliptic_reduction :=
  hasGoodReduction_iff_isElliptic_reduction

/-- A minimal Weierstrass equation has multiplicative reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` equals 1. -/
@[mk_iff]
/--
Definition of `HasMultiplicativeReduction` / `HasMultiplicativeReduction` 的定义

English:
class HasMultiplicativeReduction
  parameters: (W : WeierstrassCurve K)
  extends: IsMinimal R W
  axioms and operations (2):
    - badReduction : valuation K (maximalIdeal R) W.Δ < 1
    - multiplicativeReduction : valuation K (maximalIdeal R) W.c₄ = 1

中文:
类 有MultiplicativeReduction
  参数: (W : WeierstrassCurve K)
  继承: 是极小 R W
  公理与运算 (2 个):
    - badReduction : valuation K (maximalIdeal R) W.Δ < 1
    - multiplicativeReduction : valuation K (maximalIdeal R) W.c₄ = 1
-/
class HasMultiplicativeReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  multiplicativeReduction : valuation K (maximalIdeal R) W.c₄ = 1

/-- A minimal Weierstrass equation has additive reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` is less than 1. -/
@[mk_iff]
/--
Definition of `HasAdditiveReduction` / `HasAdditiveReduction` 的定义

English:
class HasAdditiveReduction
  parameters: (W : WeierstrassCurve K)
  extends: IsMinimal R W
  axioms and operations (2):
    - badReduction : valuation K (maximalIdeal R) W.Δ < 1
    - additiveReduction : valuation K (maximalIdeal R) W.c₄ < 1

中文:
类 有加法itiveReduction
  参数: (W : WeierstrassCurve K)
  继承: 是极小 R W
  公理与运算 (2 个):
    - badReduction : valuation K (maximalIdeal R) W.Δ < 1
    - additiveReduction : valuation K (maximalIdeal R) W.c₄ < 1
-/
class HasAdditiveReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  additiveReduction : valuation K (maximalIdeal R) W.c₄ < 1

-- TODO: add characterization in terms of the discriminant when the characteristic is not 2
open Polynomial in
/-- A minimal Weierstrass equation has split multiplicative reduction if and only if
the polynomial `c₄ T ^ 2 + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` splits in the residue field.

To see how this expression arises, note that the node `(x₀, y₀)` has second order Taylor expansion
`(Y - y₀)^2 + a_1(X - x₀)(Y - y₀) - (3x₀ + a_2)(X - x₀)^2` where `x₀ = (18 b₆ - b₂ b₄) / c₄`. -/
@[mk_iff]
/--
Definition of `HasSplitMultiplicativeReduction` / `HasSplitMultiplicativeReduction` 的定义

English:
class HasSplitMultiplicativeReduction
  parameters: (W : WeierstrassCurve K)
  extends: W.HasMultiplicativeReduction R
  axioms and operations (1):
    - splitMultiplicativeReduction : letI I  [default: W.integralModel R]

中文:
类 有SplitMultiplicativeReduction
  参数: (W : WeierstrassCurve K)
  继承: W.有MultiplicativeReduction R
  公理与运算 (1 个):
    - splitMultiplicativeReduction : letI I  [默认: W.integralModel R]

Depends on / 依赖: W.integralModel, integralModel
-/
class HasSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop
    extends W.HasMultiplicativeReduction R where
  splitMultiplicativeReduction : letI I := W.integralModel R
Splits .map (algebraMap R (ResidueField R))
      C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X - C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)

variable {W : WeierstrassCurve K}

/--
theorem `hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction` / 定理 `hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction`

English:
theorem hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
  given: [IsMinimal R W]
  proof: by
  rw [hasGoodReduction_iff]; rw [hasMultiplicativeReduction_iff]; rw [hasAdditiveReduction_iff]; rw [← integralModel_Δ_eq R W]; rw [← integralModel_c₄_eq R W]
  grind [valuation_le_one]

中文:
定理 hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
  条件: [是极小 R W]
  证明: by
  rw [hasGoodReduction_iff]; rw [hasMultiplicativeReduction_iff]; rw [hasAdditiveReduction_iff]; rw [← integralModel_Δ_eq R W]; rw [← integralModel_c₄_eq R W]
  grind [valuation_le_one]

Depends on / 依赖: hasAdditiveReduction_iff, hasGoodReduction_iff, hasMultiplicativeReduction_iff, valuation_le_one
-/
theorem hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction [IsMinimal R W] :
    W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R ∨ W.HasAdditiveReduction R := by
  rw [hasGoodReduction_iff]; rw [hasMultiplicativeReduction_iff]; rw [hasAdditiveReduction_iff]; rw [← integralModel_Δ_eq R W]; rw [← integralModel_c₄_eq R W]
  grind [valuation_le_one]

/--
theorem `HasGoodReduction.not_hasMultiplicativeReduction` / 定理 `HasGoodReduction.not_hasMultiplicativeReduction`

English:
theorem HasGoodReduction.not_hasMultiplicativeReduction
  given: (hW : W.HasGoodReduction R)
  proof: fun h => h.badReduction.ne hW.goodReduction

中文:
定理 有GoodReduction.not_hasMultiplicativeReduction
  条件: (hW : W.有GoodReduction R)
  证明: fun h => h.badReduction.ne hW.goodReduction

Depends on / 依赖: badReduction, goodReduction, h.badReduction.ne, hW.goodReduction
-/
theorem HasGoodReduction.not_hasMultiplicativeReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h => h.badReduction.ne hW.goodReduction

/--
theorem `HasGoodReduction.not_hasAdditiveReduction` / 定理 `HasGoodReduction.not_hasAdditiveReduction`

English:
theorem HasGoodReduction.not_hasAdditiveReduction
  given: (hW : W.HasGoodReduction R)
  proof: fun h => h.badReduction.ne hW.goodReduction

中文:
定理 有GoodReduction.not_hasAdditiveReduction
  条件: (hW : W.有GoodReduction R)
  证明: fun h => h.badReduction.ne hW.goodReduction

Depends on / 依赖: badReduction, goodReduction, h.badReduction.ne, hW.goodReduction
-/
theorem HasGoodReduction.not_hasAdditiveReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h => h.badReduction.ne hW.goodReduction

/--
theorem `HasMultiplicativeReduction.not_hasGoodReduction` / 定理 `HasMultiplicativeReduction.not_hasGoodReduction`

English:
theorem HasMultiplicativeReduction.not_hasGoodReduction
  given: (hW : W.HasMultiplicativeReduction R)
  proof: fun h => hW.badReduction.ne h.goodReduction

中文:
定理 有MultiplicativeReduction.not_hasGoodReduction
  条件: (hW : W.有MultiplicativeReduction R)
  证明: fun h => hW.badReduction.ne h.goodReduction

Depends on / 依赖: badReduction, goodReduction, h.goodReduction, hW.badReduction.ne
-/
theorem HasMultiplicativeReduction.not_hasGoodReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h => hW.badReduction.ne h.goodReduction

/--
theorem `HasAdditiveReduction.not_hasGoodReduction` / 定理 `HasAdditiveReduction.not_hasGoodReduction`

English:
theorem HasAdditiveReduction.not_hasGoodReduction
  given: (hW : W.HasAdditiveReduction R)
  proof: fun h => hW.badReduction.ne h.goodReduction

中文:
定理 有加法itiveReduction.not_hasGoodReduction
  条件: (hW : W.有加法itiveReduction R)
  证明: fun h => hW.badReduction.ne h.goodReduction

Depends on / 依赖: badReduction, goodReduction, h.goodReduction, hW.badReduction.ne
-/
theorem HasAdditiveReduction.not_hasGoodReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h => hW.badReduction.ne h.goodReduction

/--
theorem `HasMultiplicativeReduction.not_hasAdditiveReduction` / 定理 `HasMultiplicativeReduction.not_hasAdditiveReduction`

English:
theorem HasMultiplicativeReduction.not_hasAdditiveReduction
  given: (hW : W.HasMultiplicativeReduction R)
  proof: fun h => h.additiveReduction.ne hW.multiplicativeReduction

中文:
定理 有MultiplicativeReduction.not_hasAdditiveReduction
  条件: (hW : W.有MultiplicativeReduction R)
  证明: fun h => h.additiveReduction.ne hW.multiplicativeReduction

Depends on / 依赖: additiveReduction, h.additiveReduction.ne, hW.multiplicativeReduction, multiplicativeReduction, quasicategory_iff_innerFibration
-/
theorem HasMultiplicativeReduction.not_hasAdditiveReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h => h.additiveReduction.ne hW.multiplicativeReduction

/--
theorem `HasAdditiveReduction.not_hasMultiplicativeReduction` / 定理 `HasAdditiveReduction.not_hasMultiplicativeReduction`

English:
theorem HasAdditiveReduction.not_hasMultiplicativeReduction
  given: (hW : W.HasAdditiveReduction R)
  proof: fun h => hW.additiveReduction.ne h.multiplicativeReduction

中文:
定理 有加法itiveReduction.not_hasMultiplicativeReduction
  条件: (hW : W.有加法itiveReduction R)
  证明: fun h => hW.additiveReduction.ne h.multiplicativeReduction

Depends on / 依赖: additiveReduction, h.multiplicativeReduction, hW.additiveReduction.ne, multiplicativeReduction
-/
theorem HasAdditiveReduction.not_hasMultiplicativeReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h => hW.additiveReduction.ne h.multiplicativeReduction

end Reduction

end WeierstrassCurve
