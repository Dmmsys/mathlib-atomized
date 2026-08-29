/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Notation

/-!
# Holomorphicity of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are holomorphic on the upper half plane, which is stated as being
MDifferentiable.
-/

public section

noncomputable section

open UpperHalfPlane Filter Function Complex Manifold CongruenceSubgroup

namespace EisensteinSeries

/--
lemma `div_linear_zpow_differentiableOn` / 引理 `div_linear_zpow_differentiableOn`

English:
lemma div_linear_zpow_differentiableOn
  given: (k : Int) (a : Fin 2 -> Int)
  proof: by
  rcases ne_or_eq a 0 with ha | rfl
  · apply DifferentiableOn.zpow
    · fun_prop
    · left
      exact fun z hz => linear_ne_zero ⟨z, hz⟩
        ((comp_ne_zero_iff _ Int.cast_injective Int.cast_zero).mpr ha)
  · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero]
    apply differenti

中文:
引理 div_linear_zpow_differentiableOn
  条件: (k : 整数) (a : 有限集 2 -> 整数)
  证明: by
  rcases ne_or_eq a 0 with ha | rfl
  · apply DifferentiableOn.zpow
    · fun_prop
    · left
      exact fun z hz => linear_ne_zero ⟨z, hz⟩
        ((comp_ne_zero_iff _ Int.cast_injective Int.cast_zero).mpr ha)
  · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero]
    apply differenti

Depends on / 依赖: DifferentiableOn, DifferentiableOn.zpow, Int.cast_injective, Int.cast_zero, Pi.zero_apply, add_zero, cast_injective, cast_zero, comp_ne_zero_iff, differentiableOn_const, fun_prop, linear_ne_zero, ne_or_eq, zero_apply, zero_mul
-/
lemma div_linear_zpow_differentiableOn (k : Int) (a : Fin 2 -> Int) :
    DifferentiableOn Complex (fun z : Complex => (a 0 * z + a 1) ^ (-k)) {z : Complex | 0 < z.im} := by
  rcases ne_or_eq a 0 with ha | rfl
  · apply DifferentiableOn.zpow
    · fun_prop
    · left
      exact fun z hz => linear_ne_zero ⟨z, hz⟩
        ((comp_ne_zero_iff _ Int.cast_injective Int.cast_zero).mpr ha)
  · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero]
    apply differentiableOn_const

/--
lemma `eisSummand_extension_differentiableOn` / 引理 `eisSummand_extension_differentiableOn`

English:
lemma eisSummand_extension_differentiableOn
  given: (k : Int) (a : Fin 2 -> Int)
  proof: by
  apply DifferentiableOn.congr (div_linear_zpow_differentiableOn k a)
  intro z hz
  lift z to ℍ using hz
  apply comp_ofComplex

中文:
引理 eisSummand_extension_differentiableOn
  条件: (k : 整数) (a : 有限集 2 -> 整数)
  证明: by
  apply DifferentiableOn.congr (div_linear_zpow_differentiableOn k a)
  intro z hz
  lift z to ℍ using hz
  apply comp_ofComplex

Depends on / 依赖: DifferentiableOn, DifferentiableOn.congr, comp_ofComplex, div_linear_zpow_differentiableOn
-/
lemma eisSummand_extension_differentiableOn (k : Int) (a : Fin 2 -> Int) :
    DifferentiableOn Complex (↑ₕeisSummand k a) {z : Complex | 0 < z.im} := by
  apply DifferentiableOn.congr (div_linear_zpow_differentiableOn k a)
  intro z hz
  lift z to ℍ using hz
  apply comp_ofComplex

/--
theorem `eisensteinSeriesSIF_mdifferentiable` / 定理 `eisensteinSeriesSIF_mdifferentiable`

English:
theorem eisensteinSeriesSIF_mdifferentiable
  given: {k : Int} {N : Nat} (hk : 3 <= k) (a : Fin 2 -> ZMod N)
  proof: by
  intro τ
  suffices DifferentiableAt Complex (↑ₕeisensteinSeriesSIF a k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z => (comp_ofComplex (eisensteinSeriesSIF a k) z).symm
  refine DifferentiableOn.differ

中文:
定理 eisensteinSeriesSIF_mdifferentiable
  条件: {k : 整数} {N : 自然数} (hk : 3 <= k) (a : 有限集 2 -> ZMod N)
  证明: by
  intro τ
  suffices DifferentiableAt Complex (↑ₕeisensteinSeriesSIF a k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z => (comp_ofComplex (eisensteinSeriesSIF a k) z).symm
  refine DifferentiableOn.differ

Depends on / 依赖: DifferentiableAt, DifferentiableAt.mdifferentiableAt, DifferentiableOn, DifferentiableOn.differentiableAt, DifferentiableOn.fun_sum, Eventually, Eventually.of_forall, MDifferentiableAt, MDifferentiableAt.comp, comp_ofComplex, convert, differentiableAt, differentiableOn, eisSummand_extension_diffe, eisensteinSeriesSIF, eisensteinSeries_tendstoLocallyUniformlyOn, fun_sum, isOpen_upperHalfPlaneSet, isOpen_upperHalfPlaneSet.mem_nhds, mdifferentiableAt
-/
theorem eisensteinSeriesSIF_mdifferentiable {k : Int} {N : Nat} (hk : 3 <= k) (a : Fin 2 -> ZMod N) :
    MDiff (eisensteinSeriesSIF a k) := by
  intro τ
  suffices DifferentiableAt Complex (↑ₕeisensteinSeriesSIF a k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z => (comp_ofComplex (eisensteinSeriesSIF a k) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (eisensteinSeries_tendstoLocallyUniformlyOn hk a).differentiableOn
    (Eventually.of_forall fun s => DifferentiableOn.fun_sum
    fun _ _ => eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

@[deprecated (since := "2026-02-09")]
alias eisensteinSeries_SIF_MDifferentiable := eisensteinSeriesSIF_mdifferentiable

end EisensteinSeries
