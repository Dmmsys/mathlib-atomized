/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Emily Riehl, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Strict Segal simplicial sets are quasicategories

In `AlgebraicTopology.SimplicialSet.StrictSegal`, we define the strict Segal
condition on a simplicial set `X`. We say that `X` is strict Segal if its
simplices are uniquely determined by their spine.

In this file, we prove that any simplicial set satisfying the strict Segal
condition is a quasicategory.
-/

public section

universe u

open CategoryTheory
open Simplicial SimplicialObject SimplexCategory

namespace SSet.StrictSegal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `quasicategory` / 定理 `quasicategory`

English:
theorem quasicategory
  given: {X : SSet.{u}} (sx : StrictSegal X)
  statement: Quasicategory X
  proof: by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
use sx.spineToSimplex Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _)]; rw [← σ₀.natu

中文:
定理 quasicategory
  条件: {X : SSet.{u}} (sx : StrictSegal X)
  结论: 拟范畴 X
  证明: by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
use sx.spineToSimplex Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _)]; rw [← σ₀.natu

Depends on / 依赖: Equiv.coe_fn_mk, Fin.coe_eq_castSucc, Function, Function.comp_apply, Path.map, Path.map_arrow, X.map, castSucc, coe_eq_castSucc, coe_fn_mk, comp_apply, horn.spineId, k.succ.castSucc, map_arrow, naturality, quasicategory_of_filler, spineEquiv, spineId, spineInjective, spineToSimplex
-/
theorem quasicategory {X : SSet.{u}} (sx : StrictSegal X) : Quasicategory X := by
  apply quasicategory_of_filler X
  intro n i σ₀ h₀ hₙ
use sx.spineToSimplex Path.map (horn.spineId i h₀ hₙ) σ₀
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (σ₀.app _) (X.map _)]; rw [← σ₀.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by lia
  · rw [← spine_arrow, spine_δ_arrow_lt sx _ hlt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe]; rw [Subfunctor.lift_ι]; rw [stdSimplex.map_apply]; rw [Quiver.Hom.unop_op]; rw [SSet.yonedaEquiv_map]; rw [Equiv.apply_symm_apply]; rw [mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, spine_δ_arrow_gt sx _ hgt]
    dsimp
    apply congr_arg
    apply Subtype.ext
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe]; rw [Subfunctor.lift_ι]; rw [stdSimplex.map_apply]; rw [Quiver.Hom.unop_op]; rw [SSet.yonedaEquiv_map]; rw [Equiv.apply_symm_apply]; rw [mkOfSucc_δ_gt hgt]
    rfl
  · obtain _ | n := n
    · /- The only inner horn of `Δ[2]` does not contain the diagonal edge. -/
      obtain rfl : k = 0 := by omega
      fin_cases i <;> contradiction
    · /- We construct the triangle in the standard simplex as a 2-simplex in
      the horn. While the triangle is not contained in the inner horn `Λ[2, 1]`,
      it suffices to inhabit `Λ[n + 3, i] _⦋2⦌`. -/
      let triangle : (Λ[n + 3, i] : SSet.{u}) _⦋2⦌ :=
        horn.primitiveTriangle i h₀ hₙ k (by grind)
      /- The interval spanning from `k` to `k + 2` is equivalently the spine
      of the triangle with vertices `k`, `k + 1`, and `k + 2`. -/
      have hi : ((horn.spineId i h₀ hₙ).map σ₀).interval k 2 (by grind) =
          X.spine 2 (σ₀.app _ triangle) := by
        ext m
        dsimp [spine_arrow, Path.map_interval, Path.map_arrow]
        rw [← dsimp% σ₀.naturality_apply]
        apply congr_arg
        apply Subtype.ext
        ext a : 1
        fin_cases a <;> fin_cases m <;> rfl
      rw [← spine_arrow]; rw [spine_δ_arrow_eq sx _ heq]; rw [hi]
      simp only [spineToDiagonal, diagonal, spineToSimplex_spine_apply]
      rw [← types_comp_apply (σ₀.app _) (X.map _)]; rw [← σ₀.naturality]; rw [types_comp_apply]
      dsimp
      apply congr_arg
      apply Subtype.ext
      ext z : 1
      dsimp [horn.face]
      rw [dsimp% Subcomplex.yonedaEquiv_coe]; rw [Subfunctor.lift_ι]; rw [stdSimplex.map_apply]; rw [Quiver.Hom.unop_op]; rw [stdSimplex.map_apply]; rw [Quiver.Hom.unop_op]
      dsimp [CosimplicialObject.δ]
      rw [SSet.yonedaEquiv_map]
      simp only [Equiv.apply_symm_apply, triangle]
      rw [mkOfSucc_δ_eq heq]
      fin_cases z <;> rfl

/--
Instance `quasicategory'` / 实例 `quasicategory'`

English:
instance quasicategory'
  signature: (X : SSet.{u}) [IsStrictSegal X]
  body: quasicategory ofIsStrictSegal X

中文:
实例 quasicategory'
  签名: (X : SSet.{u}) [是StrictSegal X]
  定义体: quasicategory ofIsStrictSegal X

Depends on / 依赖: ofIsStrictSegal, quasicategory
-/
instance quasicategory' (X : SSet.{u}) [IsStrictSegal X] : Quasicategory X :=
quasicategory ofIsStrictSegal X

end SSet.StrictSegal
