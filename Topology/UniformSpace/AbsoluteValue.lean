/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.UniformSpace.OfFun

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

@[expose] public section

open Set Function Filter Uniformity

namespace AbsoluteValue

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {R : Type*} [CommRing R] (abv : AbsoluteValue R 𝕜)

/-- The uniform structure coming from an absolute value. -/
@[instance_reducible]
/--
Definition of `uniformSpace` / `uniformSpace` 的定义

English:
definition uniformSpace
  signature: : UniformSpace R
  body: .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun _ _ _ => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

中文:
定义 uniformSpace
  签名: : UniformSpace R
  定义体: .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun _ _ _ => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

Depends on / 依赖: abv.map_sub, abv.sub_le, add_comm, add_halves, add_lt_add, half_pos, map_sub, sub_le, trans_eq
-/
def uniformSpace : UniformSpace R :=
  .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun _ _ _ => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩

/--
theorem `hasBasis_uniformity` / 定理 `hasBasis_uniformity`

English:
theorem hasBasis_uniformity
  proof: UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

中文:
定理 hasBasis_uniformity
  证明: UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

Depends on / 依赖: UniformSpace, UniformSpace.hasBasis_ofFun, exists_gt, hasBasis_ofFun
-/
theorem hasBasis_uniformity :
    𝓤[abv.uniformSpace].HasBasis ((0 : 𝕜) < ·) fun ε => { p : R × R | abv (p.2 - p.1) < ε } :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

end AbsoluteValue
