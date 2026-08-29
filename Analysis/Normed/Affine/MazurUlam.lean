/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Mazur-Ulam Theorem

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `IsometryEquiv.toRealLinearIsometryEquivOfMapZero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `toFun` and `invFun`;
* `IsometryEquiv.toRealLinearIsometryEquiv` : given `f : E ≃ᵢ F`, returns a linear isometry
  equivalence `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `IsometryEquiv.toRealAffineIsometryEquiv` : given `f : PE ≃ᵢ PF`, returns an affine isometry
  equivalence `g : PE ≃ᵃⁱ[ℝ] PF` whose underlying `IsometryEquiv` is `f`

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/

@[expose] public section


variable {E PE F PF : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MetricSpace PE]
  [NormedAddTorsor E PE] [NormedAddCommGroup F] [NormedSpace Real F] [MetricSpace PF]
  [NormedAddTorsor F PF]

open Set AffineMap AffineIsometryEquiv

noncomputable section

namespace IsometryEquiv

/--
theorem `midpoint_fixed` / 定理 `midpoint_fixed`

English:
theorem midpoint_fixed
  given: {x y : PE}
  proof: by
  set z := midpoint Real x y
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y }
  have : Nonempty s := ⟨⟨IsometryEquiv.refl PE, rfl, rfl⟩⟩
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd :

中文:
定理 midpoint_fixed
  条件: {x y : PE}
  证明: by
  set z := midpoint Real x y
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y }
  have : Nonempty s := ⟨⟨IsometryEquiv.refl PE, rfl, rfl⟩⟩
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd :

Depends on / 依赖: midpoint
-/
theorem midpoint_fixed {x y : PE} :
    forall e : PE ≃ᵢ PE, e x = x -> e y = y -> e (midpoint Real x y) = midpoint Real x y := by
  set z := midpoint Real x y
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y }
  have : Nonempty s := ⟨⟨IsometryEquiv.refl PE, rfl, rfl⟩⟩
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd : BddAbove (range fun e : s => dist ((e : PE ≃ᵢ PE) z) z) := by
refine ⟨dist x z + dist x z, forall_mem_range.2 Subtype.forall.2 ?_⟩
    rintro e ⟨hx, _⟩
    calc
      dist (e z) z <= dist (e z) x + dist x z := dist_triangle (e z) x z
      _ = dist (e x) (e z) + dist x z := by rw [hx, dist_comm]
      _ = dist x z + dist x z := by rw [e.dist_eq x z]
  -- On the other hand, consider the map `f : (E ≃ᵢ E) → (E ≃ᵢ E)`
  -- sending each `e` to `R ∘ e⁻¹ ∘ R ∘ e`, where `R` is the point reflection in the
  -- midpoint `z` of `[x, y]`.
  set R : PE ≃ᵢ PE := (pointReflection Real z).toIsometryEquiv
  set f : PE ≃ᵢ PE -> PE ≃ᵢ PE := fun e => ((e.trans R).trans e.symm).trans R
  -- Note that `f` doubles the value of `dist (e z) z`
  have hf_dist : forall e, dist (f e z) z = 2 * dist (e z) z := by
    intro e
    dsimp only [trans_apply, coe_toIsometryEquiv, f, R]
    rw [dist_pointReflection_fixed]; rw [← e.dist_eq]; rw [e.apply_symm_apply]; rw [dist_pointReflection_self_real]; rw [dist_comm]
  -- Also note that `f` maps `s` to itself
  have hf_maps_to : MapsTo f s s := by
    rintro e ⟨hx, hy⟩
    constructor <;> simp [f, R, z, hx, hy, e.symm_apply_eq.2 hx.symm, e.symm_apply_eq.2 hy.symm]
  -- Therefore, `dist (e z) z = 0` for all `e ∈ s`.
  set c := ⨆ e : s, dist ((e : PE ≃ᵢ PE) z) z
  have : c <= c / 2 := by
    apply ciSup_le
    rintro ⟨e, he⟩
    simp only [le_div_iff₀' (zero_lt_two' Real), ← hf_dist]
    exact le_ciSup h_bdd ⟨f e, hf_maps_to he⟩
  replace : c <= 0 := by linarith
  refine fun e hx hy => dist_le_zero.1 (le_trans ?_ this)
  exact le_ciSup h_bdd ⟨e, hx, hy⟩

/--
theorem `map_midpoint` / 定理 `map_midpoint`

English:
theorem map_midpoint
  given: (f : PE ≃ᵢ PF) (x y : PE)
  statement: f (midpoint Real x y) = midpoint Real (f x) (f y)
  proof: by
  set e : PE ≃ᵢ PE :=
    ((f.trans <| (pointReflection Real <| midpoint Real (f x) (f y)).toIsometryEquiv).trans f.symm).trans
      (pointReflection Real <| midpoint Real x y).toIsometryEquiv
  have hx : e x = x := by simp [e]
  have hy : e y = y := by simp [e]
  have hm := e.midpoint_fixed hx 

中文:
定理 map_midpoint
  条件: (f : PE ≃ᵢ PF) (x y : PE)
  结论: f (midpoint 实数 x y) = midpoint 实数 (f x) (f y)
  证明: by
  set e : PE ≃ᵢ PE :=
    ((f.trans <| (pointReflection Real <| midpoint Real (f x) (f y)).toIsometryEquiv).trans f.symm).trans
      (pointReflection Real <| midpoint Real x y).toIsometryEquiv
  have hx : e x = x := by simp [e]
  have hy : e y = y := by simp [e]
  have hm := e.midpoint_fixed hx 

Depends on / 依赖: coe_toIsometryEquiv, e.midpoint_fixed, eq_symm_apply, f.symm, f.trans, midpoint, midpoint_fixed, pointReflection, pointReflection_fixed_iff, pointReflection_self, pointReflection_symm, symm_apply_eq, toIsometryEquiv, toIsometryEquiv_symm, trans_apply
-/
theorem map_midpoint (f : PE ≃ᵢ PF) (x y : PE) : f (midpoint Real x y) = midpoint Real (f x) (f y) := by
  set e : PE ≃ᵢ PE :=
    ((f.trans <| (pointReflection Real <| midpoint Real (f x) (f y)).toIsometryEquiv).trans f.symm).trans
      (pointReflection Real <| midpoint Real x y).toIsometryEquiv
  have hx : e x = x := by simp [e]
  have hy : e y = y := by simp [e]
  have hm := e.midpoint_fixed hx hy
  simp only [e, trans_apply] at hm
  rwa [← eq_symm_apply, ← toIsometryEquiv_symm, pointReflection_symm, coe_toIsometryEquiv,
    coe_toIsometryEquiv, pointReflection_self, symm_apply_eq, @pointReflection_fixed_iff] at hm

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `ContinuousLinearEquiv` first, then a conversion to an `AffineMap`.
-/


/--
Definition of `toRealLinearIsometryEquivOfMapZero` / `toRealLinearIsometryEquivOfMapZero` 的定义

English:
definition toRealLinearIsometryEquivOfMapZero
  signature: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  body: { (AddMonoidHom.ofMapMidpoint Real Real f h0 f.map_midpoint).toRealLinearMap f.continuous, f with
    norm_map' := fun x => show ‖f x‖ = ‖x‖ by simp only [← dist_zero_right, ← h0, f.dist_eq] }

@[simp]

中文:
定义 toRealLinearIsometryEquivOfMapZero
  签名: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  定义体: { (AddMonoidHom.ofMapMidpoint Real Real f h0 f.map_midpoint).toRealLinearMap f.continuous, f with
    norm_map' := fun x => show ‖f x‖ = ‖x‖ by simp only [← dist_zero_right, ← h0, f.dist_eq] }

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ofMapMidpoint, continuous, dist_eq, dist_zero_right, f.continuous, f.dist_eq, f.map_midpoint, map_midpoint, norm_map, ofMapMidpoint, toRealLinearMap
-/
def toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) : E ≃ₗᵢ[Real] F :=
  { (AddMonoidHom.ofMapMidpoint Real Real f h0 f.map_midpoint).toRealLinearMap f.continuous, f with
    norm_map' := fun x => show ‖f x‖ = ‖x‖ by simp only [← dist_zero_right, ← h0, f.dist_eq] }

@[simp]
/--
theorem `coe_toRealLinearIsometryEquivOfMapZero` / 定理 `coe_toRealLinearIsometryEquivOfMapZero`

English:
theorem coe_toRealLinearIsometryEquivOfMapZero
  given: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  proof: rfl

@[simp]

中文:
定理 coe_toRealLinearIsometryEquivOfMapZero
  条件: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  证明: rfl

@[simp]
-/
theorem coe_toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = f :=
  rfl

@[simp]
/--
theorem `coe_toRealLinearIsometryEquivOfMapZero_symm` / 定理 `coe_toRealLinearIsometryEquivOfMapZero_symm`

English:
theorem coe_toRealLinearIsometryEquivOfMapZero_symm
  given: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  proof: rfl

中文:
定理 coe_toRealLinearIsometryEquivOfMapZero_symm
  条件: (f : E ≃ᵢ F) (h0 : f 0 = 0)
  证明: rfl
-/
theorem coe_toRealLinearIsometryEquivOfMapZero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0).symm = f.symm :=
  rfl

/--
Definition of `toRealLinearIsometryEquiv` / `toRealLinearIsometryEquiv` 的定义

English:
definition toRealLinearIsometryEquiv
  signature: (f : E ≃ᵢ F)
  body: (f.trans (IsometryEquiv.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by simpa only [sub_eq_add_neg] using! sub_self (f 0))

@[simp]

中文:
定义 toRealLinearIsometryEquiv
  签名: (f : E ≃ᵢ F)
  定义体: (f.trans (IsometryEquiv.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by simpa only [sub_eq_add_neg] using! sub_self (f 0))

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.addRight, addRight, f.trans, sub_eq_add_neg, sub_self, toRealLinearIsometryEquivOfMapZero
-/
def toRealLinearIsometryEquiv (f : E ≃ᵢ F) : E ≃ₗᵢ[Real] F :=
  (f.trans (IsometryEquiv.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by simpa only [sub_eq_add_neg] using! sub_self (f 0))

@[simp]
/--
theorem `toRealLinearIsometryEquiv_apply` / 定理 `toRealLinearIsometryEquiv_apply`

English:
theorem toRealLinearIsometryEquiv_apply
  given: (f : E ≃ᵢ F) (x : E)
  proof: (sub_eq_add_neg (f x) (f 0)).symm

@[simp]

中文:
定理 toRealLinearIsometryEquiv_apply
  条件: (f : E ≃ᵢ F) (x : E)
  证明: (sub_eq_add_neg (f x) (f 0)).symm

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem toRealLinearIsometryEquiv_apply (f : E ≃ᵢ F) (x : E) :
    (f.toRealLinearIsometryEquiv : E -> F) x = f x - f 0 :=
  (sub_eq_add_neg (f x) (f 0)).symm

@[simp]
/--
theorem `toRealLinearIsometryEquiv_symm_apply` / 定理 `toRealLinearIsometryEquiv_symm_apply`

English:
theorem toRealLinearIsometryEquiv_symm_apply
  given: (f : E ≃ᵢ F) (y : F)
  proof: rfl

中文:
定理 toRealLinearIsometryEquiv_symm_apply
  条件: (f : E ≃ᵢ F) (y : F)
  证明: rfl
-/
theorem toRealLinearIsometryEquiv_symm_apply (f : E ≃ᵢ F) (y : F) :
    (f.toRealLinearIsometryEquiv.symm : F -> E) y = f.symm (y + f 0) :=
  rfl

/--
Definition of `toRealAffineIsometryEquiv` / `toRealAffineIsometryEquiv` 的定义

English:
definition toRealAffineIsometryEquiv
  signature: (f : PE ≃ᵢ PF)
  body: AffineIsometryEquiv.mk' f
    ((vaddConst (Classical.arbitrary PE)).trans <|
        f.trans (vaddConst (f <| Classical.arbitrary PE)).symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE) fun p => by simp

@[simp]

中文:
定义 toRealAffineIsometryEquiv
  签名: (f : PE ≃ᵢ PF)
  定义体: AffineIsometryEquiv.mk' f
    ((vaddConst (Classical.arbitrary PE)).trans <|
        f.trans (vaddConst (f <| Classical.arbitrary PE)).symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE) fun p => by simp

@[simp]

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.mk, Classical, Classical.arbitrary, arbitrary, f.trans, toRealLinearIsometryEquiv, vaddConst
-/
def toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : PE ≃ᵃⁱ[Real] PF :=
  AffineIsometryEquiv.mk' f
    ((vaddConst (Classical.arbitrary PE)).trans <|
        f.trans (vaddConst (f <| Classical.arbitrary PE)).symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE) fun p => by simp

@[simp]
/--
theorem `coeFn_toRealAffineIsometryEquiv` / 定理 `coeFn_toRealAffineIsometryEquiv`

English:
theorem coeFn_toRealAffineIsometryEquiv
  given: (f : PE ≃ᵢ PF)
  statement: ⇑f.toRealAffineIsometryEquiv = f
  proof: rfl

@[simp]

中文:
定理 coeFn_toRealAffineIsometryEquiv
  条件: (f : PE ≃ᵢ PF)
  结论: ⇑f.to实数AffineIsometryEquiv = f
  证明: rfl

@[simp]
-/
theorem coeFn_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : ⇑f.toRealAffineIsometryEquiv = f :=
  rfl

@[simp]
/--
theorem `coe_toRealAffineIsometryEquiv` / 定理 `coe_toRealAffineIsometryEquiv`

English:
theorem coe_toRealAffineIsometryEquiv
  given: (f : PE ≃ᵢ PF)
  proof: by
  ext
  rfl

中文:
定理 coe_toRealAffineIsometryEquiv
  条件: (f : PE ≃ᵢ PF)
  证明: by
  ext
  rfl
-/
theorem coe_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) :
    f.toRealAffineIsometryEquiv.toIsometryEquiv = f := by
  ext
  rfl

end IsometryEquiv
