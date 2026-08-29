/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Junyan Xu
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Path

/-!
# H-spaces

This file defines H-spaces mainly following the approach proposed by Serre in his paper
*Homologie singulière des espaces fibrés*. The idea beneath `H-spaces` is that they are topological
spaces with a binary operation `⋀ : X → X → X` that is a homotopy-theoretic weakening of an
operation that would make `X` into a topological monoid.
In particular, there exists a "neutral element" `e : X` such that `fun x ↦ e ⋀ x` and
`fun x ↦ x ⋀ e` are homotopic to the identity on `X`, see
[the Wikipedia page of H-spaces](https://en.wikipedia.org/wiki/H-space).

Some notable properties of `H-spaces` are
* Their fundamental group is always abelian (by the same argument for topological groups);
* Their cohomology ring comes equipped with a structure of a Hopf-algebra;
* The loop space based at every `x : X` carries a structure of an `H-space`.

## Main Results

* Every topological group `G` is an `H-space` using its operation `* : G → G → G` (this is already
  true if `G` has an instance of a `MulOneClass` and `ContinuousMul`);
* Given two `H-spaces` `X` and `Y`, their product is again an `H`-space. We show in an example that
  starting with two topological groups `G, G'`, the `H`-space structure on `G × G'` is
  definitionally equal to the product of `H-space` structures on `G` and `G'`.
* The loop space based at every `x : X` carries a structure of an `H-space`.

## To Do
* Prove that for every `NormedAddTorsor Z` and every `z : Z`, the operation
  `fun x y ↦ midpoint x y` defines an `H-space` structure with `z` as a "neutral element".
* Prove that `S^0`, `S^1`, `S^3` and `S^7` are the unique spheres that are `H-spaces`, where the
  first three inherit the structure because they are topological groups (they are Lie groups,
  actually), isomorphic to the invertible elements in `ℤ`, in `ℂ` and in the quaternions; and the
  fourth from the fact that `S^7` coincides with the octonions of norm 1 (it is not a group, in
  particular, only has an instance of `MulOneClass`).

## References

* [J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*,
  Ann. of Math (2) 1951, 54, 425–505][serre1951]
-/

@[expose] public section

universe u v

noncomputable section

open scoped unitInterval

open Path ContinuousMap Set.Icc TopologicalSpace

/--
Definition of `HSpace` / `HSpace` 的定义

English:
class HSpace
  parameters: (X : Type u) [TopologicalSpace X]
  axioms and operations (5):
    - hmul : C(X × X, X)
    - e : X
    - hmul_e_e : hmul (e, e) = e
    - eHmul : (hmul.comp <| (const X e).prodMk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
    - hmulE : (hmul.comp <| (ContinuousMap.id X).prodMk <| const X e).HomotopyRel (ContinuousMap.id X) {e}

中文:
类 H空间
  参数: (X : 类型u) [拓扑空间 X]
  公理与运算 (5 个):
    - hmul : C(X × X, X)
    - e : X
    - hmul_e_e : hmul (e, e) = e
    - eHmul : (hmul.comp <| (const X e).prodMk <| 连续映射.id X).HomotopyRel (连续映射.id X) {e}
    - hmulE : (hmul.comp <| (连续映射.id X).prodMk <| const X e).HomotopyRel (连续映射.id X) {e}
-/
class HSpace (X : Type u) [TopologicalSpace X] where
  hmul : C(X × X, X)
  e : X
  hmul_e_e : hmul (e, e) = e
  eHmul :
    (hmul.comp <| (const X e).prodMk <| ContinuousMap.id X).HomotopyRel (ContinuousMap.id X) {e}
  hmulE :
    (hmul.comp <| (ContinuousMap.id X).prodMk <| const X e).HomotopyRel (ContinuousMap.id X) {e}

/-- The binary operation `hmul` on an `H`-space -/
scoped[HSpaces] notation x "⋀" y => HSpace.hmul (x, y)

open HSpaces

/--
Instance `HSpace.prod` / 实例 `HSpace.prod`

English:
instance HSpace.prod
  signature: (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] [HSpace X]
  body: ⟨fun p => (p.1.1 ⋀ p.2.1, p.1.2 ⋀ p.2.2), by fun_prop⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk_inj]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.2 x) (HSpace.eHmul.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.3 x) (HSpace.eHmul.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.eHmul.2 t x h.1) (HSpace.eHmul.2 t y h.2)
  hmulE := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.2 x) (HSpace.hmulE.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.3 x) (HSpace.hmulE.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.hmulE.2 t x h.1) (HSpace.hmulE.2 t y h.2)

中文:
实例 H空间.乘积
  签名: (X : 类型u) (Y : 类型v) [拓扑空间 X] [拓扑空间 Y] [H空间 X]
  定义体: ⟨fun p => (p.1.1 ⋀ p.2.1, p.1.2 ⋀ p.2.2), by fun_prop⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk_inj]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.2 x) (HSpace.eHmul.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.3 x) (HSpace.eHmul.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.eHmul.2 t x h.1) (HSpace.eHmul.2 t y h.2)
  hmulE := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.2 x) (HSpace.hmulE.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.3 x) (HSpace.hmulE.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.hmulE.2 t x h.1) (HSpace.hmulE.2 t y h.2)

Depends on / 依赖: fun_prop
-/
instance HSpace.prod (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] [HSpace X]
    [HSpace Y] : HSpace (X × Y) where
  hmul := ⟨fun p => (p.1.1 ⋀ p.2.1, p.1.2 ⋀ p.2.2), by fun_prop⟩
  e := (HSpace.e, HSpace.e)
  hmul_e_e := by
    simp only [ContinuousMap.coe_mk, Prod.mk_inj]
    exact ⟨HSpace.hmul_e_e, HSpace.hmul_e_e⟩
  eHmul := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.eHmul (p.1, p.2.1), HSpace.eHmul (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.2 x) (HSpace.eHmul.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.eHmul.1.3 x) (HSpace.eHmul.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.eHmul.2 t x h.1) (HSpace.eHmul.2 t y h.2)
  hmulE := by
    let G : I × X × Y -> X × Y := fun p => (HSpace.hmulE (p.1, p.2.1), HSpace.hmulE (p.1, p.2.2))
    have hG : Continuous G := by fun_prop
    use! ⟨G, hG⟩
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.2 x) (HSpace.hmulE.1.2 y)
    · rintro ⟨x, y⟩
      exact Prod.ext (HSpace.hmulE.1.3 x) (HSpace.hmulE.1.3 y)
    · rintro t ⟨x, y⟩ h
      replace h := Prod.mk_inj.mp h
      exact Prod.ext (HSpace.hmulE.2 t x h.1) (HSpace.hmulE.2 t y h.2)


namespace IsTopologicalGroup

/-- The definition `toHSpace` is not an instance because its additive version would
lead to a diamond since a topological field would inherit two `HSpace` structures, one from the
`MulOneClass` and one from the `AddZeroClass`. In the case of a group, we make
`IsTopologicalGroup.hSpace` an instance." -/
@[to_additive (attr := instance_reducible)
      /-- The definition `toHSpace` is not an instance because it comes together with a
      multiplicative version which would lead to a diamond since a topological field would inherit
      two `HSpace` structures, one from the `MulOneClass` and one from the `AddZeroClass`.
      In the case of an additive group, we make `IsTopologicalAddGroup.hSpace` an instance. -/]
/--
Definition of `toHSpace` / `toHSpace` 的定义

English:
definition toHSpace
  signature: (M : Type u) [MulOneClass M] [TopologicalSpace M] [ContinuousMul M]
  body: ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)

@[to_additive]

中文:
定义 toHSpace
  签名: (M : 类型u) [MulOne类 M] [拓扑空间 M] [连续乘法 M]
  定义体: ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)

@[to_additive]

Depends on / 依赖: Function, Function.uncurry, Mul.mul, continuous_mul, uncurry
-/
def toHSpace (M : Type u) [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] : HSpace M where
  hmul := ⟨Function.uncurry Mul.mul, continuous_mul⟩
  e := 1
  hmul_e_e := one_mul 1
  eHmul := (HomotopyRel.refl _ _).cast rfl (by ext1; apply one_mul)
  hmulE := (HomotopyRel.refl _ _).cast rfl (by ext1; apply mul_one)

@[to_additive]
instance (priority := 600) hSpace (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : HSpace G :=
  toHSpace G

/--
theorem `one_eq_hSpace_e` / 定理 `one_eq_hSpace_e`

English:
theorem one_eq_hSpace_e
  given: {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  proof: rfl

中文:
定理 one_eq_hSpace_e
  条件: {G : 类型u} [拓扑空间 G] [群 G] [是拓扑群 G]
  证明: rfl
-/
theorem one_eq_hSpace_e {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    (1 : G) = HSpace.e :=
  rfl

/- In the following example we see that the H-space structure on the product of two topological
groups is definitionally equally to the product H-space-structure of the two groups. -/
example {G G' : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace G']
    [Group G'] [IsTopologicalGroup G'] : IsTopologicalGroup.hSpace (G × G') = HSpace.prod G G' := by
  simp only [HSpace.prod]
  rfl


end IsTopologicalGroup

namespace unitInterval

/--
Definition of `qRight` / `qRight` 的定义

English:
definition qRight
  signature: (p : I × I)
  body: Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

@[fun_prop]

中文:
定义 qRight
  签名: (p : I × I)
  定义体: Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

@[fun_prop]

Depends on / 依赖: Set.projIcc, projIcc, zero_le_one
-/
def qRight (p : I × I) : I :=
  Set.projIcc 0 1 zero_le_one (2 * p.1 / (1 + p.2))

@[fun_prop]
/--
theorem `continuous_qRight` / 定理 `continuous_qRight`

English:
theorem continuous_qRight
  statement: Continuous qRight
  proof: continuous_projIcc.comp
    Continuous.div (by fun_prop) (by fun_prop) fun _ => (add_pos zero_lt_one).ne'

中文:
定理 continuous_qRight
  结论: 连续 qRight
  证明: continuous_projIcc.comp
    Continuous.div (by fun_prop) (by fun_prop) fun _ => (add_pos zero_lt_one).ne'

Depends on / 依赖: Continuous, Continuous.div, add_pos, continuous_projIcc, continuous_projIcc.comp, fun_prop, zero_lt_one
-/
theorem continuous_qRight : Continuous qRight :=
continuous_projIcc.comp
    Continuous.div (by fun_prop) (by fun_prop) fun _ => (add_pos zero_lt_one).ne'

/--
theorem `qRight_zero_left` / 定理 `qRight_zero_left`

English:
theorem qRight_zero_left
  given: (θ : I)
  statement: qRight (0, θ) = 0
  proof: Set.projIcc_of_le_left _ by simp only [coe_zero, mul_zero, zero_div, le_refl]

中文:
定理 qRight_zero_left
  条件: (θ : I)
  结论: qRight (0, θ) = 0
  证明: Set.projIcc_of_le_left _ by simp only [coe_zero, mul_zero, zero_div, le_refl]

Depends on / 依赖: Set.projIcc_of_le_left, coe_zero, le_refl, mul_zero, projIcc_of_le_left, zero_div
-/
theorem qRight_zero_left (θ : I) : qRight (0, θ) = 0 :=
Set.projIcc_of_le_left _ by simp only [coe_zero, mul_zero, zero_div, le_refl]

/--
theorem `qRight_one_left` / 定理 `qRight_one_left`

English:
theorem qRight_one_left
  given: (θ : I)
  statement: qRight (1, θ) = 1
  proof: Set.projIcc_of_right_le _
(le_div_iff₀ <| add_pos zero_lt_one).2 by
      dsimp only
      rw [coe_one]; rw [one_mul]; rw [mul_one]; rw [add_comm]; rw [← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _

中文:
定理 qRight_one_left
  条件: (θ : I)
  结论: qRight (1, θ) = 1
  证明: Set.projIcc_of_right_le _
(le_div_iff₀ <| add_pos zero_lt_one).2 by
      dsimp only
      rw [coe_one]; rw [one_mul]; rw [mul_one]; rw [add_comm]; rw [← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _

Depends on / 依赖: Set.projIcc_of_right_le, add_comm, add_le_add_iff_right, add_pos, coe_one, le_one, mul_one, one_add_one_eq_two, one_mul, projIcc_of_right_le, zero_lt_one
-/
theorem qRight_one_left (θ : I) : qRight (1, θ) = 1 :=
Set.projIcc_of_right_le _
(le_div_iff₀ <| add_pos zero_lt_one).2 by
      dsimp only
      rw [coe_one]; rw [one_mul]; rw [mul_one]; rw [add_comm]; rw [← one_add_one_eq_two]
      simp only [add_le_add_iff_right]
      exact le_one _

/--
theorem `qRight_zero_right` / 定理 `qRight_zero_right`

English:
theorem qRight_zero_right
  given: (t : I)
  proof: by
  simp only [qRight, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]
    refine ⟨t.2.1, ?_⟩
    tauto
  · rw [(Set.projIcc_eq_right _).2]
    · linarith
    · exact zero_lt_one

中文:
定理 qRight_zero_right
  条件: (t : I)
  证明: by
  simp only [qRight, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]
    refine ⟨t.2.1, ?_⟩
    tauto
  · rw [(Set.projIcc_eq_right _).2]
    · linarith
    · exact zero_lt_one

Depends on / 依赖: Set.projIcc_eq_right, Set.projIcc_of_mem, add_zero, coe_zero, div_one, mul_pos_mem_iff, projIcc_eq_right, projIcc_of_mem, qRight, split_ifs, zero_lt_one, zero_lt_two
-/
theorem qRight_zero_right (t : I) :
    (qRight (t, 0) : Real) = if (t : Real) <= 1 / 2 then (2 : Real) * t else 1 := by
  simp only [qRight, coe_zero, add_zero, div_one]
  split_ifs
  · rw [Set.projIcc_of_mem _ ((mul_pos_mem_iff zero_lt_two).2 _)]
    refine ⟨t.2.1, ?_⟩
    tauto
  · rw [(Set.projIcc_eq_right _).2]
    · linarith
    · exact zero_lt_one

/--
theorem `qRight_one_right` / 定理 `qRight_one_right`

English:
theorem qRight_one_right
  given: (t : I)
  statement: qRight (t, 1) = t
  proof: Eq.trans (by rw [qRight]; norm_num) Set.projIcc_val zero_le_one _

中文:
定理 qRight_one_right
  条件: (t : I)
  结论: qRight (t, 1) = t
  证明: Eq.trans (by rw [qRight]; norm_num) Set.projIcc_val zero_le_one _

Depends on / 依赖: Eq.trans, Set.projIcc_val, projIcc_val, qRight, zero_le_one
-/
theorem qRight_one_right (t : I) : qRight (t, 1) = t :=
Eq.trans (by rw [qRight]; norm_num) Set.projIcc_val zero_le_one _

end unitInterval

namespace Path

open unitInterval

variable {X : Type u} [TopologicalSpace X] {x y : X}

/--
Definition of `delayReflRight` / `delayReflRight` 的定义

English:
definition delayReflRight
  signature: (θ : I) (γ : Path x y)
  body: γ (qRight (t, θ))
  continuous_toFun := by fun_prop
  source' := by
    rw [qRight_zero_left]; rw [γ.source]
  target' := by
    rw [qRight_one_left]; rw [γ.target]

中文:
定义 delayReflRight
  签名: (θ : I) (γ : 道路 x y)
  定义体: γ (qRight (t, θ))
  continuous_toFun := by fun_prop
  source' := by
    rw [qRight_zero_left]; rw [γ.source]
  target' := by
    rw [qRight_one_left]; rw [γ.target]

Depends on / 依赖: qRight
-/
def delayReflRight (θ : I) (γ : Path x y) : Path x y where
  toFun t := γ (qRight (t, θ))
  continuous_toFun := by fun_prop
  source' := by
    rw [qRight_zero_left]; rw [γ.source]
  target' := by
    rw [qRight_one_left]; rw [γ.target]

/--
theorem `continuous_delayReflRight` / 定理 `continuous_delayReflRight`

English:
theorem continuous_delayReflRight
  statement: Continuous fun p : I × Path x y => delayReflRight p.1 p.2
  proof: continuous_uncurry_iff.mp
(continuous_snd.comp continuous_fst).eval
continuous_qRight.comp continuous_snd.prodMk continuous_fst.comp continuous_fst

中文:
定理 continuous_delayReflRight
  结论: 连续 fun p : I × 道路 x y => delayReflRight p.1 p.2
  证明: continuous_uncurry_iff.mp
(continuous_snd.comp continuous_fst).eval
continuous_qRight.comp continuous_snd.prodMk continuous_fst.comp continuous_fst

Depends on / 依赖: continuous_fst, continuous_fst.comp, continuous_qRight, continuous_qRight.comp, continuous_snd, continuous_snd.comp, continuous_snd.prodMk, continuous_uncurry_iff, continuous_uncurry_iff.mp, prodMk
-/
theorem continuous_delayReflRight : Continuous fun p : I × Path x y => delayReflRight p.1 p.2 :=
continuous_uncurry_iff.mp
(continuous_snd.comp continuous_fst).eval
continuous_qRight.comp continuous_snd.prodMk continuous_fst.comp continuous_fst

/--
theorem `delayReflRight_zero` / 定理 `delayReflRight_zero`

English:
theorem delayReflRight_zero
  given: (γ : Path x y)
  statement: delayReflRight 0 γ = γ.trans (Path.refl y)
  proof: by
  ext t
  simp only [delayReflRight, trans_apply, Path.coe_mk_mk,
    refl_apply]
  split_ifs with h; swap
  on_goal 1 => conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [qRight_zero_right]
  exacts [if_neg h, if_pos h]

中文:
定理 delayReflRight_zero
  条件: (γ : 道路 x y)
  结论: delayReflRight 0 γ = γ.trans (道路.refl y)
  证明: by
  ext t
  simp only [delayReflRight, trans_apply, Path.coe_mk_mk,
    refl_apply]
  split_ifs with h; swap
  on_goal 1 => conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [qRight_zero_right]
  exacts [if_neg h, if_pos h]

Depends on / 依赖: Path.coe_mk_mk, all_goals, coe_mk_mk, congr_arg, conv_rhs, delayReflRight, exacts, if_neg, if_pos, on_goal, qRight_zero_right, refl_apply, split_ifs, target, trans_apply
-/
theorem delayReflRight_zero (γ : Path x y) : delayReflRight 0 γ = γ.trans (Path.refl y) := by
  ext t
  simp only [delayReflRight, trans_apply, Path.coe_mk_mk,
    refl_apply]
  split_ifs with h; swap
  on_goal 1 => conv_rhs => rw [← γ.target]
  all_goals apply congr_arg γ; ext1; rw [qRight_zero_right]
  exacts [if_neg h, if_pos h]

/--
theorem `delayReflRight_one` / 定理 `delayReflRight_one`

English:
theorem delayReflRight_one
  given: (γ : Path x y)
  statement: delayReflRight 1 γ = γ
  proof: by
  ext t
  exact congr_arg γ (qRight_one_right t)

中文:
定理 delayReflRight_one
  条件: (γ : 道路 x y)
  结论: delayReflRight 1 γ = γ
  证明: by
  ext t
  exact congr_arg γ (qRight_one_right t)

Depends on / 依赖: congr_arg, qRight_one_right
-/
theorem delayReflRight_one (γ : Path x y) : delayReflRight 1 γ = γ := by
  ext t
  exact congr_arg γ (qRight_one_right t)

/--
Definition of `delayReflLeft` / `delayReflLeft` 的定义

English:
definition delayReflLeft
  signature: (θ : I) (γ : Path x y)
  body: (delayReflRight θ γ.symm).symm

中文:
定义 delayReflLeft
  签名: (θ : I) (γ : 道路 x y)
  定义体: (delayReflRight θ γ.symm).symm

Depends on / 依赖: delayReflRight
-/
def delayReflLeft (θ : I) (γ : Path x y) : Path x y :=
  (delayReflRight θ γ.symm).symm

/--
theorem `continuous_delayReflLeft` / 定理 `continuous_delayReflLeft`

English:
theorem continuous_delayReflLeft
  statement: Continuous fun p : I × Path x y => delayReflLeft p.1 p.2
  proof: Path.continuous_symm.comp
continuous_delayReflRight.comp
continuous_fst.prodMk Path.continuous_symm.comp continuous_snd

中文:
定理 continuous_delayReflLeft
  结论: 连续 fun p : I × 道路 x y => delayReflLeft p.1 p.2
  证明: Path.continuous_symm.comp
continuous_delayReflRight.comp
continuous_fst.prodMk Path.continuous_symm.comp continuous_snd

Depends on / 依赖: Path.continuous_symm.comp, continuous_delayReflRight, continuous_delayReflRight.comp, continuous_fst, continuous_fst.prodMk, continuous_snd, continuous_symm, prodMk
-/
theorem continuous_delayReflLeft : Continuous fun p : I × Path x y => delayReflLeft p.1 p.2 :=
Path.continuous_symm.comp
continuous_delayReflRight.comp
continuous_fst.prodMk Path.continuous_symm.comp continuous_snd

/--
theorem `delayReflLeft_zero` / 定理 `delayReflLeft_zero`

English:
theorem delayReflLeft_zero
  given: (γ : Path x y)
  statement: delayReflLeft 0 γ = (Path.refl x).trans γ
  proof: by
  simp only [delayReflLeft, delayReflRight_zero, trans_symm, refl_symm, Path.symm_symm]

中文:
定理 delayReflLeft_zero
  条件: (γ : 道路 x y)
  结论: delayReflLeft 0 γ = (道路.refl x).trans γ
  证明: by
  simp only [delayReflLeft, delayReflRight_zero, trans_symm, refl_symm, Path.symm_symm]

Depends on / 依赖: Path.symm_symm, delayReflLeft, delayReflRight_zero, refl_symm, symm_symm, trans_symm
-/
theorem delayReflLeft_zero (γ : Path x y) : delayReflLeft 0 γ = (Path.refl x).trans γ := by
  simp only [delayReflLeft, delayReflRight_zero, trans_symm, refl_symm, Path.symm_symm]

/--
theorem `delayReflLeft_one` / 定理 `delayReflLeft_one`

English:
theorem delayReflLeft_one
  given: (γ : Path x y)
  statement: delayReflLeft 1 γ = γ
  proof: by
  simp only [delayReflLeft, delayReflRight_one, Path.symm_symm]

中文:
定理 delayReflLeft_one
  条件: (γ : 道路 x y)
  结论: delayReflLeft 1 γ = γ
  证明: by
  simp only [delayReflLeft, delayReflRight_one, Path.symm_symm]

Depends on / 依赖: Path.symm_symm, delayReflLeft, delayReflRight_one, symm_symm
-/
theorem delayReflLeft_one (γ : Path x y) : delayReflLeft 1 γ = γ := by
  simp only [delayReflLeft, delayReflRight_one, Path.symm_symm]

/-- The loop space at x carries a structure of an H-space. Note that the field `eHmul`
(resp. `hmulE`) neither implies nor is implied by `Path.Homotopy.reflTrans`
(resp. `Path.Homotopy.transRefl`).
-/
instance (x : X) : HSpace (Path x x) where
  hmul := ⟨fun ρ => ρ.1.trans ρ.2, continuous_trans⟩
  e := refl x
  hmul_e_e := refl_trans_refl
  eHmul :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x => delayReflLeft p.1 p.2, continuous_delayReflLeft⟩,
          delayReflLeft_zero, delayReflLeft_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }
  hmulE :=
    { toHomotopy :=
        ⟨⟨fun p : I × Path x x => delayReflRight p.1 p.2, continuous_delayReflRight⟩,
          delayReflRight_zero, delayReflRight_one⟩
      prop' := by rintro t _ rfl; exact refl_trans_refl.symm }

end Path
