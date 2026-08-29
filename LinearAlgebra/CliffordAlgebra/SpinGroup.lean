/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Utensil Song, Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-!
# The Pin group and the Spin group

In this file we define `lipschitzGroup`, `pinGroup` and `spinGroup` and show they form a group.

## Main definitions

* `lipschitzGroup`: the Lipschitz group with a quadratic form.
* `pinGroup`: the Pin group defined as the infimum of `lipschitzGroup` and `unitary`.
* `spinGroup`: the Spin group defined as the infimum of `pinGroup` and `CliffordAlgebra.even`.

## Implementation Notes

The definition of the Lipschitz group
$\{ x \in \mathop{\mathcal{C}\ell} | x \text{ is invertible and } x v x^{-1} ∈ V \}$ is given by:

* [fulton2004], Chapter 20
* https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group

But they presumably form a group only in finite dimensions. So we define `lipschitzGroup` with
closure of all the invertible elements in the form of `ι Q m`, and we show this definition is
at least as large as the other definition (See `lipschitzGroup.conjAct_smul_range_ι` and
`lipschitzGroup.involute_act_ι_mem_range_ι`).
The reverse statement presumably is true only in finite dimensions.

Here are some discussions about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

## TODO

Try to show the reverse statement is true in finite dimensions.
-/

@[expose] public section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

/--
Definition of `lipschitzGroup` / `lipschitzGroup` 的定义

English:
definition lipschitzGroup
  signature: (Q : QuadraticForm R M)
  body: Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

中文:
定义 lipschitzGroup
  签名: (Q : QuadraticForm R M)
  定义体: Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

Depends on / 依赖: CliffordAlgebra, Set.range, Subgroup, Subgroup.closure, closure
-/
def lipschitzGroup (Q : QuadraticForm R M) : Subgroup (CliffordAlgebra Q)ˣ :=
  Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

namespace lipschitzGroup

/--
theorem `conjAct_smul_ι_mem_range_ι` / 定理 `conjAct_smul_ι_mem_range_ι`

English:
theorem conjAct_smul_ι_mem_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
  proof: by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def]; rw [ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q 

中文:
定理 conjAct_smul_ι_mem_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
  证明: by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def]; rw [ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q 

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_toConjAct, ConjAct.units_smul_def, Invert, Invertible, LinearMap, LinearMap.mem_range_self, Subgroup, Subgroup.closure_induction, closure_induction, generalizing, invOf_units, inv_mem, invertible, lipschitzGroup, mem_range_self, ofConjAct_toConjAct, simp_rw, units_smul_def, x.invertible
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
    [Invertible (2 : R)] (m : M) :
    ConjAct.toConjAct x • ι Q m in LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def]; rw [ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, ι_mul_ι_mul_invOf_ι, LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, inv_inv, ← ha, invOf_ι_mul_ι_mul_ι, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul]
    suffices ↑y * (↑z * ι Q m * ↑z⁻¹) * ↑y⁻¹ in _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz m
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

/--
theorem `involute_act_ι_mem_range_ι` / 定理 `involute_act_ι_mem_range_ι`

English:
theorem involute_act_ι_mem_range_ι
  statement: [Invertible (2 : R)]
  proof: by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, 

中文:
定理 involute_act_ι_mem_range_ι
  结论: [Invertible (2 : R)]
  证明: by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, 

Depends on / 依赖: Invertible, LinearMap, LinearMap.mem_range_self, LinearMap.range, Subgroup, Subgroup.closure_induction, closure_induction, generalizing, invOf_units, inv_mem, invertible, lipschitzGroup, map_neg, mem_range_self, neg_mul, simp_rw, x.invertible
-/
theorem involute_act_ι_mem_range_ι [Invertible (2 : R)]
    {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q) (b : M) :
      involute (Q := Q) ↑x * ι Q b * ↑x⁻¹ in LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, involute_ι, neg_mul, ι_mul_ι_mul_invOf_ι Q a b, ← map_neg,
      LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    let := invertibleNeg (ι Q a)
    let := Invertible.map involute (ι Q a)
    simp_rw [← invOf_units x, inv_inv, ← ha, map_invOf, involute_ι, invOf_neg, neg_mul,
      invOf_ι_mul_ι_mul_ι, ← map_neg, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, map_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul, map_mul]
    suffices involute (Q := Q) ↑y * (involute (Q := Q) ↑z * ι Q b * ↑z⁻¹) * ↑y⁻¹ in _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz b
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

/--
theorem `conjAct_smul_range_ι` / 定理 `conjAct_smul_range_ι`

English:
theorem conjAct_smul_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
  proof: by
  suffices forall x in lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (ι Q) <= LinearMap.range (ι Q) by
    apply le_antisymm
    · exact this _ hx
· have := smul_mono_right (ConjAct.toConjAct x) this _ (inv_mem hx)
      refine Eq.trans_le ?_ this
      simp only [map_inv, smul_in

中文:
定理 conjAct_smul_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
  证明: by
  suffices forall x in lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (ι Q) <= LinearMap.range (ι Q) by
    apply le_antisymm
    · exact this _ hx
· have := smul_mono_right (ConjAct.toConjAct x) this _ (inv_mem hx)
      refine Eq.trans_le ?_ this
      simp only [map_inv, smul_in

Depends on / 依赖: ConjAct, ConjAct.toConjAct, Eq.trans_le, LinearMap, LinearMap.range, Submodule, Submodule.map_le_iff_le_comap, Submodule.pointwise_smul_def, inv_mem, le_antisymm, lipschitzGroup, map_inv, map_le_iff_le_comap, pointwise_smul_def, smul_inv_smul, smul_mono_right, toConjAct, trans_le
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x in lipschitzGroup Q)
    [Invertible (2 : R)] :
    ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) := by
  suffices forall x in lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (ι Q) <= LinearMap.range (ι Q) by
    apply le_antisymm
    · exact this _ hx
· have := smul_mono_right (ConjAct.toConjAct x) this _ (inv_mem hx)
      refine Eq.trans_le ?_ this
      simp only [map_inv, smul_inv_smul]
  intro x hx
  rw [Submodule.pointwise_smul_def]; rw [Submodule.map_le_iff_le_comap]
  rintro _ ⟨m, rfl⟩
  exact conjAct_smul_ι_mem_range_ι hx _

/--
theorem `coe_mem_iff_mem` / 定理 `coe_mem_iff_mem`

English:
theorem coe_mem_iff_mem
  given: {x : (CliffordAlgebra Q)ˣ}
  proof: by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  norm_cast
  exact exists_eq_right

中文:
定理 coe_mem_iff_mem
  条件: {x : (CliffordAlgebra Q)ˣ}
  证明: by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  norm_cast
  exact exists_eq_right

Depends on / 依赖: Subgroup, Subgroup.mem_toSubmonoid, Submonoid, Submonoid.mem_map, Units.coeHom_apply, coeHom_apply, exists_eq_right, mem_map, mem_toSubmonoid
-/
theorem coe_mem_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔
    x in lipschitzGroup Q := by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  norm_cast
  exact exists_eq_right

end lipschitzGroup

/--
Definition of `pinGroup` / `pinGroup` 的定义

English:
definition pinGroup
  signature: (Q : QuadraticForm R M)
  body: (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

中文:
定义 pinGroup
  签名: (Q : QuadraticForm R M)
  定义体: (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

Depends on / 依赖: CliffordAlgebra, Units.coeHom, coeHom, lipschitzGroup, toSubmonoid, toSubmonoid.map, unitary
-/
def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

namespace pinGroup

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {x : CliffordAlgebra Q}
  proof: Iff.rfl

中文:
定理 mem_iff
  条件: {x : CliffordAlgebra Q}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff {x : CliffordAlgebra Q} :
    x in pinGroup Q ↔
      x in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧
        x in unitary (CliffordAlgebra Q) :=
  Iff.rfl

/--
theorem `mem_lipschitzGroup` / 定理 `mem_lipschitzGroup`

English:
theorem mem_lipschitzGroup
  given: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  proof: hx.1

中文:
定理 mem_lipschitzGroup
  条件: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  证明: hx.1
-/
theorem mem_lipschitzGroup {x : CliffordAlgebra Q} (hx : x in pinGroup Q) :
    x in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1

/--
theorem `mem_unitary` / 定理 `mem_unitary`

English:
theorem mem_unitary
  given: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  proof: hx.2

中文:
定理 mem_unitary
  条件: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  证明: hx.2
-/
theorem mem_unitary {x : CliffordAlgebra Q} (hx : x in pinGroup Q) :
    x in unitary (CliffordAlgebra Q) :=
  hx.2

/--
theorem `units_mem_iff` / 定理 `units_mem_iff`

English:
theorem units_mem_iff
  given: {x : (CliffordAlgebra Q)ˣ}
  proof: by
  rw [mem_iff]; rw [lipschitzGroup.coe_mem_iff_mem]

中文:
定理 units_mem_iff
  条件: {x : (CliffordAlgebra Q)ˣ}
  证明: by
  rw [mem_iff]; rw [lipschitzGroup.coe_mem_iff_mem]

Depends on / 依赖: coe_mem_iff_mem, lipschitzGroup, lipschitzGroup.coe_mem_iff_mem, mem_iff
-/
theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x in pinGroup Q ↔ x in lipschitzGroup Q ∧ ↑x in unitary (CliffordAlgebra Q) := by
  rw [mem_iff]; rw [lipschitzGroup.coe_mem_iff_mem]

/--
theorem `units_mem_lipschitzGroup` / 定理 `units_mem_lipschitzGroup`

English:
theorem units_mem_lipschitzGroup
  given: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  proof: (units_mem_iff.1 hx).1

中文:
定理 units_mem_lipschitzGroup
  条件: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  证明: (units_mem_iff.1 hx).1

Depends on / 依赖: units_mem_iff
-/
theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q) :
    x in lipschitzGroup Q :=
  (units_mem_iff.1 hx).1

/--
theorem `conjAct_smul_ι_mem_range_ι` / 定理 `conjAct_smul_ι_mem_range_ι`

English:
theorem conjAct_smul_ι_mem_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  proof: lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

中文:
定理 conjAct_smul_ι_mem_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  证明: lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

Depends on / 依赖: lipschitzGroup, lipschitzGroup.conjAct_smul_, units_mem_lipschitzGroup
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
    [Invertible (2 : R)] (y : M) : ConjAct.toConjAct x • ι Q y in LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/--
theorem `involute_act_ι_mem_range_ι` / 定理 `involute_act_ι_mem_range_ι`

English:
theorem involute_act_ι_mem_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  proof: lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

中文:
定理 involute_act_ι_mem_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  证明: lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

Depends on / 依赖: LinearMap, LinearMap.range
-/
theorem involute_act_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ in LinearMap.range (ι Q) :=
  lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/--
theorem `conjAct_smul_range_ι` / 定理 `conjAct_smul_range_ι`

English:
theorem conjAct_smul_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  proof: lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]

中文:
定理 conjAct_smul_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
  证明: lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]

Depends on / 依赖: lipschitzGroup, lipschitzGroup.conjAct_smul_range_, units_mem_lipschitzGroup
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]
/--
theorem `star_mul_self_of_mem` / 定理 `star_mul_self_of_mem`

English:
theorem star_mul_self_of_mem
  given: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  statement: star x * x = 1
  proof: hx.2.1

@[simp]

中文:
定理 star_mul_self_of_mem
  条件: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  结论: star x * x = 1
  证明: hx.2.1

@[simp]
-/
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : star x * x = 1 :=
  hx.2.1

@[simp]
/--
theorem `mul_star_self_of_mem` / 定理 `mul_star_self_of_mem`

English:
theorem mul_star_self_of_mem
  given: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  statement: x * star x = 1
  proof: hx.2.2

中文:
定理 mul_star_self_of_mem
  条件: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  结论: x * star x = 1
  证明: hx.2.2
-/
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : x * star x = 1 :=
  hx.2.2

/--
theorem `star_mem` / 定理 `star_mem`

English:
theorem star_mem
  given: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  statement: star x in pinGroup Q
  proof: by
  rw [mem_iff] at hx ⊢
  refine ⟨?_, Unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, _hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  refine ⟨st

中文:
定理 star_mem
  条件: {x : CliffordAlgebra Q} (hx : x in pinGroup Q)
  结论: star x in pinGroup Q
  证明: by
  rw [mem_iff] at hx ⊢
  refine ⟨?_, Unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, _hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  refine ⟨st

Depends on / 依赖: SetLike, SetLike.mem_coe, Subgroup, Subgroup.coe_toSubmonoid, Subgroup.mem_toSubmonoid, Submonoid, Submonoid.mem_map, Unitary, Unitary.star_mem, Units.coeHom_apply, Units.coe_star, Units.val_inj, Units.val_mul, Units.val_one, apply_fun, coeHom_apply, coe_star, coe_toSubmonoid, mem_coe, mem_iff
-/
theorem star_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : star x in pinGroup Q := by
  rw [mem_iff] at hx ⊢
  refine ⟨?_, Unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, _hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  refine ⟨star y, ?_, by simp only [hy₂, Units.coe_star]⟩
  rw [← hy₂] at hx₃
  have hy₃ : y * star y = 1 := by
    rw [← Units.val_inj]
    simp only [hx₃, Units.val_mul, Units.coe_star, Units.val_one]
  apply_fun fun x => y⁻¹ * x at hy₃
  simp only [inv_mul_cancel_left, mul_one] at hy₃
  simp only [hy₃, hy₁, inv_mem_iff]

/-- An element is in `pinGroup Q` if and only if `star x` is in `pinGroup Q`.
See `star_mem` for only one direction. -/
@[simp]
/--
theorem `star_mem_iff` / 定理 `star_mem_iff`

English:
theorem star_mem_iff
  given: {x : CliffordAlgebra Q}
  statement: star x in pinGroup Q ↔ x in pinGroup Q
  proof: by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

中文:
定理 star_mem_iff
  条件: {x : CliffordAlgebra Q}
  结论: star x in pinGroup Q ↔ x in pinGroup Q
  证明: by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

Depends on / 依赖: convert, star_mem, star_star
-/
theorem star_mem_iff {x : CliffordAlgebra Q} : star x in pinGroup Q ↔ x in pinGroup Q := by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (pinGroup Q)
  body: ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Star (pinGroup Q)
  定义体: ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]

Depends on / 依赖: star_mem, x.prop
-/
instance : Star (pinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: {x : pinGroup Q}
  statement: ↑(star x) = (star x : CliffordAlgebra Q)
  proof: rfl

中文:
定理 coe_star
  条件: {x : pinGroup Q}
  结论: ↑(star x) = (star x : CliffordAlgebra Q)
  证明: rfl
-/
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl

/--
theorem `coe_star_mul_self` / 定理 `coe_star_mul_self`

English:
theorem coe_star_mul_self
  given: (x : pinGroup Q)
  statement: (star x : CliffordAlgebra Q) * x = 1
  proof: star_mul_self_of_mem x.prop

中文:
定理 coe_star_mul_self
  条件: (x : pinGroup Q)
  结论: (star x : CliffordAlgebra Q) * x = 1
  证明: star_mul_self_of_mem x.prop

Depends on / 依赖: star_mul_self_of_mem, x.prop
-/
theorem coe_star_mul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop

/--
theorem `coe_mul_star_self` / 定理 `coe_mul_star_self`

English:
theorem coe_mul_star_self
  given: (x : pinGroup Q)
  statement: (x : CliffordAlgebra Q) * star x = 1
  proof: mul_star_self_of_mem x.prop

@[simp]

中文:
定理 coe_mul_star_self
  条件: (x : pinGroup Q)
  结论: (x : CliffordAlgebra Q) * star x = 1
  证明: mul_star_self_of_mem x.prop

@[simp]

Depends on / 依赖: mul_star_self_of_mem, x.prop
-/
theorem coe_mul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop

@[simp]
/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  given: (x : pinGroup Q)
  statement: star x * x = 1
  proof: Subtype.ext coe_star_mul_self x

@[simp]

中文:
定理 star_mul_self
  条件: (x : pinGroup Q)
  结论: star x * x = 1
  证明: Subtype.ext coe_star_mul_self x

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, coe_star_mul_self
-/
theorem star_mul_self (x : pinGroup Q) : star x * x = 1 :=
Subtype.ext coe_star_mul_self x

@[simp]
/--
theorem `mul_star_self` / 定理 `mul_star_self`

English:
theorem mul_star_self
  given: (x : pinGroup Q)
  statement: x * star x = 1
  proof: Subtype.ext coe_mul_star_self x

中文:
定理 mul_star_self
  条件: (x : pinGroup Q)
  结论: x * star x = 1
  证明: Subtype.ext coe_mul_star_self x

Depends on / 依赖: Subtype, Subtype.ext, coe_mul_star_self
-/
theorem mul_star_self (x : pinGroup Q) : x * star x = 1 :=
Subtype.ext coe_mul_star_self x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (pinGroup Q)
  body: star
  inv_mul_cancel := star_mul_self

中文:
实例 :
  签名: Group (pinGroup Q)
  定义体: star
  inv_mul_cancel := star_mul_self
-/
instance : Group (pinGroup Q) where
  inv := star
  inv_mul_cancel := star_mul_self

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (pinGroup Q)
  body: Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

中文:
实例 :
  签名: StarMul (pinGroup Q)
  定义体: Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

Depends on / 依赖: Subtype, Subtype.ext, star_involutive
-/
instance : StarMul (pinGroup Q) where
star_involutive _ := Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (pinGroup Q)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (pinGroup Q)
  定义体: ⟨1⟩
-/
instance : Inhabited (pinGroup Q) :=
  ⟨1⟩

/--
theorem `star_eq_inv` / 定理 `star_eq_inv`

English:
theorem star_eq_inv
  given: (x : pinGroup Q)
  statement: star x = x⁻¹
  proof: rfl

中文:
定理 star_eq_inv
  条件: (x : pinGroup Q)
  结论: star x = x⁻¹
  证明: rfl
-/
theorem star_eq_inv (x : pinGroup Q) : star x = x⁻¹ :=
  rfl

/--
theorem `star_eq_inv'` / 定理 `star_eq_inv'`

English:
theorem star_eq_inv'
  statement: (star : pinGroup Q -> pinGroup Q) = Inv.inv
  proof: rfl

中文:
定理 star_eq_inv'
  结论: (star : pinGroup Q -> pinGroup Q) = Inv.inv
  证明: rfl
-/
theorem star_eq_inv' : (star : pinGroup Q -> pinGroup Q) = Inv.inv :=
  rfl

/-- The elements in `pinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
/--
Definition of `toUnits` / `toUnits` 的定义

English:
definition toUnits
  signature: : pinGroup Q ->* (CliffordAlgebra Q)ˣ where
  body: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

中文:
定义 toUnits
  签名: : pinGroup Q ->* (CliffordAlgebra Q)ˣ where
  定义体: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

Depends on / 依赖: coe_mul_star_self, coe_star_mul_self
-/
def toUnits : pinGroup Q ->* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

/--
theorem `toUnits_injective` / 定理 `toUnits_injective`

English:
theorem toUnits_injective
  statement: Function.Injective (toUnits : pinGroup Q -> (CliffordAlgebra Q)ˣ)
  proof: fun _x _y h => Subtype.ext Units.ext_iff.mp h

中文:
定理 toUnits_injective
  结论: Function.Injective (toUnits : pinGroup Q -> (CliffordAlgebra Q)ˣ)
  证明: fun _x _y h => Subtype.ext Units.ext_iff.mp h

Depends on / 依赖: Subtype, Subtype.ext, Units.ext_iff.mp, ext_iff
-/
theorem toUnits_injective : Function.Injective (toUnits : pinGroup Q -> (CliffordAlgebra Q)ˣ) :=
fun _x _y h => Subtype.ext Units.ext_iff.mp h

end pinGroup

end Pin

section Spin

open CliffordAlgebra MulAction

open scoped Pointwise

/--
Definition of `spinGroup` / `spinGroup` 的定义

English:
definition spinGroup
  signature: (Q : QuadraticForm R M)
  body: pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid

中文:
定义 spinGroup
  签名: (Q : QuadraticForm R M)
  定义体: pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.even, pinGroup, toSubmonoid, toSubring, toSubring.toSubmonoid
-/
def spinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid

namespace spinGroup

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {x : CliffordAlgebra Q}
  statement: x in spinGroup Q ↔ x in pinGroup Q ∧ x in even Q
  proof: Iff.rfl

中文:
定理 mem_iff
  条件: {x : CliffordAlgebra Q}
  结论: x in spinGroup Q ↔ x in pinGroup Q ∧ x in even Q
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_iff {x : CliffordAlgebra Q} : x in spinGroup Q ↔ x in pinGroup Q ∧ x in even Q :=
  Iff.rfl

/--
theorem `mem_pin` / 定理 `mem_pin`

English:
theorem mem_pin
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: x in pinGroup Q
  proof: hx.1

中文:
定理 mem_pin
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: x in pinGroup Q
  证明: hx.1
-/
theorem mem_pin {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x in pinGroup Q :=
  hx.1

/--
theorem `mem_even` / 定理 `mem_even`

English:
theorem mem_even
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: x in even Q
  proof: hx.2

中文:
定理 mem_even
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: x in even Q
  证明: hx.2
-/
theorem mem_even {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x in even Q :=
  hx.2

/--
theorem `units_mem_lipschitzGroup` / 定理 `units_mem_lipschitzGroup`

English:
theorem units_mem_lipschitzGroup
  given: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  proof: pinGroup.units_mem_lipschitzGroup (mem_pin hx)

中文:
定理 units_mem_lipschitzGroup
  条件: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  证明: pinGroup.units_mem_lipschitzGroup (mem_pin hx)

Depends on / 依赖: mem_pin, pinGroup, pinGroup.units_mem_lipschitzGroup, units_mem_lipschitzGroup
-/
theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q) :
    x in lipschitzGroup Q :=
  pinGroup.units_mem_lipschitzGroup (mem_pin hx)

/--
theorem `involute_eq` / 定理 `involute_eq`

English:
theorem involute_eq
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: involute x = x
  proof: involute_eq_of_mem_even (mem_even hx)

中文:
定理 involute_eq
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: involute x = x
  证明: involute_eq_of_mem_even (mem_even hx)

Depends on / 依赖: involute_eq_of_mem_even, mem_even
-/
theorem involute_eq {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : involute x = x :=
  involute_eq_of_mem_even (mem_even hx)

/--
theorem `units_involute_act_eq_conjAct` / 定理 `units_involute_act_eq_conjAct`

English:
theorem units_involute_act_eq_conjAct
  given: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q) (y : M)
  proof: by
  rw [involute_eq hx]; rw [@ConjAct.units_smul_def]; rw [@ConjAct.ofConjAct_toConjAct]

中文:
定理 units_involute_act_eq_conjAct
  条件: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q) (y : M)
  证明: by
  rw [involute_eq hx]; rw [@ConjAct.units_smul_def]; rw [@ConjAct.ofConjAct_toConjAct]

Depends on / 依赖: ConjAct, ConjAct.ofConjAct_toConjAct, ConjAct.toConjAct, ConjAct.units_smul_def, involute_eq, ofConjAct_toConjAct, toConjAct, units_smul_def
-/
theorem units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q) (y : M) :
    involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ = ConjAct.toConjAct x • (ι Q y) := by
  rw [involute_eq hx]; rw [@ConjAct.units_smul_def]; rw [@ConjAct.ofConjAct_toConjAct]

/--
theorem `conjAct_smul_ι_mem_range_ι` / 定理 `conjAct_smul_ι_mem_range_ι`

English:
theorem conjAct_smul_ι_mem_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  proof: lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

中文:
定理 conjAct_smul_ι_mem_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  证明: lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

Depends on / 依赖: lipschitzGroup, lipschitzGroup.conjAct_smul_, units_mem_lipschitzGroup
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
    [Invertible (2 : R)] (y : M) : ConjAct.toConjAct x • ι Q y in LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/--
theorem `involute_act_ι_mem_range_ι` / 定理 `involute_act_ι_mem_range_ι`

English:
theorem involute_act_ι_mem_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  proof: lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

中文:
定理 involute_act_ι_mem_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  证明: lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

Depends on / 依赖: LinearMap, LinearMap.range
-/
theorem involute_act_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ in LinearMap.range (ι Q) :=
  lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/--
theorem `conjAct_smul_range_ι` / 定理 `conjAct_smul_range_ι`

English:
theorem conjAct_smul_range_ι
  statement: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  proof: lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]

中文:
定理 conjAct_smul_range_ι
  结论: {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
  证明: lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]

Depends on / 依赖: lipschitzGroup, lipschitzGroup.conjAct_smul_range_, units_mem_lipschitzGroup
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]
/--
theorem `star_mul_self_of_mem` / 定理 `star_mul_self_of_mem`

English:
theorem star_mul_self_of_mem
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: star x * x = 1
  proof: hx.1.2.1

@[simp]

中文:
定理 star_mul_self_of_mem
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: star x * x = 1
  证明: hx.1.2.1

@[simp]
-/
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : star x * x = 1 :=
  hx.1.2.1

@[simp]
/--
theorem `mul_star_self_of_mem` / 定理 `mul_star_self_of_mem`

English:
theorem mul_star_self_of_mem
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: x * star x = 1
  proof: hx.1.2.2

中文:
定理 mul_star_self_of_mem
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: x * star x = 1
  证明: hx.1.2.2
-/
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x * star x = 1 :=
  hx.1.2.2

/--
theorem `star_mem` / 定理 `star_mem`

English:
theorem star_mem
  given: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  statement: star x in spinGroup Q
  proof: by
  rw [mem_iff] at hx ⊢
  obtain ⟨hx₁, hx₂⟩ := hx
  refine ⟨pinGroup.star_mem hx₁, ?_⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]

中文:
定理 star_mem
  条件: {x : CliffordAlgebra Q} (hx : x in spinGroup Q)
  结论: star x in spinGroup Q
  证明: by
  rw [mem_iff] at hx ⊢
  obtain ⟨hx₁, hx₂⟩ := hx
  refine ⟨pinGroup.star_mem hx₁, ?_⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.even, Submodule, Submodule.mem_toSubalgebra, involute_mem_evenOdd_iff, mem_iff, mem_toSubalgebra, pinGroup, pinGroup.star_mem, reverse_mem_evenOdd_iff, star_def, star_mem
-/
theorem star_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : star x in spinGroup Q := by
  rw [mem_iff] at hx ⊢
  obtain ⟨hx₁, hx₂⟩ := hx
  refine ⟨pinGroup.star_mem hx₁, ?_⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]

/-- An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`.
See `star_mem` for only one direction.
-/
@[simp]
/--
theorem `star_mem_iff` / 定理 `star_mem_iff`

English:
theorem star_mem_iff
  given: {x : CliffordAlgebra Q}
  statement: star x in spinGroup Q ↔ x in spinGroup Q
  proof: by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

中文:
定理 star_mem_iff
  条件: {x : CliffordAlgebra Q}
  结论: star x in spinGroup Q ↔ x in spinGroup Q
  证明: by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

Depends on / 依赖: convert, star_mem, star_star
-/
theorem star_mem_iff {x : CliffordAlgebra Q} : star x in spinGroup Q ↔ x in spinGroup Q := by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Star (spinGroup Q)
  body: ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Star (spinGroup Q)
  定义体: ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]

Depends on / 依赖: star_mem, x.prop
-/
instance : Star (spinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
/--
theorem `coe_star` / 定理 `coe_star`

English:
theorem coe_star
  given: {x : spinGroup Q}
  statement: ↑(star x) = (star x : CliffordAlgebra Q)
  proof: rfl

中文:
定理 coe_star
  条件: {x : spinGroup Q}
  结论: ↑(star x) = (star x : CliffordAlgebra Q)
  证明: rfl
-/
theorem coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl

/--
theorem `coe_star_mul_self` / 定理 `coe_star_mul_self`

English:
theorem coe_star_mul_self
  given: (x : spinGroup Q)
  statement: (star x : CliffordAlgebra Q) * x = 1
  proof: star_mul_self_of_mem x.prop

中文:
定理 coe_star_mul_self
  条件: (x : spinGroup Q)
  结论: (star x : CliffordAlgebra Q) * x = 1
  证明: star_mul_self_of_mem x.prop

Depends on / 依赖: star_mul_self_of_mem, x.prop
-/
theorem coe_star_mul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop

/--
theorem `coe_mul_star_self` / 定理 `coe_mul_star_self`

English:
theorem coe_mul_star_self
  given: (x : spinGroup Q)
  statement: (x : CliffordAlgebra Q) * star x = 1
  proof: mul_star_self_of_mem x.prop

@[simp]

中文:
定理 coe_mul_star_self
  条件: (x : spinGroup Q)
  结论: (x : CliffordAlgebra Q) * star x = 1
  证明: mul_star_self_of_mem x.prop

@[simp]

Depends on / 依赖: mul_star_self_of_mem, x.prop
-/
theorem coe_mul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop

@[simp]
/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  given: (x : spinGroup Q)
  statement: star x * x = 1
  proof: Subtype.ext coe_star_mul_self x

@[simp]

中文:
定理 star_mul_self
  条件: (x : spinGroup Q)
  结论: star x * x = 1
  证明: Subtype.ext coe_star_mul_self x

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, coe_star_mul_self
-/
theorem star_mul_self (x : spinGroup Q) : star x * x = 1 :=
Subtype.ext coe_star_mul_self x

@[simp]
/--
theorem `mul_star_self` / 定理 `mul_star_self`

English:
theorem mul_star_self
  given: (x : spinGroup Q)
  statement: x * star x = 1
  proof: Subtype.ext coe_mul_star_self x

中文:
定理 mul_star_self
  条件: (x : spinGroup Q)
  结论: x * star x = 1
  证明: Subtype.ext coe_mul_star_self x

Depends on / 依赖: Subtype, Subtype.ext, coe_mul_star_self
-/
theorem mul_star_self (x : spinGroup Q) : x * star x = 1 :=
Subtype.ext coe_mul_star_self x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (spinGroup Q)
  body: star
  inv_mul_cancel := star_mul_self

中文:
实例 :
  签名: Group (spinGroup Q)
  定义体: star
  inv_mul_cancel := star_mul_self
-/
instance : Group (spinGroup Q) where
  inv := star
  inv_mul_cancel := star_mul_self

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (spinGroup Q)
  body: Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

中文:
实例 :
  签名: StarMul (spinGroup Q)
  定义体: Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

Depends on / 依赖: Subtype, Subtype.ext, star_involutive
-/
instance : StarMul (spinGroup Q) where
star_involutive _ := Subtype.ext star_involutive _
star_mul _ _ := Subtype.ext star_mul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (spinGroup Q)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (spinGroup Q)
  定义体: ⟨1⟩
-/
instance : Inhabited (spinGroup Q) :=
  ⟨1⟩

/--
theorem `star_eq_inv` / 定理 `star_eq_inv`

English:
theorem star_eq_inv
  given: (x : spinGroup Q)
  statement: star x = x⁻¹
  proof: rfl

中文:
定理 star_eq_inv
  条件: (x : spinGroup Q)
  结论: star x = x⁻¹
  证明: rfl
-/
theorem star_eq_inv (x : spinGroup Q) : star x = x⁻¹ :=
  rfl

/--
theorem `star_eq_inv'` / 定理 `star_eq_inv'`

English:
theorem star_eq_inv'
  statement: (star : spinGroup Q -> spinGroup Q) = Inv.inv
  proof: rfl

中文:
定理 star_eq_inv'
  结论: (star : spinGroup Q -> spinGroup Q) = Inv.inv
  证明: rfl
-/
theorem star_eq_inv' : (star : spinGroup Q -> spinGroup Q) = Inv.inv :=
  rfl

/-- The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
/--
Definition of `toUnits` / `toUnits` 的定义

English:
definition toUnits
  signature: : spinGroup Q ->* (CliffordAlgebra Q)ˣ where
  body: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

中文:
定义 toUnits
  签名: : spinGroup Q ->* (CliffordAlgebra Q)ˣ where
  定义体: ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

Depends on / 依赖: coe_mul_star_self, coe_star_mul_self
-/
def toUnits : spinGroup Q ->* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl

/--
theorem `toUnits_injective` / 定理 `toUnits_injective`

English:
theorem toUnits_injective
  statement: Function.Injective (toUnits : spinGroup Q -> (CliffordAlgebra Q)ˣ)
  proof: fun _x _y h => Subtype.ext Units.ext_iff.mp h

中文:
定理 toUnits_injective
  结论: Function.Injective (toUnits : spinGroup Q -> (CliffordAlgebra Q)ˣ)
  证明: fun _x _y h => Subtype.ext Units.ext_iff.mp h

Depends on / 依赖: Subtype, Subtype.ext, Units.ext_iff.mp, ext_iff
-/
theorem toUnits_injective : Function.Injective (toUnits : spinGroup Q -> (CliffordAlgebra Q)ˣ) :=
fun _x _y h => Subtype.ext Units.ext_iff.mp h

end spinGroup

end Spin
