/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Notation

/-!
# Lie groups

A Lie group is a group that is also a `C^n` manifold, in which the group operations of
multiplication and inversion are `C^n` maps. Regularity of the group multiplication means that
multiplication is a `C^n` mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff, a Lie group here is not
guaranteed to be second-countable (even though it can be proved that it is Hausdorff). Note also
that Lie groups here are not necessarily finite dimensional.

## Main definitions

* `LieAddGroup I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `LieGroup I G` : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.
* `ContMDiffInv₀`: typeclass for `C^n` manifolds with `0` and `Inv` such that inversion is `C^n`
  map at each non-zero point. This includes complete normed fields and (multiplicative) Lie groups.


## Main results
* `ContMDiff.inv`, `ContMDiff.div` and variants: point-wise inversion and division of maps `M → G`
  is `C^n`.
* `ContMDiff.inv₀` and variants: if `ContMDiffInv₀ I n N`, point-wise inversion of `C^n`
  maps `f : M → N` is `C^n` at all points at which `f` doesn't vanish.
* `ContMDiff.div₀` and variants: if also `ContMDiffMul I n N` (i.e., `N` is a Lie group except
  possibly for smoothness of inversion at `0`), similar results hold for point-wise division.
* `instNormedSpaceLieAddGroup` : a normed vector space over a nontrivially normed field
  is an additive Lie group.
* `Instances/UnitsOfNormedAlgebra` shows that the group of units of a complete normed `𝕜`-algebra
  is a multiplicative Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : ModelWithCorners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, because in the product situation,
the model space is `ModelProd E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : ModelWithCorners 𝕜 E H`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

-- See note [Design choices about smooth algebraic structures]
/--
Definition of `LieAddGroup` / `LieAddGroup` 的定义

English:
class LieAddGroup
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  extends: ContMDiffAdd I n G
  axioms and operations (1):
    - contMDiff_neg : CMDiff n fun a : G => -a

中文:
类 LieAddGroup
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  继承: ContMDiffAdd I n G
  公理与运算 (1 个):
    - contMDiff_neg : CMDiff n fun a : G => -a
-/
class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : Nat∞ω) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffAdd I n G where
  /-- Negation is smooth in an additive Lie group. -/
  contMDiff_neg : CMDiff n fun a : G => -a

-- See note [Design choices about smooth algebraic structures]
/-- A (multiplicative) Lie group is a group and a `C^n` manifold at the same time in which
the multiplication and inverse operations are `C^n`. -/
@[to_additive]
/--
Definition of `LieGroup` / `LieGroup` 的定义

English:
class LieGroup
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  extends: ContMDiffMul I n G
  axioms and operations (1):
    - contMDiff_inv : CMDiff n fun a : G => a⁻¹

中文:
类 LieGroup
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  继承: ContMDiffMul I n G
  公理与运算 (1 个):
    - contMDiff_inv : CMDiff n fun a : G => a⁻¹
-/
class LieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : Nat∞ω) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffMul I n G where
  /-- Inversion is smooth in a Lie group. -/
  contMDiff_inv : CMDiff n fun a : G => a⁻¹

/-!
  ### Smoothness of inversion, negation, division and subtraction

  Let `f : M → G` be a `C^n` function into a Lie group, then `f` is point-wise
  invertible with smooth inverse `f`. If `f` and `g` are two such functions, the quotient
  `f / g` (i.e., the point-wise product of `f` and the point-wise inverse of `g`) is also `C^n`. -/
section PointwiseDivision

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : Nat∞ω} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
/--
theorem `LieGroup.of_le` / 定理 `LieGroup.of_le`

English:
theorem LieGroup.of_le
  statement: {m n : Nat∞ω} (hmn : m <= n)
  proof: by
  have : ContMDiffMul I m G := ContMDiffMul.of_le hmn
  exact ⟨h.contMDiff_inv.of_le hmn⟩

@[to_additive]

中文:
定理 LieGroup.of_le
  结论: {m n : 自然数∞ω} (hmn : m <= n)
  证明: by
  have : ContMDiffMul I m G := ContMDiffMul.of_le hmn
  exact ⟨h.contMDiff_inv.of_le hmn⟩

@[to_additive]
-/
protected theorem LieGroup.of_le {m n : Nat∞ω} (hmn : m <= n)
    [h : LieGroup I n G] : LieGroup I m G := by
  have : ContMDiffMul I m G := ContMDiffMul.of_le hmn
  exact ⟨h.contMDiff_inv.of_le hmn⟩

@[to_additive]
instance {a : Nat∞ω} [LieGroup I ∞ G] [h : ENat.LEInfty a] : LieGroup I a G :=
  LieGroup.of_le h.out

@[to_additive]
instance {a : Nat∞ω} [LieGroup I ω G] : LieGroup I a G :=
  LieGroup.of_le le_top

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalGroup
  signature: G] : LieGroup I 0 G
  body: by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_inv

@[to_additive]

中文:
实例 [IsTopologicalGroup
  签名: G] : LieGroup I 0 G
  定义体: by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_inv

@[to_additive]

Depends on / 依赖: contMDiff_zero_iff, continuous_inv
-/
instance [IsTopologicalGroup G] : LieGroup I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_inv

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LieGroup
  signature: I 2 G] : LieGroup I 1 G
  body: LieGroup.of_le one_le_two

中文:
实例 [LieGroup
  签名: I 2 G] : LieGroup I 1 G
  定义体: LieGroup.of_le one_le_two

Depends on / 依赖: LieGroup, LieGroup.of_le, of_le, one_le_two
-/
instance [LieGroup I 2 G] : LieGroup I 1 G :=
  LieGroup.of_le one_le_two

variable [LieGroup I n G]

section

variable (I n)

/-- In a Lie group, inversion is `C^n`. -/
@[to_additive /-- In an additive Lie group, inversion is a smooth map. -/]
/--
theorem `contMDiff_inv` / 定理 `contMDiff_inv`

English:
theorem contMDiff_inv
  statement: CMDiff n fun x : G => x⁻¹
  proof: LieGroup.contMDiff_inv

include I n in

中文:
定理 contMDiff_inv
  结论: CMDiff n fun x : G => x⁻¹
  证明: LieGroup.contMDiff_inv

include I n in

Depends on / 依赖: LieGroup, LieGroup.contMDiff_inv, contMDiff_inv
-/
theorem contMDiff_inv : CMDiff n fun x : G => x⁻¹ :=
  LieGroup.contMDiff_inv

include I n in
/-- A Lie group is a topological group. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- An additive Lie group is an additive topological group. This is not an instance
for technical reasons, see note [Design choices about smooth algebraic structures]. -/]
/--
theorem `topologicalGroup_of_lieGroup` / 定理 `topologicalGroup_of_lieGroup`

English:
theorem topologicalGroup_of_lieGroup
  statement: IsTopologicalGroup G
  proof: { continuousMul_of_contMDiffMul I n with continuous_inv := (contMDiff_inv I n).continuous }

中文:
定理 topologicalGroup_of_lieGroup
  结论: IsTopologicalGroup G
  证明: { continuousMul_of_contMDiffMul I n with continuous_inv := (contMDiff_inv I n).continuous }

Depends on / 依赖: contMDiff_inv, continuous, continuousMul_of_contMDiffMul, continuous_inv
-/
theorem topologicalGroup_of_lieGroup : IsTopologicalGroup G :=
  { continuousMul_of_contMDiffMul I n with continuous_inv := (contMDiff_inv I n).continuous }

end

@[to_additive]
/--
theorem `ContMDiffWithinAt.inv` / 定理 `ContMDiffWithinAt.inv`

English:
theorem ContMDiffWithinAt.inv
  statement: {f : M -> G} {s : Set M} {x₀ : M}
  proof: (contMDiff_inv I n).contMDiffAt.contMDiffWithinAt.comp x₀ hf Set.mapsTo_univ _ _

@[to_additive]

中文:
定理 ContMDiffWithinAt.inv
  结论: {f : M -> G} {s : Set M} {x₀ : M}
  证明: (contMDiff_inv I n).contMDiffAt.contMDiffWithinAt.comp x₀ hf Set.mapsTo_univ _ _

@[to_additive]

Depends on / 依赖: Set.mapsTo_univ, contMDiffAt, contMDiffAt.contMDiffWithinAt.comp, contMDiffWithinAt, contMDiff_inv, mapsTo_univ
-/
theorem ContMDiffWithinAt.inv {f : M -> G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) : CMDiffAt[s] n (fun x => (f x)⁻¹) x₀ :=
(contMDiff_inv I n).contMDiffAt.contMDiffWithinAt.comp x₀ hf Set.mapsTo_univ _ _

@[to_additive]
/--
theorem `ContMDiffAt.inv` / 定理 `ContMDiffAt.inv`

English:
theorem ContMDiffAt.inv
  given: {f : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀)
  proof: (contMDiff_inv I n).contMDiffAt.comp x₀ hf

@[to_additive]

中文:
定理 ContMDiffAt.inv
  条件: {f : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀)
  证明: (contMDiff_inv I n).contMDiffAt.comp x₀ hf

@[to_additive]

Depends on / 依赖: contMDiffAt, contMDiffAt.comp, contMDiff_inv
-/
theorem ContMDiffAt.inv {f : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀) :
    CMDiffAt n (fun x => (f x)⁻¹) x₀ :=
  (contMDiff_inv I n).contMDiffAt.comp x₀ hf

@[to_additive]
/--
theorem `ContMDiffOn.inv` / 定理 `ContMDiffOn.inv`

English:
theorem ContMDiffOn.inv
  given: {f : M -> G} {s : Set M} (hf : CMDiff[s] n f)
  proof: fun x hx => (hf x hx).inv

@[to_additive]

中文:
定理 ContMDiffOn.inv
  条件: {f : M -> G} {s : Set M} (hf : CMDiff[s] n f)
  证明: fun x hx => (hf x hx).inv

@[to_additive]
-/
theorem ContMDiffOn.inv {f : M -> G} {s : Set M} (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x => (f x)⁻¹) := fun x hx => (hf x hx).inv

@[to_additive]
/--
theorem `ContMDiff.inv` / 定理 `ContMDiff.inv`

English:
theorem ContMDiff.inv
  given: {f : M -> G} (hf : CMDiff n f)
  statement: CMDiff n fun x => (f x)⁻¹
  proof: fun x => (hf x).inv

@[to_additive]

中文:
定理 ContMDiff.inv
  条件: {f : M -> G} (hf : CMDiff n f)
  结论: CMDiff n fun x => (f x)⁻¹
  证明: fun x => (hf x).inv

@[to_additive]
-/
theorem ContMDiff.inv {f : M -> G} (hf : CMDiff n f) : CMDiff n fun x => (f x)⁻¹ :=
  fun x => (hf x).inv

@[to_additive]
/--
theorem `ContMDiffWithinAt.div` / 定理 `ContMDiffWithinAt.div`

English:
theorem ContMDiffWithinAt.div
  statement: {f g : M -> G} {s : Set M} {x₀ : M}
  proof: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

中文:
定理 ContMDiffWithinAt.div
  结论: {f g : M -> G} {s : Set M} {x₀ : M}
  证明: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv, simp_rw
-/
theorem ContMDiffWithinAt.div {f g : M -> G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) (hg : CMDiffAt[s] n g x₀) :
    CMDiffAt[s] n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
/--
theorem `ContMDiffAt.div` / 定理 `ContMDiffAt.div`

English:
theorem ContMDiffAt.div
  statement: {f g : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀)
  proof: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

中文:
定理 ContMDiffAt.div
  结论: {f g : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀)
  证明: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv, simp_rw
-/
theorem ContMDiffAt.div {f g : M -> G} {x₀ : M} (hf : CMDiffAt n f x₀)
    (hg : CMDiffAt n g x₀) : CMDiffAt n (fun x => f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
/--
theorem `ContMDiffOn.div` / 定理 `ContMDiffOn.div`

English:
theorem ContMDiffOn.div
  statement: {f g : M -> G} {s : Set M} (hf : CMDiff[s] n f)
  proof: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

中文:
定理 ContMDiffOn.div
  结论: {f g : M -> G} {s : Set M} (hf : CMDiff[s] n f)
  证明: by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv, simp_rw
-/
theorem ContMDiffOn.div {f g : M -> G} {s : Set M} (hf : CMDiff[s] n f)
    (hg : CMDiff[s] n g) : CMDiff[s] n (fun x => f x / g x) := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
/--
theorem `ContMDiff.div` / 定理 `ContMDiff.div`

English:
theorem ContMDiff.div
  given: {f g : M -> G} (hf : CMDiff n f) (hg : CMDiff n g)
  proof: by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

中文:
定理 ContMDiff.div
  条件: {f g : M -> G} (hf : CMDiff n f) (hg : CMDiff n g)
  证明: by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv, simp_rw
-/
theorem ContMDiff.div {f g : M -> G} (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n fun x => f x / g x := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

end PointwiseDivision

/-! Binary product of Lie groups -/
section Product

-- Instance of product group
@[to_additive]
/--
Instance `Prod.instLieGroup` / 实例 `Prod.instLieGroup`

English:
instance Prod.instLieGroup
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  body: { ContMDiffMul.prod _ _ _ _ with contMDiff_inv := contMDiff_fst.inv.prodMk contMDiff_snd.inv }

中文:
实例 Prod.instLieGroup
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {n : 自然数∞ω}
  定义体: { ContMDiffMul.prod _ _ _ _ with contMDiff_inv := contMDiff_fst.inv.prodMk contMDiff_snd.inv }

Depends on / 依赖: ContMDiffMul, ContMDiffMul.prod, contMDiff_fst, contMDiff_fst.inv.prodMk, contMDiff_inv, contMDiff_snd, contMDiff_snd.inv, prodMk
-/
instance Prod.instLieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
    {H : Type*} [TopologicalSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
    [Group G'] [LieGroup I' n G'] : LieGroup (I.prod I') n (G × G') :=
  { ContMDiffMul.prod _ _ _ _ with contMDiff_inv := contMDiff_fst.inv.prodMk contMDiff_snd.inv }

end Product


/--
Instance `instNormedSpaceLieAddGroup` / 实例 `instNormedSpaceLieAddGroup`

English:
instance instNormedSpaceLieAddGroup
  signature: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  body: contDiff_neg.contMDiff

中文:
实例 instNormedSpaceLieAddGroup
  签名: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {n : 自然数∞ω}
  定义体: contDiff_neg.contMDiff

Depends on / 依赖: contDiff_neg, contDiff_neg.contMDiff, contMDiff
-/
instance instNormedSpaceLieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) n E where
  contMDiff_neg := contDiff_neg.contMDiff

/-! ## `C^n` manifolds with `C^n` inversion away from zero

Typeclass for `C^n` manifolds with `0` and `Inv` such that inversion is `C^n` at all non-zero
points. (This includes multiplicative Lie groups, but also complete normed semifields.)
Point-wise inversion is `C^n` when the function/denominator is non-zero. -/
section ContMDiffInv₀

-- See note [Design choices about smooth algebraic structures]
/--
Definition of `ContMDiffInv₀` / `ContMDiffInv₀` 的定义

English:
class ContMDiffInv₀
  parameters: {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
  axioms and operations (1):
    - contMDiffAt_inv₀ : forall ⦃x : G⦄, x != 0 -> CMDiffAt n (fun (y : G) => y⁻¹) x

中文:
类 ContMDiffInv₀
  参数: {𝕜 : 类型} [NontriviallyNormedField 𝕜] {H : 类型} [TopologicalSpace H]
  公理与运算 (1 个):
    - contMDiffAt_inv₀ : 对任意 ⦃x : G⦄, x != 0 -> CMDiffAt n (fun (y : G) => y⁻¹) x
-/
class ContMDiffInv₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : Nat∞ω) (G : Type*)
    [Inv G] [Zero G] [TopologicalSpace G] [ChartedSpace H G] : Prop where
  /-- Inversion is `C^n` away from `0`. -/
  contMDiffAt_inv₀ : forall ⦃x : G⦄, x != 0 -> CMDiffAt n (fun (y : G) => y⁻¹) x

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω} : ContMDiffInv₀ 𝓘(𝕜) n 𝕜 where
  contMDiffAt_inv₀ x hx := by
    change ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) n Inv.inv x
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_inv 𝕜 hx

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Inv G] [Zero G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f : M -> G}

/--
theorem `ContMDiffInv₀.of_le` / 定理 `ContMDiffInv₀.of_le`

English:
theorem ContMDiffInv₀.of_le
  statement: {m n : Nat∞ω} (hmn : m <= n)
  proof: by
  exact ⟨fun x hx => (h.contMDiffAt_inv₀ hx).of_le hmn⟩

中文:
定理 ContMDiffInv₀.of_le
  结论: {m n : 自然数∞ω} (hmn : m <= n)
  证明: by
  exact ⟨fun x hx => (h.contMDiffAt_inv₀ hx).of_le hmn⟩
-/
protected theorem ContMDiffInv₀.of_le {m n : Nat∞ω} (hmn : m <= n)
    [h : ContMDiffInv₀ I n G] : ContMDiffInv₀ I m G := by
  exact ⟨fun x hx => (h.contMDiffAt_inv₀ hx).of_le hmn⟩

instance {a : Nat∞ω} [ContMDiffInv₀ I ∞ G] [h : ENat.LEInfty a] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le h.out

instance {a : Nat∞ω} [ContMDiffInv₀ I ω G] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le le_top

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContinuousInv₀
  signature: G] : ContMDiffInv₀ I 0 G
  body: by
  have : T1Space G := I.t1Space G
  constructor
  have A : CMDiff[{0}ᶜ] 0 (fun (x : G) => x⁻¹) := by
    rw [contMDiffOn_zero_iff]
    exact continuousOn_inv₀
  intro x hx
  have : ContMDiffWithinAt I I 0 (fun (x : G) => x⁻¹) {0}ᶜ x := A x hx
  apply ContMDiffWithinAt.contMDiffAt this
  exact IsO

中文:
实例 [ContinuousInv₀
  签名: G] : ContMDiffInv₀ I 0 G
  定义体: by
  have : T1Space G := I.t1Space G
  constructor
  have A : CMDiff[{0}ᶜ] 0 (fun (x : G) => x⁻¹) := by
    rw [contMDiffOn_zero_iff]
    exact continuousOn_inv₀
  intro x hx
  have : ContMDiffWithinAt I I 0 (fun (x : G) => x⁻¹) {0}ᶜ x := A x hx
  apply ContMDiffWithinAt.contMDiffAt this
  exact IsO

Depends on / 依赖: CMDiff, ContMDiffWithinAt, ContMDiffWithinAt.contMDiffAt, I.t1Space, IsOpen, IsOpen.mem_nhds, T1Space, contMDiffAt, contMDiffOn_zero_iff, isOpen_compl_singleton, mem_nhds, t1Space
-/
instance [ContinuousInv₀ G] : ContMDiffInv₀ I 0 G := by
  have : T1Space G := I.t1Space G
  constructor
  have A : CMDiff[{0}ᶜ] 0 (fun (x : G) => x⁻¹) := by
    rw [contMDiffOn_zero_iff]
    exact continuousOn_inv₀
  intro x hx
  have : ContMDiffWithinAt I I 0 (fun (x : G) => x⁻¹) {0}ᶜ x := A x hx
  apply ContMDiffWithinAt.contMDiffAt this
  exact IsOpen.mem_nhds isOpen_compl_singleton hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ContMDiffInv₀
  signature: I 2 G] : ContMDiffInv₀ I 1 G
  body: ContMDiffInv₀.of_le one_le_two

中文:
实例 [ContMDiffInv₀
  签名: I 2 G] : ContMDiffInv₀ I 1 G
  定义体: ContMDiffInv₀.of_le one_le_two

Depends on / 依赖: of_le, one_le_two
-/
instance [ContMDiffInv₀ I 2 G] : ContMDiffInv₀ I 1 G :=
  ContMDiffInv₀.of_le one_le_two

variable [ContMDiffInv₀ I n G]

/--
theorem `contMDiffAt_inv₀` / 定理 `contMDiffAt_inv₀`

English:
theorem contMDiffAt_inv₀
  given: {x : G} (hx : x != 0)
  statement: ContMDiffAt I I n (fun y => y⁻¹) x
  proof: ContMDiffInv₀.contMDiffAt_inv₀ hx

include I n in

中文:
定理 contMDiffAt_inv₀
  条件: {x : G} (hx : x != 0)
  结论: ContMDiffAt I I n (fun y => y⁻¹) x
  证明: ContMDiffInv₀.contMDiffAt_inv₀ hx

include I n in
-/
theorem contMDiffAt_inv₀ {x : G} (hx : x != 0) : ContMDiffAt I I n (fun y => y⁻¹) x :=
  ContMDiffInv₀.contMDiffAt_inv₀ hx

include I n in
/--
theorem `continuousInv₀_of_contMDiffInv₀` / 定理 `continuousInv₀_of_contMDiffInv₀`

English:
theorem continuousInv₀_of_contMDiffInv₀
  statement: ContinuousInv₀ G
  proof: { continuousAt_inv₀ := fun _ hx => (contMDiffAt_inv₀ (I := I) (n := n) hx).continuousAt }

中文:
定理 continuousInv₀_of_contMDiffInv₀
  结论: ContinuousInv₀ G
  证明: { continuousAt_inv₀ := fun _ hx => (contMDiffAt_inv₀ (I := I) (n := n) hx).continuousAt }

Depends on / 依赖: continuousAt
-/
theorem continuousInv₀_of_contMDiffInv₀ : ContinuousInv₀ G :=
  { continuousAt_inv₀ := fun _ hx => (contMDiffAt_inv₀ (I := I) (n := n) hx).continuousAt }

/--
theorem `contMDiffOn_inv₀` / 定理 `contMDiffOn_inv₀`

English:
theorem contMDiffOn_inv₀
  statement: CMDiff[{0}ᶜ] n (Inv.inv : G -> G)
  proof: fun _x hx => (contMDiffAt_inv₀ hx).contMDiffWithinAt

中文:
定理 contMDiffOn_inv₀
  结论: CMDiff[{0}ᶜ] n (Inv.inv : G -> G)
  证明: fun _x hx => (contMDiffAt_inv₀ hx).contMDiffWithinAt

Depends on / 依赖: contMDiffWithinAt
-/
theorem contMDiffOn_inv₀ : CMDiff[{0}ᶜ] n (Inv.inv : G -> G) :=
  fun _x hx => (contMDiffAt_inv₀ hx).contMDiffWithinAt

variable {s : Set M} {a : M}

/--
theorem `ContMDiffWithinAt.inv₀` / 定理 `ContMDiffWithinAt.inv₀`

English:
theorem ContMDiffWithinAt.inv₀
  given: (hf : CMDiffAt[s] n f a) (ha : f a != 0)
  proof: (contMDiffAt_inv₀ ha).comp_contMDiffWithinAt a hf

中文:
定理 ContMDiffWithinAt.inv₀
  条件: (hf : CMDiffAt[s] n f a) (ha : f a != 0)
  证明: (contMDiffAt_inv₀ ha).comp_contMDiffWithinAt a hf

Depends on / 依赖: comp_contMDiffWithinAt
-/
theorem ContMDiffWithinAt.inv₀ (hf : CMDiffAt[s] n f a) (ha : f a != 0) :
    CMDiffAt[s] n (fun x => (f x)⁻¹) a :=
  (contMDiffAt_inv₀ ha).comp_contMDiffWithinAt a hf

/--
theorem `ContMDiffAt.inv₀` / 定理 `ContMDiffAt.inv₀`

English:
theorem ContMDiffAt.inv₀
  given: (hf : CMDiffAt n f a) (ha : f a != 0)
  statement: CMDiffAt n (fun x => (f x)⁻¹) a
  proof: (contMDiffAt_inv₀ ha).comp a hf

中文:
定理 ContMDiffAt.inv₀
  条件: (hf : CMDiffAt n f a) (ha : f a != 0)
  结论: CMDiffAt n (fun x => (f x)⁻¹) a
  证明: (contMDiffAt_inv₀ ha).comp a hf
-/
theorem ContMDiffAt.inv₀ (hf : CMDiffAt n f a) (ha : f a != 0) : CMDiffAt n (fun x => (f x)⁻¹) a :=
  (contMDiffAt_inv₀ ha).comp a hf

/--
theorem `ContMDiff.inv₀` / 定理 `ContMDiff.inv₀`

English:
theorem ContMDiff.inv₀
  given: (hf : CMDiff n f) (h0 : forall x, f x != 0)
  proof: fun x => ContMDiffAt.inv₀ (hf x) (h0 x)

中文:
定理 ContMDiff.inv₀
  条件: (hf : CMDiff n f) (h0 : 对任意 x, f x != 0)
  证明: fun x => ContMDiffAt.inv₀ (hf x) (h0 x)

Depends on / 依赖: ContMDiffAt, ContMDiffAt.inv
-/
theorem ContMDiff.inv₀ (hf : CMDiff n f) (h0 : forall x, f x != 0) :
    CMDiff n (fun x => (f x)⁻¹) :=
  fun x => ContMDiffAt.inv₀ (hf x) (h0 x)

/--
theorem `ContMDiffOn.inv₀` / 定理 `ContMDiffOn.inv₀`

English:
theorem ContMDiffOn.inv₀
  given: (hf : CMDiff[s] n f) (h0 : forall x in s, f x != 0)
  proof: fun x hx => ContMDiffWithinAt.inv₀ (hf x hx) (h0 x hx)

中文:
定理 ContMDiffOn.inv₀
  条件: (hf : CMDiff[s] n f) (h0 : 对任意 x in s, f x != 0)
  证明: fun x hx => ContMDiffWithinAt.inv₀ (hf x hx) (h0 x hx)

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.inv
-/
theorem ContMDiffOn.inv₀ (hf : CMDiff[s] n f) (h0 : forall x in s, f x != 0) :
    CMDiff[s] n (fun x => (f x)⁻¹) :=
  fun x hx => ContMDiffWithinAt.inv₀ (hf x hx) (h0 x hx)

end ContMDiffInv₀

/-! ### Point-wise division of `C^n` functions

If `[ContMDiffMul I n N]` and `[ContMDiffInv₀ I n N]`, point-wise division of `C^n`
functions `f : M → N` is `C^n` whenever the denominator is non-zero.
(This includes `N` being a completely normed field.)
-/
section Div

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Nat∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [GroupWithZero G] [ContMDiffInv₀ I n G]
  [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f g : M -> G} {s : Set M} {a : M}

/--
theorem `ContMDiffWithinAt.div₀` / 定理 `ContMDiffWithinAt.div₀`

English:
theorem ContMDiffWithinAt.div₀
  proof: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

中文:
定理 ContMDiffWithinAt.div₀
  证明: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem ContMDiffWithinAt.div₀
    (hf : CMDiffAt[s] n f a) (hg : CMDiffAt[s] n g a) (h₀ : g a != 0) : CMDiffAt[s] n (f / g) a := by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

/--
theorem `ContMDiffOn.div₀` / 定理 `ContMDiffOn.div₀`

English:
theorem ContMDiffOn.div₀
  statement: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  proof: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

中文:
定理 ContMDiffOn.div₀
  结论: (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
  证明: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem ContMDiffOn.div₀ (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
    (h₀ : forall x in s, g x != 0) : CMDiff[s] n (f / g) := by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

/--
theorem `ContMDiffAt.div₀` / 定理 `ContMDiffAt.div₀`

English:
theorem ContMDiffAt.div₀
  statement: (hf : CMDiffAt n f a) (hg : CMDiffAt n g a)
  proof: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

中文:
定理 ContMDiffAt.div₀
  结论: (hf : CMDiffAt n f a) (hg : CMDiffAt n g a)
  证明: by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem ContMDiffAt.div₀ (hf : CMDiffAt n f a) (hg : CMDiffAt n g a)
    (h₀ : g a != 0) : CMDiffAt n (f / g) a := by
  simpa [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

/--
theorem `ContMDiff.div₀` / 定理 `ContMDiff.div₀`

English:
theorem ContMDiff.div₀
  given: (hf : CMDiff n f) (hg : CMDiff n g) (h₀ : forall x, g x != 0)
  proof: by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

中文:
定理 ContMDiff.div₀
  条件: (hf : CMDiff n f) (hg : CMDiff n g) (h₀ : 对任意 x, g x != 0)
  证明: by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

Depends on / 依赖: div_eq_mul_inv, hf.mul, hg.inv
-/
theorem ContMDiff.div₀ (hf : CMDiff n f) (hg : CMDiff n g) (h₀ : forall x, g x != 0) :
    CMDiff n (f / g) := by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

end Div
