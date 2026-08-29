/-
Copyright (c) 2023 Yaël Dilies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dilies
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# L2 inner product of finite sequences

This file defines the weighted L2 inner product of functions `f g : ι → R` where `ι` is a fintype as
`∑ i, conj (f i) * g i`. This convention (conjugation on the left) matches the inner product coming
from `RCLike.innerProductSpace`.

## TODO

* Build a non-instance `InnerProductSpace` from `wInner`.
* `cWeight` is a poor name. Can we find better? It doesn't hugely matter for typing, since it's
  hidden behind the `⟪f, g⟫ₙ_[𝕝]` notation, but it does show up in lemma names
  `⟪f, g⟫_[𝕝, cWeight]` is called `wInner_cWeight`. Maybe we should introduce some naming
  convention, similarly to `MeasureTheory.average`?
-/

public section

open Finset Function WithLp
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

variable {ι κ 𝕜 : Type*} {E : ι -> Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜]

section Pi
variable [forall i, SeminormedAddCommGroup (E i)] [forall i, InnerProductSpace 𝕜 (E i)] {w : ι -> Real}

/--
Definition of `wInner` / `wInner` 的定义

English:
definition wInner
  signature: (w : ι -> Real) (f g : forall i, E i)
  body: ∑ i, w i • ⟪f i, g i⟫_𝕜

中文:
定义 wInner
  签名: (w : ι -> 实数) (f g : 对任意 i, E i)
  定义体: ∑ i, w i • ⟪f i, g i⟫_𝕜
-/
def wInner (w : ι -> Real) (f g : forall i, E i) : 𝕜 := ∑ i, w i • ⟪f i, g i⟫_𝕜

/--
Definition of `cWeight` / `cWeight` 的定义

English:
abbreviation cWeight
  signature: : ι -> Real
  body: Function.const _ (Fintype.card ι)⁻¹

@[inherit_doc wInner] notation3 "⟪" f ", " g "⟫_[" 𝕝 ", " w "]" => wInner (𝕜 := 𝕝) w f g

中文:
缩写 cWeight
  签名: : ι -> 实数
  定义体: Function.const _ (Fintype.card ι)⁻¹

@[inherit_doc wInner] notation3 "⟪" f ", " g "⟫_[" 𝕝 ", " w "]" => wInner (𝕜 := 𝕝) w f g

Depends on / 依赖: Fintype, Fintype.card, Function, Function.const
-/
noncomputable abbrev cWeight : ι -> Real := Function.const _ (Fintype.card ι)⁻¹

@[inherit_doc wInner] notation3 "⟪" f ", " g "⟫_[" 𝕝 ", " w "]" => wInner (𝕜 := 𝕝) w f g

/-- Discrete inner product giving rise to the discrete L2 norm. -/
notation3 "⟪" f ", " g "⟫_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, 1]

/-- Compact inner product giving rise to the compact L2 norm. -/
notation3 "⟪" f ", " g "⟫ₙ_[" 𝕝 "]" => ⟪f, g⟫_[𝕝, cWeight]

/--
lemma `wInner_cWeight_eq_smul_wInner_one` / 引理 `wInner_cWeight_eq_smul_wInner_one`

English:
lemma wInner_cWeight_eq_smul_wInner_one
  given: (f g : forall i, E i)
  proof: by
  simp [wInner, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

中文:
引理 wInner_cWeight_eq_smul_wInner_one
  条件: (f g : 对任意 i, E i)
  证明: by
  simp [wInner, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, smul_sum, wInner
-/
lemma wInner_cWeight_eq_smul_wInner_one (f g : forall i, E i) :
    ⟪f, g⟫ₙ_[𝕜] = (Fintype.card ι : Rat>=0)⁻¹ • ⟪f, g⟫_[𝕜] := by
  simp [wInner, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

/--
lemma `conj_wInner_symm` / 引理 `conj_wInner_symm`

English:
lemma conj_wInner_symm
  given: (w : ι -> Real) (f g : forall i, E i)
  proof: by
  simp [wInner, map_sum, inner_conj_symm, rclike_simps]

中文:
引理 conj_wInner_symm
  条件: (w : ι -> 实数) (f g : 对任意 i, E i)
  证明: by
  simp [wInner, map_sum, inner_conj_symm, rclike_simps]
-/
@[simp] lemma conj_wInner_symm (w : ι -> Real) (f g : forall i, E i) :
    conj ⟪f, g⟫_[𝕜, w] = ⟪g, f⟫_[𝕜, w] := by
  simp [wInner, map_sum, inner_conj_symm, rclike_simps]

/--
lemma `wInner_zero_left` / 引理 `wInner_zero_left`

English:
lemma wInner_zero_left
  given: (w : ι -> Real) (g : forall i, E i)
  statement: ⟪0, g⟫_[𝕜, w] = 0
  proof: by simp [wInner]

中文:
引理 wInner_zero_left
  条件: (w : ι -> 实数) (g : 对任意 i, E i)
  结论: ⟪0, g⟫_[𝕜, w] = 0
  证明: by simp [wInner]
-/
@[simp] lemma wInner_zero_left (w : ι -> Real) (g : forall i, E i) : ⟪0, g⟫_[𝕜, w] = 0 := by simp [wInner]
/--
lemma `wInner_zero_right` / 引理 `wInner_zero_right`

English:
lemma wInner_zero_right
  given: (w : ι -> Real) (f : forall i, E i)
  statement: ⟪f, 0⟫_[𝕜, w] = 0
  proof: by simp [wInner]

中文:
引理 wInner_zero_right
  条件: (w : ι -> 实数) (f : 对任意 i, E i)
  结论: ⟪f, 0⟫_[𝕜, w] = 0
  证明: by simp [wInner]
-/
@[simp] lemma wInner_zero_right (w : ι -> Real) (f : forall i, E i) : ⟪f, 0⟫_[𝕜, w] = 0 := by simp [wInner]

/--
lemma `wInner_add_left` / 引理 `wInner_add_left`

English:
lemma wInner_add_left
  given: (w : ι -> Real) (f₁ f₂ g : forall i, E i)
  proof: by
  simp [wInner, inner_add_left, smul_add, sum_add_distrib]

中文:
引理 wInner_add_left
  条件: (w : ι -> 实数) (f₁ f₂ g : 对任意 i, E i)
  证明: by
  simp [wInner, inner_add_left, smul_add, sum_add_distrib]

Depends on / 依赖: inner_add_left, smul_add, sum_add_distrib, wInner
-/
lemma wInner_add_left (w : ι -> Real) (f₁ f₂ g : forall i, E i) :
    ⟪f₁ + f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] + ⟪f₂, g⟫_[𝕜, w] := by
  simp [wInner, inner_add_left, smul_add, sum_add_distrib]

/--
lemma `wInner_add_right` / 引理 `wInner_add_right`

English:
lemma wInner_add_right
  given: (w : ι -> Real) (f g₁ g₂ : forall i, E i)
  proof: by
  simp [wInner, inner_add_right, smul_add, sum_add_distrib]

中文:
引理 wInner_add_right
  条件: (w : ι -> 实数) (f g₁ g₂ : 对任意 i, E i)
  证明: by
  simp [wInner, inner_add_right, smul_add, sum_add_distrib]

Depends on / 依赖: inner_add_right, smul_add, sum_add_distrib, wInner
-/
lemma wInner_add_right (w : ι -> Real) (f g₁ g₂ : forall i, E i) :
    ⟪f, g₁ + g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] + ⟪f, g₂⟫_[𝕜, w] := by
  simp [wInner, inner_add_right, smul_add, sum_add_distrib]

/--
lemma `wInner_neg_left` / 引理 `wInner_neg_left`

English:
lemma wInner_neg_left
  given: (w : ι -> Real) (f g : forall i, E i)
  statement: ⟪-f, g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w]
  proof: by
  simp [wInner]

中文:
引理 wInner_neg_left
  条件: (w : ι -> 实数) (f g : 对任意 i, E i)
  结论: ⟪-f, g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w]
  证明: by
  simp [wInner]
-/
@[simp] lemma wInner_neg_left (w : ι -> Real) (f g : forall i, E i) : ⟪-f, g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]

/--
lemma `wInner_neg_right` / 引理 `wInner_neg_right`

English:
lemma wInner_neg_right
  given: (w : ι -> Real) (f g : forall i, E i)
  statement: ⟪f, -g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w]
  proof: by
  simp [wInner]

中文:
引理 wInner_neg_right
  条件: (w : ι -> 实数) (f g : 对任意 i, E i)
  结论: ⟪f, -g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w]
  证明: by
  simp [wInner]
-/
@[simp] lemma wInner_neg_right (w : ι -> Real) (f g : forall i, E i) : ⟪f, -g⟫_[𝕜, w] = -⟪f, g⟫_[𝕜, w] := by
  simp [wInner]

/--
lemma `wInner_sub_left` / 引理 `wInner_sub_left`

English:
lemma wInner_sub_left
  given: (w : ι -> Real) (f₁ f₂ g : forall i, E i)
  proof: by
  simp_rw [sub_eq_add_neg, wInner_add_left, wInner_neg_left]

中文:
引理 wInner_sub_left
  条件: (w : ι -> 实数) (f₁ f₂ g : 对任意 i, E i)
  证明: by
  simp_rw [sub_eq_add_neg, wInner_add_left, wInner_neg_left]

Depends on / 依赖: simp_rw, sub_eq_add_neg, wInner_add_left, wInner_neg_left
-/
lemma wInner_sub_left (w : ι -> Real) (f₁ f₂ g : forall i, E i) :
    ⟪f₁ - f₂, g⟫_[𝕜, w] = ⟪f₁, g⟫_[𝕜, w] - ⟪f₂, g⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_left, wInner_neg_left]

/--
lemma `wInner_sub_right` / 引理 `wInner_sub_right`

English:
lemma wInner_sub_right
  given: (w : ι -> Real) (f g₁ g₂ : forall i, E i)
  proof: by
  simp_rw [sub_eq_add_neg, wInner_add_right, wInner_neg_right]

中文:
引理 wInner_sub_right
  条件: (w : ι -> 实数) (f g₁ g₂ : 对任意 i, E i)
  证明: by
  simp_rw [sub_eq_add_neg, wInner_add_right, wInner_neg_right]

Depends on / 依赖: simp_rw, sub_eq_add_neg, wInner_add_right, wInner_neg_right
-/
lemma wInner_sub_right (w : ι -> Real) (f g₁ g₂ : forall i, E i) :
    ⟪f, g₁ - g₂⟫_[𝕜, w] = ⟪f, g₁⟫_[𝕜, w] - ⟪f, g₂⟫_[𝕜, w] := by
  simp_rw [sub_eq_add_neg, wInner_add_right, wInner_neg_right]

/--
lemma `wInner_of_isEmpty` / 引理 `wInner_of_isEmpty`

English:
lemma wInner_of_isEmpty
  given: [IsEmpty ι] (w : ι -> Real) (f g : forall i, E i)
  statement: ⟪f, g⟫_[𝕜, w] = 0
  proof: by
  simp [Subsingleton.elim f 0]

中文:
引理 wInner_of_isEmpty
  条件: [IsEmpty ι] (w : ι -> 实数) (f g : 对任意 i, E i)
  结论: ⟪f, g⟫_[𝕜, w] = 0
  证明: by
  simp [Subsingleton.elim f 0]
-/
@[simp] lemma wInner_of_isEmpty [IsEmpty ι] (w : ι -> Real) (f g : forall i, E i) : ⟪f, g⟫_[𝕜, w] = 0 := by
  simp [Subsingleton.elim f 0]

/--
lemma `wInner_smul_left` / 引理 `wInner_smul_left`

English:
lemma wInner_smul_left
  statement: {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
  proof: by
  simp_rw [wInner, Pi.smul_apply, inner_smul_left_eq_star_smul, starRingEnd_apply, smul_sum,
    smul_comm (w _)]

中文:
引理 wInner_smul_left
  结论: {𝕝 : 类型} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
  证明: by
  simp_rw [wInner, Pi.smul_apply, inner_smul_left_eq_star_smul, starRingEnd_apply, smul_sum,
    smul_comm (w _)]

Depends on / 依赖: Pi.smul_apply, inner_smul_left_eq_star_smul, simp_rw, smul_apply, smul_comm, smul_sum, starRingEnd_apply, wInner
-/
lemma wInner_smul_left {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [SMulCommClass Real 𝕝 𝕜] [forall i, Module 𝕝 (E i)] [forall i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι -> Real) (f g : forall i, E i) : ⟪c • f, g⟫_[𝕜, w] = star c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_left_eq_star_smul, starRingEnd_apply, smul_sum,
    smul_comm (w _)]

/--
lemma `wInner_smul_right` / 引理 `wInner_smul_right`

English:
lemma wInner_smul_right
  statement: {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
  proof: by
  simp_rw [wInner, Pi.smul_apply, inner_smul_right_eq_smul, smul_sum, smul_comm c]

中文:
引理 wInner_smul_right
  结论: {𝕝 : 类型} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
  证明: by
  simp_rw [wInner, Pi.smul_apply, inner_smul_right_eq_smul, smul_sum, smul_comm c]

Depends on / 依赖: Pi.smul_apply, inner_smul_right_eq_smul, simp_rw, smul_apply, smul_comm, smul_sum, wInner
-/
lemma wInner_smul_right {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [StarModule 𝕝 𝕜]
    [forall i, Module 𝕝 (E i)] [forall i, IsScalarTower 𝕝 𝕜 (E i)] (c : 𝕝)
    (w : ι -> Real) (f g : forall i, E i) : ⟪f, c • g⟫_[𝕜, w] = c • ⟪f, g⟫_[𝕜, w] := by
  simp_rw [wInner, Pi.smul_apply, inner_smul_right_eq_smul, smul_sum, smul_comm c]

/--
lemma `mul_wInner_left` / 引理 `mul_wInner_left`

English:
lemma mul_wInner_left
  given: (c : 𝕜) (w : ι -> Real) (f g : forall i, E i)
  proof: by rw [wInner_smul_left, star_star, smul_eq_mul]

中文:
引理 mul_wInner_left
  条件: (c : 𝕜) (w : ι -> 实数) (f g : 对任意 i, E i)
  证明: by rw [wInner_smul_left, star_star, smul_eq_mul]

Depends on / 依赖: smul_eq_mul, star_star, wInner_smul_left
-/
lemma mul_wInner_left (c : 𝕜) (w : ι -> Real) (f g : forall i, E i) :
    c * ⟪f, g⟫_[𝕜, w] = ⟪star c • f, g⟫_[𝕜, w] := by rw [wInner_smul_left, star_star, smul_eq_mul]

/--
lemma `wInner_one_eq_sum` / 引理 `wInner_one_eq_sum`

English:
lemma wInner_one_eq_sum
  given: (f g : forall i, E i)
  statement: ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜
  proof: by simp [wInner]

中文:
引理 wInner_one_eq_sum
  条件: (f g : 对任意 i, E i)
  结论: ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜
  证明: by simp [wInner]

Depends on / 依赖: wInner
-/
lemma wInner_one_eq_sum (f g : forall i, E i) : ⟪f, g⟫_[𝕜] = ∑ i, ⟪f i, g i⟫_𝕜 := by simp [wInner]
/--
lemma `wInner_cWeight_eq_expect` / 引理 `wInner_cWeight_eq_expect`

English:
lemma wInner_cWeight_eq_expect
  given: (f g : forall i, E i)
  statement: ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
  proof: by
  simp [wInner, expect, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

中文:
引理 wInner_cWeight_eq_expect
  条件: (f g : 对任意 i, E i)
  结论: ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜
  证明: by
  simp [wInner, expect, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, expect, smul_sum, wInner
-/
lemma wInner_cWeight_eq_expect (f g : forall i, E i) : ⟪f, g⟫ₙ_[𝕜] = 𝔼 i, ⟪f i, g i⟫_𝕜 := by
  simp [wInner, expect, smul_sum, ← NNRat.cast_smul_eq_nnqsmul Real]

end Pi

section Function
variable {w : ι -> Real} {f g : ι -> 𝕜}

/--
lemma `wInner_const_left` / 引理 `wInner_const_left`

English:
lemma wInner_const_left
  given: (a : 𝕜) (f : ι -> 𝕜)
  proof: by simp [wInner, const_apply, sum_mul]

中文:
引理 wInner_const_left
  条件: (a : 𝕜) (f : ι -> 𝕜)
  证明: by simp [wInner, const_apply, sum_mul]

Depends on / 依赖: const_apply, sum_mul, wInner
-/
lemma wInner_const_left (a : 𝕜) (f : ι -> 𝕜) :
    ⟪const _ a, f⟫_[𝕜, w] = (∑ i, w i • f i) * conj a := by simp [wInner, const_apply, sum_mul]

/--
lemma `wInner_const_right` / 引理 `wInner_const_right`

English:
lemma wInner_const_right
  given: (f : ι -> 𝕜) (a : 𝕜)
  proof: by simp [wInner, const_apply, mul_sum]

中文:
引理 wInner_const_right
  条件: (f : ι -> 𝕜) (a : 𝕜)
  证明: by simp [wInner, const_apply, mul_sum]

Depends on / 依赖: const_apply, mul_sum, wInner
-/
lemma wInner_const_right (f : ι -> 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜, w] = a * (∑ i, w i • conj (f i)) := by simp [wInner, const_apply, mul_sum]

/--
lemma `wInner_one_const_left` / 引理 `wInner_one_const_left`

English:
lemma wInner_one_const_left
  given: (a : 𝕜) (f : ι -> 𝕜)
  proof: by simp [wInner_one_eq_sum, sum_mul]

中文:
引理 wInner_one_const_left
  条件: (a : 𝕜) (f : ι -> 𝕜)
  证明: by simp [wInner_one_eq_sum, sum_mul]
-/
@[simp] lemma wInner_one_const_left (a : 𝕜) (f : ι -> 𝕜) :
    ⟪const _ a, f⟫_[𝕜] = (∑ i, f i) * conj a := by simp [wInner_one_eq_sum, sum_mul]

/--
lemma `wInner_one_const_right` / 引理 `wInner_one_const_right`

English:
lemma wInner_one_const_right
  given: (f : ι -> 𝕜) (a : 𝕜)
  proof: by simp [wInner_one_eq_sum, mul_sum]

中文:
引理 wInner_one_const_right
  条件: (f : ι -> 𝕜) (a : 𝕜)
  证明: by simp [wInner_one_eq_sum, mul_sum]
-/
@[simp] lemma wInner_one_const_right (f : ι -> 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫_[𝕜] = a * (∑ i, conj (f i)) := by simp [wInner_one_eq_sum, mul_sum]

/--
lemma `wInner_cWeight_const_left` / 引理 `wInner_cWeight_const_left`

English:
lemma wInner_cWeight_const_left
  given: (a : 𝕜) (f : ι -> 𝕜)
  proof: by simp [wInner_cWeight_eq_expect]

中文:
引理 wInner_cWeight_const_left
  条件: (a : 𝕜) (f : ι -> 𝕜)
  证明: by simp [wInner_cWeight_eq_expect]
-/
@[simp] lemma wInner_cWeight_const_left (a : 𝕜) (f : ι -> 𝕜) :
    ⟪const _ a, f⟫ₙ_[𝕜] = 𝔼 i, f i * conj a := by simp [wInner_cWeight_eq_expect]

/--
lemma `wInner_cWeight_const_right` / 引理 `wInner_cWeight_const_right`

English:
lemma wInner_cWeight_const_right
  given: (f : ι -> 𝕜) (a : 𝕜)
  proof: by simp [wInner_cWeight_eq_expect, mul_expect]

中文:
引理 wInner_cWeight_const_right
  条件: (f : ι -> 𝕜) (a : 𝕜)
  证明: by simp [wInner_cWeight_eq_expect, mul_expect]
-/
@[simp] lemma wInner_cWeight_const_right (f : ι -> 𝕜) (a : 𝕜) :
    ⟪f, const _ a⟫ₙ_[𝕜] = a * (𝔼 i, conj (f i)) := by simp [wInner_cWeight_eq_expect, mul_expect]

/--
lemma `wInner_one_eq_inner` / 引理 `wInner_one_eq_inner`

English:
lemma wInner_one_eq_inner
  given: (f g : ι -> 𝕜)
  proof: by
  simp [PiLp.inner_apply, wInner]

中文:
引理 wInner_one_eq_inner
  条件: (f g : ι -> 𝕜)
  证明: by
  simp [PiLp.inner_apply, wInner]

Depends on / 依赖: PiLp.inner_apply, inner_apply, wInner
-/
lemma wInner_one_eq_inner (f g : ι -> 𝕜) :
    ⟪f, g⟫_[𝕜, 1] = ⟪toLp 2 f, toLp 2 g⟫_𝕜 := by
  simp [PiLp.inner_apply, wInner]

/--
lemma `inner_eq_wInner_one` / 引理 `inner_eq_wInner_one`

English:
lemma inner_eq_wInner_one
  given: (f g : PiLp 2 fun _i : ι => 𝕜)
  proof: by
  simp [PiLp.inner_apply, wInner]

中文:
引理 inner_eq_wInner_one
  条件: (f g : PiLp 2 fun _i : ι => 𝕜)
  证明: by
  simp [PiLp.inner_apply, wInner]

Depends on / 依赖: PiLp.inner_apply, inner_apply, wInner
-/
lemma inner_eq_wInner_one (f g : PiLp 2 fun _i : ι => 𝕜) :
    ⟪f, g⟫_𝕜 = ⟪ofLp f, ofLp g⟫_[𝕜, 1] := by
  simp [PiLp.inner_apply, wInner]

/--
lemma `linearIndependent_of_ne_zero_of_wInner_one_eq_zero` / 引理 `linearIndependent_of_ne_zero_of_wInner_one_eq_zero`

English:
lemma linearIndependent_of_ne_zero_of_wInner_one_eq_zero
  statement: {f : κ -> ι -> 𝕜} (hf : forall k, f k != 0)
  proof: by
  simp_rw [wInner_one_eq_inner] at hinner
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ hinner
  exacts [(WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm.toLinearMap.linearIndependent_iff_of_injOn
.1 this, fun i => (toLp_eq_zero 2).ne.2 (hf i)] (toLp_injective 2).injOn

中文:
引理 linearIndependent_of_ne_zero_of_wInner_one_eq_zero
  结论: {f : κ -> ι -> 𝕜} (hf : 对任意 k, f k != 0)
  证明: by
  simp_rw [wInner_one_eq_inner] at hinner
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ hinner
  exacts [(WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm.toLinearMap.linearIndependent_iff_of_injOn
.1 this, fun i => (toLp_eq_zero 2).ne.2 (hf i)] (toLp_injective 2).injOn

Depends on / 依赖: WithLp, WithLp.linearEquiv, exacts, hinner, linearEquiv, linearIndependent_iff_of_injOn, linearIndependent_of_ne_zero_of_inner_eq_zero, simp_rw, symm.toLinearMap.linearIndependent_iff_of_injOn, toLinearMap, toLp_eq_zero, toLp_injective, wInner_one_eq_inner
-/
lemma linearIndependent_of_ne_zero_of_wInner_one_eq_zero {f : κ -> ι -> 𝕜} (hf : forall k, f k != 0)
    (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  simp_rw [wInner_one_eq_inner] at hinner
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ hinner
  exacts [(WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm.toLinearMap.linearIndependent_iff_of_injOn
.1 this, fun i => (toLp_eq_zero 2).ne.2 (hf i)] (toLp_injective 2).injOn

/--
lemma `linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero` / 引理 `linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero`

English:
lemma linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero
  statement: {f : κ -> ι -> 𝕜} (hf : forall k, f k != 0)
  proof: by
  cases isEmpty_or_nonempty ι
· have : IsEmpty κ := ⟨fun k => hf k Subsingleton.elim ..⟩
    exact linearIndependent_empty_type
· exact linearIndependent_of_ne_zero_of_wInner_one_eq_zero hf by
      simpa [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul 𝕜] using hinner

中文:
引理 linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero
  结论: {f : κ -> ι -> 𝕜} (hf : 对任意 k, f k != 0)
  证明: by
  cases isEmpty_or_nonempty ι
· have : IsEmpty κ := ⟨fun k => hf k Subsingleton.elim ..⟩
    exact linearIndependent_empty_type
· exact linearIndependent_of_ne_zero_of_wInner_one_eq_zero hf by
      simpa [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul 𝕜] using hinner

Depends on / 依赖: IsEmpty, NNRat.cast_smul_eq_nnqsmul, Subsingleton, Subsingleton.elim, cast_smul_eq_nnqsmul, hinner, isEmpty_or_nonempty, linearIndependent_empty_type, linearIndependent_of_ne_zero_of_wInner_one_eq_zero, wInner_cWeight_eq_smul_wInner_one
-/
lemma linearIndependent_of_ne_zero_of_wInner_cWeight_eq_zero {f : κ -> ι -> 𝕜} (hf : forall k, f k != 0)
    (hinner : Pairwise fun k₁ k₂ => ⟪f k₁, f k₂⟫ₙ_[𝕜] = 0) : LinearIndependent 𝕜 f := by
  cases isEmpty_or_nonempty ι
· have : IsEmpty κ := ⟨fun k => hf k Subsingleton.elim ..⟩
    exact linearIndependent_empty_type
· exact linearIndependent_of_ne_zero_of_wInner_one_eq_zero hf by
      simpa [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul 𝕜] using hinner

/--
lemma `wInner_nonneg` / 引理 `wInner_nonneg`

English:
lemma wInner_nonneg
  given: (hw : 0 <= w) (hf : 0 <= f) (hg : 0 <= g)
  statement: 0 <= ⟪f, g⟫_[𝕜, w]
  proof: sum_nonneg fun _ _ => smul_nonneg (hw _) mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))

中文:
引理 wInner_nonneg
  条件: (hw : 0 <= w) (hf : 0 <= f) (hg : 0 <= g)
  结论: 0 <= ⟪f, g⟫_[𝕜, w]
  证明: sum_nonneg fun _ _ => smul_nonneg (hw _) mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))

Depends on / 依赖: mul_nonneg, smul_nonneg, star_nonneg_iff, sum_nonneg
-/
lemma wInner_nonneg (hw : 0 <= w) (hf : 0 <= f) (hg : 0 <= g) : 0 <= ⟪f, g⟫_[𝕜, w] :=
sum_nonneg fun _ _ => smul_nonneg (hw _) mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))

/--
lemma `norm_wInner_le` / 引理 `norm_wInner_le`

English:
lemma norm_wInner_le
  given: (hw : 0 <= w)
  statement: ‖⟪f, g⟫_[𝕜, w]‖ <= ⟪fun i => ‖f i‖, fun i => ‖g i‖⟫_[Real, w]
  proof: (norm_sum_le ..).trans_eq sum_congr rfl fun i _ => by
    simp [Algebra.smul_def, norm_mul, abs_of_nonneg (hw i)]

中文:
引理 norm_wInner_le
  条件: (hw : 0 <= w)
  结论: ‖⟪f, g⟫_[𝕜, w]‖ <= ⟪fun i => ‖f i‖, fun i => ‖g i‖⟫_[实数, w]
  证明: (norm_sum_le ..).trans_eq sum_congr rfl fun i _ => by
    simp [Algebra.smul_def, norm_mul, abs_of_nonneg (hw i)]

Depends on / 依赖: Algebra, Algebra.smul_def, abs_of_nonneg, norm_mul, norm_sum_le, smul_def, sum_congr, trans_eq
-/
lemma norm_wInner_le (hw : 0 <= w) : ‖⟪f, g⟫_[𝕜, w]‖ <= ⟪fun i => ‖f i‖, fun i => ‖g i‖⟫_[Real, w] :=
(norm_sum_le ..).trans_eq sum_congr rfl fun i _ => by
    simp [Algebra.smul_def, norm_mul, abs_of_nonneg (hw i)]

end Function

section Real
variable {w f g : ι -> Real}

/--
lemma `abs_wInner_le` / 引理 `abs_wInner_le`

English:
lemma abs_wInner_le
  given: (hw : 0 <= w)
  statement: |⟪f, g⟫_[Real, w]| <= ⟪|f|, |g|⟫_[Real, w]
  proof: by
  simpa using! norm_wInner_le (𝕜 := Real) hw

中文:
引理 abs_wInner_le
  条件: (hw : 0 <= w)
  结论: |⟪f, g⟫_[实数, w]| <= ⟪|f|, |g|⟫_[实数, w]
  证明: by
  simpa using! norm_wInner_le (𝕜 := Real) hw

Depends on / 依赖: norm_wInner_le
-/
lemma abs_wInner_le (hw : 0 <= w) : |⟪f, g⟫_[Real, w]| <= ⟪|f|, |g|⟫_[Real, w] := by
  simpa using! norm_wInner_le (𝕜 := Real) hw

end Real
end RCLike
