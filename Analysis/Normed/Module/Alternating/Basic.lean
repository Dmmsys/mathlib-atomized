/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, Heather Macbeth, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Operator norm on the space of continuous alternating maps

In this file we show that continuous alternating maps
from a seminormed space to a (semi)normed space form a (semi)normed space.
We also prove basic facts about this norm
and define bundled versions of some operations on continuous alternating maps.

Most proofs just invoke the corresponding fact about continuous multilinear maps.
-/

@[expose] public section

noncomputable section

open scoped NNReal
open Finset Metric

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a nontrivially normed field;
* `ι`: a finite index type;
* `E`, `F`, `G`: (semi)normed vector spaces over `𝕜`.
-/

/--
Instance `ContinuousAlternatingMap.instContinuousEval` / 实例 `ContinuousAlternatingMap.instContinuousEval`

English:
instance ContinuousAlternatingMap.instContinuousEval
  signature: {𝕜 ι E F : Type*}
  body: .of_continuous_forget continuous_toContinuousMultilinearMap

中文:
实例 余ntinuousAlternating映射.instContinuousEval
  签名: {𝕜 ι E F : 类型}
  定义体: .of_continuous_forget continuous_toContinuousMultilinearMap

Depends on / 依赖: continuous_toContinuousMultilinearMap, of_continuous_forget
-/
instance ContinuousAlternatingMap.instContinuousEval {𝕜 ι E F : Type*}
    [NormedField 𝕜] [Finite ι] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F] :
    ContinuousEval (E [⋀^ι]->L[𝕜] F) (ι -> E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap

section Seminorm

universe u wE wF wG v
variable {𝕜 : Type u} {n : Nat} {E : Type wE} {F : Type wF} {G : Type wG} {ι : Type v}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-!
### Continuity properties of alternating maps

We relate continuity of alternating maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/
namespace AlternatingMap

/--
theorem `norm_map_coord_zero` / 定理 `norm_map_coord_zero`

English:
theorem norm_map_coord_zero
  statement: (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f)
  proof: f.1.norm_map_coord_zero hf hi

中文:
定理 norm_map_coord_zero
  结论: (f : E [⋀^ι]->ₗ[𝕜] F) (hf : 连续 f)
  证明: f.1.norm_map_coord_zero hf hi

Depends on / 依赖: norm_map_coord_zero
-/
theorem norm_map_coord_zero (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f)
    {m : ι -> E} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 :=
  f.1.norm_map_coord_zero hf hi

variable [Fintype ι]

/--
theorem `bound_of_shell_of_norm_map_coord_zero` / 定理 `bound_of_shell_of_norm_map_coord_zero`

English:
theorem bound_of_shell_of_norm_map_coord_zero
  statement: (f : E [⋀^ι]->ₗ[𝕜] F)
  proof: f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

中文:
定理 bound_of_shell_of_norm_map_coord_zero
  结论: (f : E [⋀^ι]->ₗ[𝕜] F)
  证明: f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

Depends on / 依赖: bound_of_shell_of_norm_map_coord_zero
-/
theorem bound_of_shell_of_norm_map_coord_zero (f : E [⋀^ι]->ₗ[𝕜] F)
    (hf₀ : forall {m i}, ‖m i‖ = 0 -> ‖f m‖ = 0)
    {ε : ι -> Real} {C : Real} (hε : forall i, 0 < ε i) {c : ι -> 𝕜} (hc : forall i, 1 < ‖c i‖)
    (hf : forall m : ι -> E, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : ι -> E) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

/--
theorem `bound_of_shell_of_continuous` / 定理 `bound_of_shell_of_continuous`

English:
theorem bound_of_shell_of_continuous
  statement: (f : E [⋀^ι]->ₗ[𝕜] F) (hfc : Continuous f)
  proof: f.1.bound_of_shell_of_continuous hfc (fun _ => hε) (fun _ => hc) hf m

中文:
定理 bound_of_shell_of_continuous
  结论: (f : E [⋀^ι]->ₗ[𝕜] F) (hfc : 连续 f)
  证明: f.1.bound_of_shell_of_continuous hfc (fun _ => hε) (fun _ => hc) hf m

Depends on / 依赖: bound_of_shell_of_continuous
-/
theorem bound_of_shell_of_continuous (f : E [⋀^ι]->ₗ[𝕜] F) (hfc : Continuous f)
    {ε : Real} {C : Real} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : forall m : ι -> E, (forall i, ε / ‖c‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : ι -> E) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_continuous hfc (fun _ => hε) (fun _ => hc) hf m

/--
theorem `exists_bound_of_continuous` / 定理 `exists_bound_of_continuous`

English:
theorem exists_bound_of_continuous
  given: (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f)
  proof: f.1.exists_bound_of_continuous hf

中文:
定理 存在_bound_of_continuous
  条件: (f : E [⋀^ι]->ₗ[𝕜] F) (hf : 连续 f)
  证明: f.1.exists_bound_of_continuous hf

Depends on / 依赖: exists_bound_of_continuous
-/
theorem exists_bound_of_continuous (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f) :
    exists (C : Real), 0 < C ∧ (forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :=
  f.1.exists_bound_of_continuous hf

/--
theorem `norm_image_sub_le_of_bound'` / 定理 `norm_image_sub_le_of_bound'`

English:
theorem norm_image_sub_le_of_bound'
  statement: [DecidableEq ι] (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
  proof: f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

中文:
定理 norm_image_sub_le_of_bound'
  结论: [DecidableEq ι] (f : E [⋀^ι]->ₗ[𝕜] F) {C : 实数} (hC : 0 <= C)
  证明: f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

Depends on / 依赖: f.toMultilinearMap.norm_image_sub_le_of_bound, norm_image_sub_le_of_bound, toMultilinearMap
-/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : ι -> E) :
    ‖f m₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

/--
theorem `norm_image_sub_le_of_bound` / 定理 `norm_image_sub_le_of_bound`

English:
theorem norm_image_sub_le_of_bound
  statement: (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
  proof: f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

中文:
定理 norm_image_sub_le_of_bound
  结论: (f : E [⋀^ι]->ₗ[𝕜] F) {C : 实数} (hC : 0 <= C)
  证明: f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

Depends on / 依赖: f.toMultilinearMap.norm_image_sub_le_of_bound, norm_image_sub_le_of_bound, toMultilinearMap
-/
theorem norm_image_sub_le_of_bound (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : ι -> E) :
    ‖f m₁ - f m₂‖ <= C * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

/--
theorem `continuous_of_bound` / 定理 `continuous_of_bound`

English:
theorem continuous_of_bound
  given: (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  proof: f.toMultilinearMap.continuous_of_bound C H

中文:
定理 continuous_of_bound
  条件: (f : E [⋀^ι]->ₗ[𝕜] F) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  证明: f.toMultilinearMap.continuous_of_bound C H

Depends on / 依赖: continuous_of_bound, f.toMultilinearMap.continuous_of_bound, toMultilinearMap
-/
theorem continuous_of_bound (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :
    Continuous f :=
  f.toMultilinearMap.continuous_of_bound C H

/--
Definition of `mkContinuous` / `mkContinuous` 的定义

English:
definition mkContinuous
  signature: (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  body: { f with cont := f.continuous_of_bound C H }

中文:
定义 mkContinuous
  签名: (f : E [⋀^ι]->ₗ[𝕜] F) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  定义体: { f with cont := f.continuous_of_bound C H }

Depends on / 依赖: continuous_of_bound, f.continuous_of_bound
-/
def mkContinuous (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : E [⋀^ι]->L[𝕜] F :=
  { f with cont := f.continuous_of_bound C H }

/--
theorem `coe_mkContinuous` / 定理 `coe_mkContinuous`

English:
theorem coe_mkContinuous
  given: (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  proof: rfl

中文:
定理 coe_mkContinuous
  条件: (f : E [⋀^ι]->ₗ[𝕜] F) (C : 实数) (H : 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  证明: rfl
-/
@[simp] theorem coe_mkContinuous (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :
    (f.mkContinuous C H : (ι -> E) -> F) = f :=
  rfl

end AlternatingMap

/-!
### Continuous alternating maps

We define the norm `‖f‖` of a continuous alternating map `f` in finitely many variables
as the smallest nonnegative number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.
We show that this defines a normed space structure on `E [⋀^ι]→L[𝕜] F`.
-/

namespace ContinuousAlternatingMap

variable [Fintype ι] {f : E [⋀^ι]->L[𝕜] F} {m : ι -> E}

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  given: (f : E [⋀^ι]->L[𝕜] F)
  statement: exists (C : Real), 0 < C ∧ (forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  proof: f.toContinuousMultilinearMap.bound

中文:
定理 bound
  条件: (f : E [⋀^ι]->L[𝕜] F)
  结论: 存在 (C : 实数), 0 < C ∧ (对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖)
  证明: f.toContinuousMultilinearMap.bound

Depends on / 依赖: f.toContinuousMultilinearMap.bound, toContinuousMultilinearMap
-/
theorem bound (f : E [⋀^ι]->L[𝕜] F) : exists (C : Real), 0 < C ∧ (forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) :=
  f.toContinuousMultilinearMap.bound

/--
Instance `instSeminormedAddCommGroup` / 实例 `instSeminormedAddCommGroup`

English:
instance instSeminormedAddCommGroup
  signature: : SeminormedAddCommGroup (E [⋀^ι]->L[𝕜] F) where
  body: .induced toContinuousMultilinearMap inferInstance
  __ := SeminormedAddCommGroup.induced _ _ (toMultilinearAddHom : E [⋀^ι]->L[𝕜] F ->+ _)
  norm f := ‖f.toContinuousMultilinearMap‖

中文:
实例 instSeminormedAddCommGroup
  签名: : SeminormedAddComm群 (E [⋀^ι]->L[𝕜] F) where
  定义体: .induced toContinuousMultilinearMap inferInstance
  __ := SeminormedAddCommGroup.induced _ _ (toMultilinearAddHom : E [⋀^ι]->L[𝕜] F ->+ _)
  norm f := ‖f.toContinuousMultilinearMap‖

Depends on / 依赖: induced, toContinuousMultilinearMap
-/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (E [⋀^ι]->L[𝕜] F) where
  toPseudoMetricSpace := .induced toContinuousMultilinearMap inferInstance
  __ := SeminormedAddCommGroup.induced _ _ (toMultilinearAddHom : E [⋀^ι]->L[𝕜] F ->+ _)
  norm f := ‖f.toContinuousMultilinearMap‖

/--
theorem `norm_toContinuousMultilinearMap` / 定理 `norm_toContinuousMultilinearMap`

English:
theorem norm_toContinuousMultilinearMap
  given: (f : E [⋀^ι]->L[𝕜] F)
  statement: ‖f.1‖ = ‖f‖
  proof: rfl

中文:
定理 norm_toContinuousMultilinearMap
  条件: (f : E [⋀^ι]->L[𝕜] F)
  结论: ‖f.1‖ = ‖f‖
  证明: rfl
-/
@[simp] theorem norm_toContinuousMultilinearMap (f : E [⋀^ι]->L[𝕜] F) : ‖f.1‖ = ‖f‖ := rfl
/--
theorem `nnnorm_toContinuousMultilinearMap` / 定理 `nnnorm_toContinuousMultilinearMap`

English:
theorem nnnorm_toContinuousMultilinearMap
  given: (f : E [⋀^ι]->L[𝕜] F)
  statement: ‖f.1‖₊ = ‖f‖₊
  proof: rfl

中文:
定理 nnnorm_toContinuousMultilinearMap
  条件: (f : E [⋀^ι]->L[𝕜] F)
  结论: ‖f.1‖₊ = ‖f‖₊
  证明: rfl
-/
@[simp] theorem nnnorm_toContinuousMultilinearMap (f : E [⋀^ι]->L[𝕜] F) : ‖f.1‖₊ = ‖f‖₊ := rfl
/--
theorem `enorm_toContinuousMultilinearMap` / 定理 `enorm_toContinuousMultilinearMap`

English:
theorem enorm_toContinuousMultilinearMap
  given: (f : E [⋀^ι]->L[𝕜] F)
  statement: ‖f.1‖ₑ = ‖f‖ₑ
  proof: rfl

中文:
定理 enorm_toContinuousMultilinearMap
  条件: (f : E [⋀^ι]->L[𝕜] F)
  结论: ‖f.1‖ₑ = ‖f‖ₑ
  证明: rfl
-/
@[simp] theorem enorm_toContinuousMultilinearMap (f : E [⋀^ι]->L[𝕜] F) : ‖f.1‖ₑ = ‖f‖ₑ := rfl

/-- The inclusion of `E [⋀^ι]→L[𝕜] F` into `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F`
as a linear isometry. -/
@[simps!]
/--
Definition of `toContinuousMultilinearMapLI` / `toContinuousMultilinearMapLI` 的定义

English:
definition toContinuousMultilinearMapLI
  signature: :
  body: toContinuousMultilinearMapLinear
  norm_map' _ := rfl

中文:
定义 toContinuousMultilinearMapLI
  签名: :
  定义体: toContinuousMultilinearMapLinear
  norm_map' _ := rfl

Depends on / 依赖: toContinuousMultilinearMapLinear
-/
def toContinuousMultilinearMapLI :
    E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F where
  toLinearMap := toContinuousMultilinearMapLinear
  norm_map' _ := rfl

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  given: (f : E [⋀^ι]->L[𝕜] F)
  proof: rfl

中文:
定理 norm_def
  条件: (f : E [⋀^ι]->L[𝕜] F)
  证明: rfl
-/
theorem norm_def (f : E [⋀^ι]->L[𝕜] F) :
    ‖f‖ = sInf {c : Real | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} :=
  rfl

/--
theorem `bounds_nonempty` / 定理 `bounds_nonempty`

English:
theorem bounds_nonempty
  proof: ContinuousMultilinearMap.bounds_nonempty

中文:
定理 bounds_nonempty
  证明: ContinuousMultilinearMap.bounds_nonempty

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.bounds_nonempty, bounds_nonempty
-/
theorem bounds_nonempty :
    exists c, c in {c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_nonempty

/--
theorem `bounds_bddBelow` / 定理 `bounds_bddBelow`

English:
theorem bounds_bddBelow
  given: {f : E [⋀^ι]->L[𝕜] F}
  proof: ContinuousMultilinearMap.bounds_bddBelow

中文:
定理 bounds_bddBelow
  条件: {f : E [⋀^ι]->L[𝕜] F}
  证明: ContinuousMultilinearMap.bounds_bddBelow

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.bounds_bddBelow, bounds_bddBelow
-/
theorem bounds_bddBelow {f : E [⋀^ι]->L[𝕜] F} :
    BddBelow {c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_bddBelow

/--
theorem `isLeast_opNorm` / 定理 `isLeast_opNorm`

English:
theorem isLeast_opNorm
  given: (f : E [⋀^ι]->L[𝕜] F)
  proof: f.1.isLeast_opNorm

中文:
定理 isLeast_opNorm
  条件: (f : E [⋀^ι]->L[𝕜] F)
  证明: f.1.isLeast_opNorm

Depends on / 依赖: isLeast_opNorm
-/
theorem isLeast_opNorm (f : E [⋀^ι]->L[𝕜] F) :
    IsLeast {c : Real | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m i‖} ‖f‖ :=
  f.1.isLeast_opNorm

/--
theorem `le_opNorm` / 定理 `le_opNorm`

English:
theorem le_opNorm
  given: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  statement: ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
  proof: f.1.le_opNorm m

中文:
定理 le_opNorm
  条件: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  结论: ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
  证明: f.1.le_opNorm m

Depends on / 依赖: le_opNorm
-/
theorem le_opNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖ := f.1.le_opNorm m

/--
theorem `le_mul_prod_of_opNorm_le_of_le` / 定理 `le_mul_prod_of_opNorm_le_of_le`

English:
theorem le_mul_prod_of_opNorm_le_of_le
  proof: f.1.le_mul_prod_of_opNorm_le_of_le hC hm

中文:
定理 le_mul_prod_of_opNorm_le_of_le
  证明: f.1.le_mul_prod_of_opNorm_le_of_le hC hm

Depends on / 依赖: le_mul_prod_of_opNorm_le_of_le
-/
theorem le_mul_prod_of_opNorm_le_of_le
    {m : ι -> E} {C : Real} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : forall i, ‖m i‖ <= b i) :
    ‖f m‖ <= C * ∏ i, b i :=
  f.1.le_mul_prod_of_opNorm_le_of_le hC hm

/--
theorem `le_opNorm_mul_prod_of_le` / 定理 `le_opNorm_mul_prod_of_le`

English:
theorem le_opNorm_mul_prod_of_le
  given: (f : E [⋀^ι]->L[𝕜] F) {b : ι -> Real} (hm : forall i, ‖m i‖ <= b i)
  proof: f.1.le_opNorm_mul_prod_of_le hm

中文:
定理 le_opNorm_mul_prod_of_le
  条件: (f : E [⋀^ι]->L[𝕜] F) {b : ι -> 实数} (hm : 对任意 i, ‖m i‖ <= b i)
  证明: f.1.le_opNorm_mul_prod_of_le hm

Depends on / 依赖: le_opNorm_mul_prod_of_le
-/
theorem le_opNorm_mul_prod_of_le (f : E [⋀^ι]->L[𝕜] F) {b : ι -> Real} (hm : forall i, ‖m i‖ <= b i) :
    ‖f m‖ <= ‖f‖ * ∏ i, b i :=
  f.1.le_opNorm_mul_prod_of_le hm

/--
theorem `le_opNorm_mul_pow_card_of_le` / 定理 `le_opNorm_mul_pow_card_of_le`

English:
theorem le_opNorm_mul_pow_card_of_le
  given: (f : E [⋀^ι]->L[𝕜] F) {m b} (hm : ‖m‖ <= b)
  proof: f.1.le_opNorm_mul_pow_card_of_le hm

中文:
定理 le_opNorm_mul_pow_card_of_le
  条件: (f : E [⋀^ι]->L[𝕜] F) {m b} (hm : ‖m‖ <= b)
  证明: f.1.le_opNorm_mul_pow_card_of_le hm

Depends on / 依赖: le_opNorm_mul_pow_card_of_le
-/
theorem le_opNorm_mul_pow_card_of_le (f : E [⋀^ι]->L[𝕜] F) {m b} (hm : ‖m‖ <= b) :
    ‖f m‖ <= ‖f‖ * b ^ Fintype.card ι :=
  f.1.le_opNorm_mul_pow_card_of_le hm

/--
theorem `le_opNorm_mul_pow_of_le` / 定理 `le_opNorm_mul_pow_of_le`

English:
theorem le_opNorm_mul_pow_of_le
  given: {n} (f : E [⋀^Fin n]->L[𝕜] F) {m b} (hm : ‖m‖ <= b)
  proof: f.1.le_opNorm_mul_pow_of_le hm

中文:
定理 le_opNorm_mul_pow_of_le
  条件: {n} (f : E [⋀^有限集 n]->L[𝕜] F) {m b} (hm : ‖m‖ <= b)
  证明: f.1.le_opNorm_mul_pow_of_le hm

Depends on / 依赖: le_opNorm_mul_pow_of_le
-/
theorem le_opNorm_mul_pow_of_le {n} (f : E [⋀^Fin n]->L[𝕜] F) {m b} (hm : ‖m‖ <= b) :
    ‖f m‖ <= ‖f‖ * b ^ n :=
  f.1.le_opNorm_mul_pow_of_le hm

/--
theorem `le_of_opNorm_le` / 定理 `le_of_opNorm_le`

English:
theorem le_of_opNorm_le
  given: {C : Real} (h : ‖f‖ <= C) (m : ι -> E)
  statement: ‖f m‖ <= C * ∏ i, ‖m i‖
  proof: f.1.le_of_opNorm_le h m

中文:
定理 le_of_opNorm_le
  条件: {C : 实数} (h : ‖f‖ <= C) (m : ι -> E)
  结论: ‖f m‖ <= C * ∏ i, ‖m i‖
  证明: f.1.le_of_opNorm_le h m

Depends on / 依赖: le_of_opNorm_le
-/
theorem le_of_opNorm_le {C : Real} (h : ‖f‖ <= C) (m : ι -> E) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.1.le_of_opNorm_le h m

/--
theorem `ratio_le_opNorm` / 定理 `ratio_le_opNorm`

English:
theorem ratio_le_opNorm
  given: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  statement: ‖f m‖ / ∏ i, ‖m i‖ <= ‖f‖
  proof: f.1.ratio_le_opNorm m

中文:
定理 ratio_le_opNorm
  条件: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  结论: ‖f m‖ / ∏ i, ‖m i‖ <= ‖f‖
  证明: f.1.ratio_le_opNorm m

Depends on / 依赖: ratio_le_opNorm
-/
theorem ratio_le_opNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖ / ∏ i, ‖m i‖ <= ‖f‖ :=
  f.1.ratio_le_opNorm m

/--
theorem `unit_le_opNorm` / 定理 `unit_le_opNorm`

English:
theorem unit_le_opNorm
  given: (f : E [⋀^ι]->L[𝕜] F) (h : ‖m‖ <= 1)
  statement: ‖f m‖ <= ‖f‖
  proof: f.1.unit_le_opNorm h

中文:
定理 unit_le_opNorm
  条件: (f : E [⋀^ι]->L[𝕜] F) (h : ‖m‖ <= 1)
  结论: ‖f m‖ <= ‖f‖
  证明: f.1.unit_le_opNorm h

Depends on / 依赖: unit_le_opNorm
-/
theorem unit_le_opNorm (f : E [⋀^ι]->L[𝕜] F) (h : ‖m‖ <= 1) : ‖f m‖ <= ‖f‖ := f.1.unit_le_opNorm h

/--
theorem `opNorm_le_bound` / 定理 `opNorm_le_bound`

English:
theorem opNorm_le_bound
  statement: (f : E [⋀^ι]->L[𝕜] F) {M : Real} (hMp : 0 <= M)
  proof: f.1.opNorm_le_bound hMp hM

中文:
定理 opNorm_le_bound
  结论: (f : E [⋀^ι]->L[𝕜] F) {M : 实数} (hMp : 0 <= M)
  证明: f.1.opNorm_le_bound hMp hM

Depends on / 依赖: opNorm_le_bound
-/
theorem opNorm_le_bound (f : E [⋀^ι]->L[𝕜] F) {M : Real} (hMp : 0 <= M)
    (hM : forall m, ‖f m‖ <= M * ∏ i, ‖m i‖) : ‖f‖ <= M :=
  f.1.opNorm_le_bound hMp hM

/--
theorem `opNorm_le_iff` / 定理 `opNorm_le_iff`

English:
theorem opNorm_le_iff
  given: {C : Real} (hC : 0 <= C)
  statement: ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖
  proof: f.1.opNorm_le_iff hC

中文:
定理 opNorm_le_iff
  条件: {C : 实数} (hC : 0 <= C)
  结论: ‖f‖ <= C ↔ 对任意 m, ‖f m‖ <= C * ∏ i, ‖m i‖
  证明: f.1.opNorm_le_iff hC

Depends on / 依赖: opNorm_le_iff
-/
theorem opNorm_le_iff {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.1.opNorm_le_iff hC

/--
theorem `le_opNNNorm` / 定理 `le_opNNNorm`

English:
theorem le_opNNNorm
  given: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  statement: ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
  proof: f.1.le_opNNNorm m

中文:
定理 le_opNNNorm
  条件: (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E)
  结论: ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊
  证明: f.1.le_opNNNorm m

Depends on / 依赖: le_opNNNorm
-/
theorem le_opNNNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊ :=
  f.1.le_opNNNorm m

/--
theorem `le_of_opNNNorm_le` / 定理 `le_of_opNNNorm_le`

English:
theorem le_of_opNNNorm_le
  given: {C : Real>=0} (h : ‖f‖₊ <= C) (m : ι -> E)
  statement: ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
  proof: f.1.le_of_opNNNorm_le h m

中文:
定理 le_of_opNNNorm_le
  条件: {C : 实数>=0} (h : ‖f‖₊ <= C) (m : ι -> E)
  结论: ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
  证明: f.1.le_of_opNNNorm_le h m

Depends on / 依赖: le_of_opNNNorm_le
-/
theorem le_of_opNNNorm_le {C : Real>=0} (h : ‖f‖₊ <= C) (m : ι -> E) : ‖f m‖₊ <= C * ∏ i, ‖m i‖₊ :=
  f.1.le_of_opNNNorm_le h m

/--
theorem `opNNNorm_le_iff` / 定理 `opNNNorm_le_iff`

English:
theorem opNNNorm_le_iff
  given: {C : Real>=0}
  statement: ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
  proof: f.1.opNNNorm_le_iff

中文:
定理 opNNNorm_le_iff
  条件: {C : 实数>=0}
  结论: ‖f‖₊ <= C ↔ 对任意 m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊
  证明: f.1.opNNNorm_le_iff

Depends on / 依赖: opNNNorm_le_iff
-/
theorem opNNNorm_le_iff {C : Real>=0} : ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊ :=
  f.1.opNNNorm_le_iff

/--
theorem `isLeast_opNNNorm` / 定理 `isLeast_opNNNorm`

English:
theorem isLeast_opNNNorm
  given: (f : E [⋀^ι]->L[𝕜] F)
  proof: f.1.isLeast_opNNNorm

中文:
定理 isLeast_opNNNorm
  条件: (f : E [⋀^ι]->L[𝕜] F)
  证明: f.1.isLeast_opNNNorm

Depends on / 依赖: isLeast_opNNNorm
-/
theorem isLeast_opNNNorm (f : E [⋀^ι]->L[𝕜] F) :
    IsLeast {C : Real>=0 | forall m, ‖f m‖₊ <= C * ∏ i, ‖m i‖₊} ‖f‖₊ :=
  f.1.isLeast_opNNNorm

/--
theorem `opNNNorm_prod` / 定理 `opNNNorm_prod`

English:
theorem opNNNorm_prod
  given: (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G)
  proof: f.1.opNNNorm_prod g.1

中文:
定理 opNNNorm_prod
  条件: (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G)
  证明: f.1.opNNNorm_prod g.1

Depends on / 依赖: opNNNorm_prod
-/
theorem opNNNorm_prod (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G) :
    ‖f.prod g‖₊ = max (‖f‖₊) (‖g‖₊) :=
  f.1.opNNNorm_prod g.1

/--
theorem `opNorm_prod` / 定理 `opNorm_prod`

English:
theorem opNorm_prod
  given: (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G)
  statement: ‖f.prod g‖ = max (‖f‖) (‖g‖)
  proof: f.1.opNorm_prod g.1

中文:
定理 opNorm_prod
  条件: (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G)
  结论: ‖f.乘积 g‖ = 最大值 (‖f‖) (‖g‖)
  证明: f.1.opNorm_prod g.1

Depends on / 依赖: opNorm_prod
-/
theorem opNorm_prod (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G) : ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
  f.1.opNorm_prod g.1

/--
theorem `opNNNorm_pi` / 定理 `opNNNorm_pi`

English:
theorem opNNNorm_pi
  statement: {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
  proof: ContinuousMultilinearMap.opNNNorm_pi fun i => (f i).1

中文:
定理 opNNNorm_pi
  结论: {ι' : 类型} [有限类型 ι'] {F : ι' -> 类型} [对任意 i', SeminormedAddComm群 (F i')]
  证明: ContinuousMultilinearMap.opNNNorm_pi fun i => (f i).1

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNNNorm_pi, opNNNorm_pi
-/
theorem opNNNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
    [forall i', NormedSpace 𝕜 (F i')] (f : forall i', E [⋀^ι]->L[𝕜] F i') : ‖pi f‖₊ = ‖f‖₊ :=
  ContinuousMultilinearMap.opNNNorm_pi fun i => (f i).1

/--
theorem `opNorm_pi` / 定理 `opNorm_pi`

English:
theorem opNorm_pi
  statement: {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
  proof: ContinuousMultilinearMap.opNorm_pi fun i => (f i).1

中文:
定理 opNorm_pi
  结论: {ι' : 类型} [有限类型 ι'] {F : ι' -> 类型} [对任意 i', SeminormedAddComm群 (F i')]
  证明: ContinuousMultilinearMap.opNorm_pi fun i => (f i).1

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_pi, opNorm_pi
-/
theorem opNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
    [forall i', NormedSpace 𝕜 (F i')] (f : forall i', E [⋀^ι]->L[𝕜] F i') : ‖pi f‖ = ‖f‖ :=
  ContinuousMultilinearMap.opNorm_pi fun i => (f i).1

/--
Instance `instNormedSpace` / 实例 `instNormedSpace`

English:
instance instNormedSpace
  signature: {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
  body: ⟨fun c f => f.1.opNorm_smul_le c⟩

中文:
实例 instNormedSpace
  签名: {𝕜' : 类型} [赋范域 𝕜'] [赋范空间 𝕜' F] [标量交换类 𝕜 𝕜' F]
  定义体: ⟨fun c f => f.1.opNorm_smul_le c⟩

Depends on / 依赖: opNorm_smul_le
-/
instance instNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    NormedSpace 𝕜' (E [⋀^ι]->L[𝕜] F) :=
  ⟨fun c f => f.1.opNorm_smul_le c⟩

section

/--
theorem `norm_ofSubsingleton` / 定理 `norm_ofSubsingleton`

English:
theorem norm_ofSubsingleton
  given: [Subsingleton ι] (i : ι) (f : E ->L[𝕜] F)
  proof: ContinuousMultilinearMap.norm_ofSubsingleton i f

中文:
定理 norm_ofSubsingleton
  条件: [子单例 ι] (i : ι) (f : E ->L[𝕜] F)
  证明: ContinuousMultilinearMap.norm_ofSubsingleton i f
-/
@[simp] theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E ->L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖ = ‖f‖ :=
  ContinuousMultilinearMap.norm_ofSubsingleton i f

/--
theorem `nnnorm_ofSubsingleton` / 定理 `nnnorm_ofSubsingleton`

English:
theorem nnnorm_ofSubsingleton
  given: [Subsingleton ι] (i : ι) (f : E ->L[𝕜] F)
  proof: NNReal.eq norm_ofSubsingleton i f

中文:
定理 nnnorm_ofSubsingleton
  条件: [子单例 ι] (i : ι) (f : E ->L[𝕜] F)
  证明: NNReal.eq norm_ofSubsingleton i f
-/
@[simp] theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E ->L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖₊ = ‖f‖₊ :=
NNReal.eq norm_ofSubsingleton i f

/-- `ContinuousAlternatingMap.ofSubsingleton` as a linear isometry. -/
@[simps +simpRhs]
/--
Definition of `ofSubsingletonLIE` / `ofSubsingletonLIE` 的定义

English:
definition ofSubsingletonLIE
  signature: [Subsingleton ι] (i : ι)
  body: ofSubsingleton 𝕜 E F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_ofSubsingleton i

中文:
定义 ofSubsingletonLIE
  签名: [子单例 ι] (i : ι)
  定义体: ofSubsingleton 𝕜 E F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_ofSubsingleton i

Depends on / 依赖: ofSubsingleton
-/
def ofSubsingletonLIE [Subsingleton ι] (i : ι) : (E ->L[𝕜] F) ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] F) where
  __ := ofSubsingleton 𝕜 E F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_ofSubsingleton i

/--
theorem `norm_ofSubsingleton_id_le` / 定理 `norm_ofSubsingleton_id_le`

English:
theorem norm_ofSubsingleton_id_le
  given: [Subsingleton ι] (i : ι)
  proof: ContinuousMultilinearMap.norm_ofSubsingleton_id_le ..

中文:
定理 norm_ofSubsingleton_id_le
  条件: [子单例 ι] (i : ι)
  证明: ContinuousMultilinearMap.norm_ofSubsingleton_id_le ..

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_ofSubsingleton_id_le, norm_ofSubsingleton_id_le
-/
theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖ <= 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id_le ..

/--
theorem `nnnorm_ofSubsingleton_id_le` / 定理 `nnnorm_ofSubsingleton_id_le`

English:
theorem nnnorm_ofSubsingleton_id_le
  given: [Subsingleton ι] (i : ι)
  proof: ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le ..

中文:
定理 nnnorm_ofSubsingleton_id_le
  条件: [子单例 ι] (i : ι)
  证明: ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le ..

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le, nnnorm_ofSubsingleton_id_le
-/
theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖₊ <= 1 :=
  ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le ..

variable (𝕜 E)

/--
theorem `norm_constOfIsEmpty` / 定理 `norm_constOfIsEmpty`

English:
theorem norm_constOfIsEmpty
  given: [IsEmpty ι] (x : F)
  statement: ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖
  proof: ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _

中文:
定理 norm_constOfIsEmpty
  条件: [是空 ι] (x : F)
  结论: ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖
  证明: ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _
-/
@[simp] theorem norm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖ :=
  ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _

/--
theorem `nnnorm_constOfIsEmpty` / 定理 `nnnorm_constOfIsEmpty`

English:
theorem nnnorm_constOfIsEmpty
  given: [IsEmpty ι] (x : F)
  statement: ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊
  proof: NNReal.eq norm_constOfIsEmpty _ _ _

中文:
定理 nnnorm_constOfIsEmpty
  条件: [是空 ι] (x : F)
  结论: ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊
  证明: NNReal.eq norm_constOfIsEmpty _ _ _
-/
@[simp] theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊ :=
NNReal.eq norm_constOfIsEmpty _ _ _

variable (ι F) in
/-- `constOfIsEmpty` as a linear isometry equivalence. -/
@[simps]
/--
Definition of `constOfIsEmptyLIE` / `constOfIsEmptyLIE` 的定义

English:
definition constOfIsEmptyLIE
  signature: [IsEmpty ι]
  body: constOfIsEmpty _ _ _
  invFun f := f 0
  left_inv x := by simp
  right_inv f := by ext x; simp [Subsingleton.allEq x 0]
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' := norm_constOfIsEmpty _ _

中文:
定义 constOfIsEmptyLIE
  签名: [是空 ι]
  定义体: constOfIsEmpty _ _ _
  invFun f := f 0
  left_inv x := by simp
  right_inv f := by ext x; simp [Subsingleton.allEq x 0]
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' := norm_constOfIsEmpty _ _

Depends on / 依赖: constOfIsEmpty
-/
def constOfIsEmptyLIE [IsEmpty ι] : F ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] F) where
  toFun := constOfIsEmpty _ _ _
  invFun f := f 0
  left_inv x := by simp
  right_inv f := by ext x; simp [Subsingleton.allEq x 0]
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' := norm_constOfIsEmpty _ _

end

variable (𝕜 E F G) in
/-- `ContinuousAlternatingMap.prod` as a `LinearIsometryEquiv`. -/
@[simps]
/--
Definition of `prodLIE` / `prodLIE` 的定义

English:
definition prodLIE
  signature: : (E [⋀^ι]->L[𝕜] F) × (E [⋀^ι]->L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (F × G)) where
  body: f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 F G).compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 F G).compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

中文:
定义 prodLIE
  签名: : (E [⋀^ι]->L[𝕜] F) × (E [⋀^ι]->L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (F × G)) where
  定义体: f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 F G).compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 F G).compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2
-/
def prodLIE : (E [⋀^ι]->L[𝕜] F) × (E [⋀^ι]->L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (F × G)) where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 F G).compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 F G).compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

variable (𝕜 E) in
/-- `ContinuousAlternatingMap.pi` as a `LinearIsometryEquiv`. -/
@[simps!]
/--
Definition of `piLIE` / `piLIE` 的定义

English:
definition piLIE
  signature: {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
  body: piLinearEquiv
  norm_map' := opNorm_pi

中文:
定义 piLIE
  签名: {ι' : 类型} [有限类型 ι'] {F : ι' -> 类型} [对任意 i', SeminormedAddComm群 (F i')]
  定义体: piLinearEquiv
  norm_map' := opNorm_pi

Depends on / 依赖: piLinearEquiv
-/
def piLIE {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')]
    [forall i', NormedSpace 𝕜 (F i')] :
    (forall i', E [⋀^ι]->L[𝕜] F i') ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (forall i, F i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

section restrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

/--
theorem `norm_restrictScalars` / 定理 `norm_restrictScalars`

English:
theorem norm_restrictScalars
  statement: ‖f.restrictScalars 𝕜'‖ = ‖f‖
  proof: rfl

中文:
定理 norm_restrictScalars
  结论: ‖f.restrictScalars 𝕜'‖ = ‖f‖
  证明: rfl
-/
@[simp] theorem norm_restrictScalars : ‖f.restrictScalars 𝕜'‖ = ‖f‖ := rfl

variable (𝕜')

/-- `ContinuousAlternatingMap.restrictScalars` as a `LinearIsometry`. -/
@[simps]
/--
Definition of `restrictScalarsLI` / `restrictScalarsLI` 的定义

English:
definition restrictScalarsLI
  signature: : E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜'] E [⋀^ι]->L[𝕜'] F where
  body: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

中文:
定义 restrictScalarsLI
  签名: : E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜'] E [⋀^ι]->L[𝕜'] F where
  定义体: restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

Depends on / 依赖: restrictScalars
-/
def restrictScalarsLI : E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜'] E [⋀^ι]->L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end restrictScalars

/--
theorem `norm_image_sub_le'` / 定理 `norm_image_sub_le'`

English:
theorem norm_image_sub_le'
  given: [DecidableEq ι] (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E)
  proof: f.1.norm_image_sub_le' m₁ m₂

中文:
定理 norm_image_sub_le'
  条件: [DecidableEq ι] (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E)
  证明: f.1.norm_image_sub_le' m₁ m₂

Depends on / 依赖: norm_image_sub_le
-/
theorem norm_image_sub_le' [DecidableEq ι] (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E) :
    ‖f m₁ - f m₂‖ <= ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.1.norm_image_sub_le' m₁ m₂

/--
theorem `norm_image_sub_le` / 定理 `norm_image_sub_le`

English:
theorem norm_image_sub_le
  given: (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E)
  proof: f.1.norm_image_sub_le m₁ m₂

中文:
定理 norm_image_sub_le
  条件: (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E)
  证明: f.1.norm_image_sub_le m₁ m₂

Depends on / 依赖: norm_image_sub_le
-/
theorem norm_image_sub_le (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E) :
    ‖f m₁ - f m₂‖ <= ‖f‖ * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.1.norm_image_sub_le m₁ m₂

end ContinuousAlternatingMap

variable [Fintype ι]

/--
theorem `AlternatingMap.mkContinuous_norm_le` / 定理 `AlternatingMap.mkContinuous_norm_le`

English:
theorem AlternatingMap.mkContinuous_norm_le
  statement: (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
  proof: f.toMultilinearMap.mkContinuous_norm_le hC H

中文:
定理 交错映射.mkContinuous_norm_le
  结论: (f : E [⋀^ι]->ₗ[𝕜] F) {C : 实数} (hC : 0 <= C)
  证明: f.toMultilinearMap.mkContinuous_norm_le hC H

Depends on / 依赖: f.toMultilinearMap.mkContinuous_norm_le, mkContinuous_norm_le, toMultilinearMap
-/
theorem AlternatingMap.mkContinuous_norm_le (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C)
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= C :=
  f.toMultilinearMap.mkContinuous_norm_le hC H

/--
theorem `AlternatingMap.mkContinuous_norm_le'` / 定理 `AlternatingMap.mkContinuous_norm_le'`

English:
theorem AlternatingMap.mkContinuous_norm_le'
  statement: (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real}
  proof: ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans by
    gcongr
    apply le_max_left

中文:
定理 交错映射.mkContinuous_norm_le'
  结论: (f : E [⋀^ι]->ₗ[𝕜] F) {C : 实数}
  证明: ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans by
    gcongr
    apply le_max_left

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, le_max_left, le_max_right, opNorm_le_bound
-/
theorem AlternatingMap.mkContinuous_norm_le' (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real}
    (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= max C 0 :=
ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m => (H m).trans by
    gcongr
    apply le_max_left

namespace ContinuousLinearMap

/--
theorem `norm_compContinuousAlternatingMap_le` / 定理 `norm_compContinuousAlternatingMap_le`

English:
theorem norm_compContinuousAlternatingMap_le
  given: (g : F ->L[𝕜] G) (f : E [⋀^ι]->L[𝕜] F)
  proof: g.norm_compContinuousMultilinearMap_le f.1

中文:
定理 norm_compContinuousAlternatingMap_le
  条件: (g : F ->L[𝕜] G) (f : E [⋀^ι]->L[𝕜] F)
  证明: g.norm_compContinuousMultilinearMap_le f.1

Depends on / 依赖: g.norm_compContinuousMultilinearMap_le, norm_compContinuousMultilinearMap_le
-/
theorem norm_compContinuousAlternatingMap_le (g : F ->L[𝕜] G) (f : E [⋀^ι]->L[𝕜] F) :
    ‖g.compContinuousAlternatingMap f‖ <= ‖g‖ * ‖f‖ :=
  g.norm_compContinuousMultilinearMap_le f.1

/-- Flip arguments in `f : F →L[𝕜] E [⋀^ι]→L[𝕜] G` to get `⋀^ι⟮𝕜; E; F →L[𝕜] G⟯` -/
@[simps! apply_apply]
/--
Definition of `flipAlternating` / `flipAlternating` 的定义

English:
definition flipAlternating
  signature: (f : F ->L[𝕜] (E [⋀^ι]->L[𝕜] G))
  body: ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

中文:
定义 flipAlternating
  签名: (f : F ->L[𝕜] (E [⋀^ι]->L[𝕜] G))
  定义体: ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

Depends on / 依赖: ContinuousAlternatingMap, ContinuousAlternatingMap.toContinuousMultilinearMapCLM, flipMultilinear, map_eq_zero_of_eq, toContinuousMultilinearMapCLM
-/
def flipAlternating (f : F ->L[𝕜] (E [⋀^ι]->L[𝕜] G)) : E [⋀^ι]->L[𝕜] (F ->L[𝕜] G) where
  toContinuousMultilinearMap :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

end ContinuousLinearMap

/--
theorem `LinearIsometry.norm_compContinuousAlternatingMap` / 定理 `LinearIsometry.norm_compContinuousAlternatingMap`

English:
theorem LinearIsometry.norm_compContinuousAlternatingMap
  given: (g : F ->ₗᵢ[𝕜] G) (f : E [⋀^ι]->L[𝕜] F)
  proof: g.norm_compContinuousMultilinearMap f.1

中文:
定理 线性等距.norm_compContinuousAlternatingMap
  条件: (g : F ->ₗᵢ[𝕜] G) (f : E [⋀^ι]->L[𝕜] F)
  证明: g.norm_compContinuousMultilinearMap f.1

Depends on / 依赖: g.norm_compContinuousMultilinearMap, norm_compContinuousMultilinearMap
-/
theorem LinearIsometry.norm_compContinuousAlternatingMap (g : F ->ₗᵢ[𝕜] G) (f : E [⋀^ι]->L[𝕜] F) :
    ‖g.toContinuousLinearMap.compContinuousAlternatingMap f‖ = ‖f‖ :=
  g.norm_compContinuousMultilinearMap f.1

open ContinuousAlternatingMap

section

namespace ContinuousAlternatingMap

/--
theorem `norm_compContinuousLinearMap_le` / 定理 `norm_compContinuousLinearMap_le`

English:
theorem norm_compContinuousLinearMap_le
  statement: (f : F [⋀^ι]->L[𝕜] G)
  proof: (f.1.norm_compContinuousLinearMap_le _).trans_eq by simp

omit [Fintype ι] in

中文:
定理 norm_compContinuousLinearMap_le
  结论: (f : F [⋀^ι]->L[𝕜] G)
  证明: (f.1.norm_compContinuousLinearMap_le _).trans_eq by simp

omit [Fintype ι] in

Depends on / 依赖: norm_compContinuousLinearMap_le, trans_eq
-/
theorem norm_compContinuousLinearMap_le (f : F [⋀^ι]->L[𝕜] G)
    (g : E ->L[𝕜] F) : ‖f.compContinuousLinearMap g‖ <= ‖f‖ * (‖g‖ ^ Fintype.card ι) :=
(f.1.norm_compContinuousLinearMap_le _).trans_eq by simp

omit [Fintype ι] in
/--
theorem `continuous_compContinuousLinearMapCLM` / 定理 `continuous_compContinuousLinearMapCLM`

English:
theorem continuous_compContinuousLinearMapCLM
  given: [Finite ι]
  proof: by
  rcases nonempty_fintype ι
  refine UniformConvergenceCLM.isUniformInducing_postcomp (.id 𝕜)
    (toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]->L[𝕜] G) ->L[𝕜] _)
.isInducing isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing _
.mpr ?_ .continuous_iff
change Continuous
    (toContinuou

中文:
定理 continuous_compContinuousLinearMapCLM
  条件: [有限 ι]
  证明: by
  rcases nonempty_fintype ι
  refine UniformConvergenceCLM.isUniformInducing_postcomp (.id 𝕜)
    (toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]->L[𝕜] G) ->L[𝕜] _)
.isInducing isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing _
.mpr ?_ .continuous_iff
change Continuous
    (toContinuou

Depends on / 依赖: Continuous, ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear, UniformConvergenceCLM, UniformConvergenceCLM.isUniformInducing_postcomp, compContinuousLinearMapContinuousMultilinear, continuous_iff, fun_prop, isInducing, isUniformEmbedding_toContinuousMultilinearMap, isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing, isUniformInducing, isUniformInducing_postcomp, nonempty_fintype, precomp, toContinuousMultilinearMapCLM
-/
theorem continuous_compContinuousLinearMapCLM [Finite ι] :
    Continuous
      (compContinuousLinearMapCLM : (E ->L[𝕜] F) -> (F [⋀^ι]->L[𝕜] G) ->L[𝕜] (E [⋀^ι]->L[𝕜] G)) := by
  rcases nonempty_fintype ι
  refine UniformConvergenceCLM.isUniformInducing_postcomp (.id 𝕜)
    (toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]->L[𝕜] G) ->L[𝕜] _)
.isInducing isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing _
.mpr ?_ .continuous_iff
change Continuous
    (toContinuousMultilinearMapCLM 𝕜 : (F [⋀^ι]->L[𝕜] G) ->L[𝕜] _).precomp _ ∘
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι => E) (fun _ => F) G ∘
      (fun f _ => f)
  fun_prop

variable [DecidableEq ι]

/--
Definition of `fderivCompContinuousLinearMap` / `fderivCompContinuousLinearMap` 的定义

English:
definition fderivCompContinuousLinearMap
  signature: (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F)
  body: liftCLM (f.1.fderivCompContinuousLinearMap (fun _ : ι => g) ∘L .pi fun _ => .id _ _) by
    intro dg v a b heq hne
    trans ∑ i, f fun j => Function.update (fun _ => g) i dg j (v j)
    · simp
    · rw [← Finset.sum_add_sum_compl {a, b}, Finset.sum_pair hne, Finset.sum_eq_zero, add_zero]
      · co

中文:
定义 fderivCompContinuousLinearMap
  签名: (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F)
  定义体: liftCLM (f.1.fderivCompContinuousLinearMap (fun _ : ι => g) ∘L .pi fun _ => .id _ _) by
    intro dg v a b heq hne
    trans ∑ i, f fun j => Function.update (fun _ => g) i dg j (v j)
    · simp
    · rw [← Finset.sum_add_sum_compl {a, b}, Finset.sum_pair hne, Finset.sum_eq_zero, add_zero]
      · co

Depends on / 依赖: Equiv.swap_apply_of_, Finset, Finset.sum_add_sum_compl, Finset.sum_eq_zero, Finset.sum_pair, Function, Function.update, Function.update_apply, add_zero, convert, eq_or_ne, f.map_add_swap, fderivCompContinuousLinearMap, hne.symm, liftCLM, map_add_swap, sum_add_sum_compl, sum_eq_zero, sum_pair, swap_apply_of_
-/
def fderivCompContinuousLinearMap (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F) :
    (E ->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] G) :=
liftCLM (f.1.fderivCompContinuousLinearMap (fun _ : ι => g) ∘L .pi fun _ => .id _ _) by
    intro dg v a b heq hne
    trans ∑ i, f fun j => Function.update (fun _ => g) i dg j (v j)
    · simp
    · rw [← Finset.sum_add_sum_compl {a, b}, Finset.sum_pair hne, Finset.sum_eq_zero, add_zero]
      · convert! f.map_add_swap _ hne with i
        rcases eq_or_ne i a with rfl | hia
        · simp [heq, hne, hne.symm]
        · rcases eq_or_ne i b with rfl | hib
          · simp [Function.update_apply, heq]
          · simp [Function.update_apply, Equiv.swap_apply_of_ne_of_ne, *]
      · simp only [mem_compl, mem_insert, mem_singleton, not_or, and_imp]
        intro i hia hib
        apply f.map_eq_zero_of_eq _ _ hne
        simp [*, Ne.symm]

@[simp]
/--
lemma `toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap` / 引理 `toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap`

English:
lemma toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap
  proof: rfl

@[simp]

中文:
引理 toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap
  证明: rfl

@[simp]
-/
lemma toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap
    (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F) :
    toContinuousMultilinearMapCLM 𝕜 ∘L f.fderivCompContinuousLinearMap g =
      f.1.fderivCompContinuousLinearMap (fun _ : ι => g) ∘L .pi fun _ => .id _ _ :=
  rfl

@[simp]
/--
lemma `fderivCompContinuousLinearMap_apply` / 引理 `fderivCompContinuousLinearMap_apply`

English:
lemma fderivCompContinuousLinearMap_apply
  given: (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜] F) (v : ι -> E)
  proof: by
  simp [fderivCompContinuousLinearMap]

@[nontriviality]

中文:
引理 fderivCompContinuousLinearMap_apply
  条件: (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜] F) (v : ι -> E)
  证明: by
  simp [fderivCompContinuousLinearMap]

@[nontriviality]

Depends on / 依赖: fderivCompContinuousLinearMap
-/
lemma fderivCompContinuousLinearMap_apply (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜] F) (v : ι -> E) :
    f.fderivCompContinuousLinearMap g dg v =
      ∑ i, f fun j => Function.update (fun _ => g) i dg j (v j) := by
  simp [fderivCompContinuousLinearMap]

@[nontriviality]
/--
lemma `fderivCompContinuousLinearMap_of_isEmpty` / 引理 `fderivCompContinuousLinearMap_of_isEmpty`

English:
lemma fderivCompContinuousLinearMap_of_isEmpty
  given: [IsEmpty ι]
  proof: by
  ext; simp

中文:
引理 fderivCompContinuousLinearMap_of_isEmpty
  条件: [是空 ι]
  证明: by
  ext; simp
-/
lemma fderivCompContinuousLinearMap_of_isEmpty [IsEmpty ι] :
    fderivCompContinuousLinearMap (ι := ι) (𝕜 := 𝕜) (E := E) (F := F) (G := G) = 0 := by
  ext; simp

variable (G) in
/--
Definition of `fderivCompContinuousLinearMapCLM` / `fderivCompContinuousLinearMapCLM` 的定义

English:
definition fderivCompContinuousLinearMapCLM
  signature: (g : E ->L[𝕜] F)
  body: LinearMap.mkContinuous
    { toFun := (fderivCompContinuousLinearMap · g)
      map_add' f₁ f₂ := by ext; simp [Finset.sum_add_distrib]
      map_smul' c f := by ext; simp [Finset.smul_sum] }
    (Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1))
    fun f => by
      refine ContinuousLinearMap.opNorm_le

中文:
定义 fderivCompContinuousLinearMapCLM
  签名: (g : E ->L[𝕜] F)
  定义体: LinearMap.mkContinuous
    { toFun := (fderivCompContinuousLinearMap · g)
      map_add' f₁ f₂ := by ext; simp [Finset.sum_add_distrib]
      map_smul' c f := by ext; simp [Finset.smul_sum] }
    (Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1))
    fun f => by
      refine ContinuousLinearMap.opNorm_le

Depends on / 依赖: AddHom, AddHom.coe_mk, ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, Finset, Finset.smul_sum, Finset.sum_add_distrib, Fintype, Fintype.card, LinearMap, LinearMap.coe_mk, LinearMap.mkContinuous, coe_mk, fderivCompContinuousLinearMap, fderivCompContinuousLinearMap_apply, map_add, map_smul, mkContinuous, mul_assoc, norm_sum_le
-/
def fderivCompContinuousLinearMapCLM (g : E ->L[𝕜] F) :
    (F [⋀^ι]->L[𝕜] G) ->L[𝕜] (E ->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] G) :=
  LinearMap.mkContinuous
    { toFun := (fderivCompContinuousLinearMap · g)
      map_add' f₁ f₂ := by ext; simp [Finset.sum_add_distrib]
      map_smul' c f := by ext; simp [Finset.smul_sum] }
    (Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1))
    fun f => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dg => ?_
      refine opNorm_le_bound _ (by positivity) fun v => ?_
      simp? [mul_assoc] says
        simp only [LinearMap.coe_mk, AddHom.coe_mk, fderivCompContinuousLinearMap_apply, mul_assoc]
      refine (norm_sum_le _ _).trans ?_
      grw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      rintro i -
      grw [le_opNorm]
      simp only [Fintype.prod_eq_mul_prod_compl i, Function.update_self, mul_left_comm (‖g‖ ^ _)]
      grw [dg.le_opNorm, mul_assoc]
      gcongr
      rw [← Finset.card_singleton i]; rw [← Finset.card_compl]; rw [← Finset.prod_const]; rw [← Finset.prod_mul_distrib]
      gcongr with j hj
      simpa [Function.update_of_ne (by simpa using hj)] using g.le_opNorm _

@[simp]
/--
lemma `fderivCompContinuousLinearMapCLM_apply` / 引理 `fderivCompContinuousLinearMapCLM_apply`

English:
lemma fderivCompContinuousLinearMapCLM_apply
  given: (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F)
  proof: rfl

中文:
引理 fderivCompContinuousLinearMapCLM_apply
  条件: (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F)
  证明: rfl
-/
lemma fderivCompContinuousLinearMapCLM_apply (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F) :
    fderivCompContinuousLinearMapCLM G g f = fderivCompContinuousLinearMap f g :=
  rfl

end ContinuousAlternatingMap

end

open ContinuousAlternatingMap

namespace AlternatingMap

/--
Definition of `mkContinuousLinear` / `mkContinuousLinear` 的定义

English:
definition mkContinuousLinear
  signature: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real)
  body: LinearMap.mkContinuous
    { toFun x := (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]
exact (mkContinuous_norm_le' _ _).trans_eq by
        rw [max_mul_of_nonneg

中文:
定义 mkContinuousLinear
  签名: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : 实数)
  定义体: LinearMap.mkContinuous
    { toFun x := (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]
exact (mkContinuous_norm_le' _ _).trans_eq by
        rw [max_mul_of_nonneg

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, LinearMap.mkContinuous, coe_mk, map_add, map_smul, max_mul_of_nonneg, mkContinuous, mkContinuous_norm_le, norm_nonneg, trans_eq, zero_mul
-/
def mkContinuousLinear (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : F ->L[𝕜] E [⋀^ι]->L[𝕜] G :=
  LinearMap.mkContinuous
    { toFun x := (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk]; rw [AddHom.coe_mk]
exact (mkContinuous_norm_le' _ _).trans_eq by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x)]; rw [zero_mul]

/--
theorem `mkContinuousLinear_norm_le_max` / 定理 `mkContinuousLinear_norm_le_max`

English:
theorem mkContinuousLinear_norm_le_max
  statement: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real)
  proof: LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

中文:
定理 mkContinuousLinear_norm_le_max
  结论: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : 实数)
  证明: LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous_norm_le, le_max_right, mkContinuous_norm_le
-/
theorem mkContinuousLinear_norm_le_max (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ <= max C 0 :=
  LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

/--
theorem `mkContinuousLinear_norm_le` / 定理 `mkContinuousLinear_norm_le`

English:
theorem mkContinuousLinear_norm_le
  statement: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) {C : Real} (hC : 0 <= C)
  proof: (mkContinuousLinear_norm_le_max f C H).trans_eq (max_eq_left hC)

中文:
定理 mkContinuousLinear_norm_le
  结论: (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) {C : 实数} (hC : 0 <= C)
  证明: (mkContinuousLinear_norm_le_max f C H).trans_eq (max_eq_left hC)

Depends on / 依赖: max_eq_left, mkContinuousLinear_norm_le_max, trans_eq
-/
theorem mkContinuousLinear_norm_le (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) {C : Real} (hC : 0 <= C)
    (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ <= C :=
  (mkContinuousLinear_norm_le_max f C H).trans_eq (max_eq_left hC)

variable {ι' : Type*} [Fintype ι']

/--
Definition of `mkContinuousAlternating` / `mkContinuousAlternating` 的定义

English:
definition mkContinuousAlternating
  signature: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G))
  body: mkContinuous
    { toFun m := mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' m i x y := by ext1; simp
      map_update_smul' m i c x := by ext1; simp
      map_eq_zero_of_eq' v i j hv hij := by
        ext v'
        have : f v = 0 := by simpa using f.map_eq_zero_of_eq' v i j hv hi

中文:
定义 mkContinuousAlternating
  签名: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G))
  定义体: mkContinuous
    { toFun m := mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' m i x y := by ext1; simp
      map_update_smul' m i c x := by ext1; simp
      map_eq_zero_of_eq' v i j hv hij := by
        ext v'
        have : f v = 0 := by simpa using f.map_eq_zero_of_eq' v i j hv hi

Depends on / 依赖: MultilinearMap, MultilinearMap.coe_mk, coe_mk, f.map_eq_zero_of_eq, map_eq_zero_of_eq, map_update_add, map_update_smul, max_mul_of_nonneg, mkContinuous, mkContinuous_norm_le, trans_eq, zero_mul
-/
def mkContinuousAlternating (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G))
    (C : Real) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    E [⋀^ι]->L[𝕜] (F [⋀^ι']->L[𝕜] G) :=
  mkContinuous
    { toFun m := mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' m i x y := by ext1; simp
      map_update_smul' m i c x := by ext1; simp
      map_eq_zero_of_eq' v i j hv hij := by
        ext v'
        have : f v = 0 := by simpa using f.map_eq_zero_of_eq' v i j hv hij
        simp [this] }
    (max C 0) fun m => by
      simp only [coe_mk, MultilinearMap.coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg]; rw [zero_mul]
      positivity

@[simp]
/--
theorem `mkContinuousAlternating_apply` / 定理 `mkContinuousAlternating_apply`

English:
theorem mkContinuousAlternating_apply
  statement: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
  proof: rfl

中文:
定理 mkContinuousAlternating_apply
  结论: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : 实数}
  证明: rfl
-/
theorem mkContinuousAlternating_apply (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
    (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι -> E) :
    ⇑(mkContinuousAlternating f C H m) = f m :=
  rfl

/--
theorem `mkContinuousAlternating_norm_le_max` / 定理 `mkContinuousAlternating_norm_le_max`

English:
theorem mkContinuousAlternating_norm_le_max
  statement: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
  proof: by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

中文:
定理 mkContinuousAlternating_norm_le_max
  结论: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : 实数}
  证明: by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

Depends on / 依赖: le_max_right, mkContinuousAlternating, mkContinuous_norm_le
-/
theorem mkContinuousAlternating_norm_le_max (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
    (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ <= max C 0 := by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

/--
theorem `mkContinuousAlternating_norm_le` / 定理 `mkContinuousAlternating_norm_le`

English:
theorem mkContinuousAlternating_norm_le
  statement: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
  proof: (mkContinuousAlternating_norm_le_max f H).trans_eq (max_eq_left hC)

中文:
定理 mkContinuousAlternating_norm_le
  结论: (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : 实数}
  证明: (mkContinuousAlternating_norm_le_max f H).trans_eq (max_eq_left hC)

Depends on / 依赖: max_eq_left, mkContinuousAlternating_norm_le_max, trans_eq
-/
theorem mkContinuousAlternating_norm_le (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real}
    (hC : 0 <= C) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ <= C :=
  (mkContinuousAlternating_norm_le_max f H).trans_eq (max_eq_left hC)

end AlternatingMap

end Seminorm

section Norm

/-! Results that are only true if the target space is a `NormedAddCommGroup`
(and not just a `SeminormedAddCommGroup`). -/

universe u wE wF v
variable {𝕜 : Type u} {n : Nat} {E : Type wE} {F : Type wF} {ι : Type v}
  [Fintype ι]
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousAlternatingMap

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: : NormedAddCommGroup (E [⋀^ι]->L[𝕜] F)
  body: NormedAddCommGroup.ofSeparation fun _f hf =>
toContinuousMultilinearMap_injective norm_eq_zero.mp hf

中文:
实例 instNormedAddCommGroup
  签名: : 赋范交换加群 (E [⋀^ι]->L[𝕜] F)
  定义体: NormedAddCommGroup.ofSeparation fun _f hf =>
toContinuousMultilinearMap_injective norm_eq_zero.mp hf

Depends on / 依赖: NormedAddCommGroup, NormedAddCommGroup.ofSeparation, norm_eq_zero, norm_eq_zero.mp, ofSeparation, toContinuousMultilinearMap_injective
-/
instance instNormedAddCommGroup : NormedAddCommGroup (E [⋀^ι]->L[𝕜] F) :=
  NormedAddCommGroup.ofSeparation fun _f hf =>
toContinuousMultilinearMap_injective norm_eq_zero.mp hf

variable (𝕜 F) in
/--
theorem `norm_ofSubsingleton_id` / 定理 `norm_ofSubsingleton_id`

English:
theorem norm_ofSubsingleton_id
  given: [Subsingleton ι] [Nontrivial F] (i : ι)
  proof: ContinuousMultilinearMap.norm_ofSubsingleton_id 𝕜 F i

中文:
定理 norm_ofSubsingleton_id
  条件: [子单例 ι] [非平凡 F] (i : ι)
  证明: ContinuousMultilinearMap.norm_ofSubsingleton_id 𝕜 F i

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_ofSubsingleton_id, norm_ofSubsingleton_id
-/
theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖ = 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id 𝕜 F i

variable (𝕜 F) in
/--
theorem `nnnorm_ofSubsingleton_id` / 定理 `nnnorm_ofSubsingleton_id`

English:
theorem nnnorm_ofSubsingleton_id
  given: [Subsingleton ι] [Nontrivial F] (i : ι)
  proof: NNReal.eq norm_ofSubsingleton_id ..

中文:
定理 nnnorm_ofSubsingleton_id
  条件: [子单例 ι] [非平凡 F] (i : ι)
  证明: NNReal.eq norm_ofSubsingleton_id ..

Depends on / 依赖: NNReal, NNReal.eq, norm_ofSubsingleton_id
-/
theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖₊ = 1 :=
NNReal.eq norm_ofSubsingleton_id ..

end ContinuousAlternatingMap

namespace AlternatingMap

/--
theorem `bound_of_shell` / 定理 `bound_of_shell`

English:
theorem bound_of_shell
  statement: (f : F [⋀^ι]->ₗ[𝕜] E) {ε : ι -> Real} {C : Real} {c : ι -> 𝕜}
  proof: f.1.bound_of_shell hε hc hf m

中文:
定理 bound_of_shell
  结论: (f : F [⋀^ι]->ₗ[𝕜] E) {ε : ι -> 实数} {C : 实数} {c : ι -> 𝕜}
  证明: f.1.bound_of_shell hε hc hf m

Depends on / 依赖: bound_of_shell
-/
theorem bound_of_shell (f : F [⋀^ι]->ₗ[𝕜] E) {ε : ι -> Real} {C : Real} {c : ι -> 𝕜}
    (hε : forall i, 0 < ε i) (hc : forall i, 1 < ‖c i‖)
    (hf : forall m : ι -> F, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖)
    (m : ι -> F) : ‖f m‖ <= C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell hε hc hf m

end AlternatingMap

end Norm
