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

/-- Applying a continuous alternating map to a vector is continuous
in the pair (map, vector).

Continuity in the vector holds by definition
and continuity in the map holds if both the domain and the codomain are topological vector spaces.
However, continuity in the pair (map, vector) needs the domain to be a locally bounded TVS.
We have no typeclass for a locally bounded TVS,
so we require it to be a seminormed space instead. -/
/-
**ContinuousAlternatingMap.instContinuousEval** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousAlternatingMap.instContinuousEval {𝕜 ι E F : Type*} [NormedField
 𝕜] [Finite ι] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace F]
 [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F] : ContinuousEval (E [⋀^
ι]->L[𝕜] F) (ι -> E) F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEval.of_continuous_forget`：ContinuousEval.of_continuous_forget
 {F' : Type*} [FunLike F' X Y] [TopologicalSpace F'] {f : F' -> F} (hc : Continu
ous f) (hf : forall g, ⇑(…
· 使用引理 `ContinuousAlternatingMap.continuous_toContinuousMultilinearMap`：continuo
us_toContinuousMultilinearMap : Continuous (toContinuousMultilinearMap : (E [⋀^ι
]->L[𝕜] F -> _))

--- 原说明 ---
Applying a continuous alternating map to a vector is continuous
in the pair (map, vector).

Continuity in the vector holds by definition
and continuity in the map holds if both the domain and the codomain are topologi
cal vector spaces.
However, continuity in the pair (map, vector) needs the domain to be a locally b
ounded TVS.
We have no typeclass for a locally bounded TVS,
so we require it to be a seminormed space instead.
-/
instance ContinuousAlternatingMap.instContinuousEval {𝕜 ι E F : Type*}
    [NormedField 𝕜] [Finite ι] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F] :
    ContinuousEval (E [⋀^ι]→L[𝕜] F) (ι → E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap

section Seminorm

universe u wE wF wG v
variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {G : Type wG} {ι : Type v}
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

/-- If `f` is a continuous alternating map on `E`
and `m` is an element of `ι → E` such that one of the `m i` has norm `0`, then `f m` has norm `0`.

Note that we cannot drop the continuity assumption.
Indeed, let `ℝ₀` be a copy or `ℝ` with zero norm and indiscrete topology.
Then `f : (Unit → ℝ₀) → ℝ` given by `f x = x ()`
sends vector `1` with zero norm to number `1` with nonzero norm. -/
/-
**AlternatingMap.norm_map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：norm_map_coord_zero (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f) {m : ι -> E}
 {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0
参数：f : E [⋀^ι]->ₗ[𝕜] F；hf : Continuous f；hi : ‖m i‖ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MultilinearMap.norm_map_coord_zero`：norm_map_coord_zero (f : Multilinear
Map 𝕜 E G) (hf : Continuous f) {m : forall i, E i} {i : ι} (hi : ‖m i‖ = 0) : ‖f
 m‖ = 0

--- 原说明 ---
If `f` is a continuous alternating map on `E`
and `m` is an element of `ι → E` such that one of the `m i` has norm `0`, then `
f m` has norm `0`.

Note that we cannot drop the continuity assumption.
Indeed, let `ℝ₀` be a copy or `ℝ` with zero norm and indiscrete topology.
Then `f : (Unit → ℝ₀) → ℝ` given by `f x = x ()`
sends vector `1` with zero norm to number `1` with nonzero norm.
-/
theorem norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f)
    {m : ι → E} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 :=
  f.1.norm_map_coord_zero hf hi

variable [Fintype ι]

/-- If an alternating map in finitely many variables on seminormed spaces
sends vectors with a component of norm zero to vectors of norm zero
and satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i`
for some positive numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`,
then it satisfies this inequality for all `m`.

The first assumption is automatically satisfied on normed spaces, see `bound_of_shell` below.
For seminormed spaces, it follows from continuity of `f`,
see lemma `bound_of_shell_of_continuous` below. -/
/-
**AlternatingMap.bound_of_shell_of_norm_map_coord_zero** 是 Mathlib 中的一个定理，位于命名空间
 `AlternatingMap`。
形式化陈述：bound_of_shell_of_norm_map_coord_zero (f : E [⋀^ι]->ₗ[𝕜] F) (hf₀ : forall 
{m i}, ‖m i‖ = 0 -> ‖f m‖ = 0) {ε : ι -> Real} {C : Real} (hε : forall i, 0 < ε 
i) {c : ι -> 𝕜} (hc : forall i, 1 < ‖c i‖) (hf : forall m : ι -> E, (forall i, ε
 i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖) (m :
 ι -> E) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : E [⋀^ι]->ₗ[𝕜] F；hf₀ : forall {m i}, ‖m i‖ = 0 -> ‖f m‖ = 0；hε : forall i,
 0 < ε i；hc : forall i, 1 < ‖c i‖；hf : forall m : ι -> E, (forall i, ε i / ‖c i‖
 <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i, ‖m i‖；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.bound_of_shell_of_norm_map_coord_zero`：bound_of_shell_of_
norm_map_coord_zero (f : MultilinearMap 𝕜 E G) (hf₀ : forall {m i}, ‖m i‖ = 0 ->
 ‖f m‖ = 0) {ε : ι -> Real} {C : Real} (hε…

--- 原说明 ---
If an alternating map in finitely many variables on seminormed spaces
sends vectors with a component of norm zero to vectors of norm zero
and satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < 
‖m i‖ < ε i`
for some positive numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`,
then it satisfies this inequality for all `m`.

The first assumption is automatically satisfied on normed spaces, see `bound_of_
shell` below.
For seminormed spaces, it follows from continuity of `f`,
see lemma `bound_of_shell_of_continuous` below.
-/
theorem bound_of_shell_of_norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F)
    (hf₀ : ∀ {m i}, ‖m i‖ = 0 → ‖f m‖ = 0)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ι → E, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

/-- If a continuous alternating map in finitely many variables on normed spaces
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`
on a shell `ε / ‖c‖ < ‖m i‖ < ε` for some positive number `ε` and an elements `c : 𝕜`, `1 < ‖c‖`,
then it satisfies this inequality for all `m`.

If the domain is a Hausdorff space, then the continuity assumption is redundant,
see `bound_of_shell` below. -/
/-
**AlternatingMap.bound_of_shell_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Alterna
tingMap`。
形式化陈述：bound_of_shell_of_continuous (f : E [⋀^ι]->ₗ[𝕜] F) (hfc : Continuous f) {ε
 : Real} {C : Real} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall m : ι -> E,
 (forall i, ε / ‖c‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε) -> ‖f m‖ <= C * ∏ i, ‖m i
‖) (m : ι -> E) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : E [⋀^ι]->ₗ[𝕜] F；hfc : Continuous f；hε : 0 < ε；hc : 1 < ‖c‖；hf : forall m 
: ι -> E, (forall i, ε / ‖c‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε) -> ‖f m‖ <= C * 
∏ i, ‖m i‖；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.bound_of_shell_of_continuous`：bound_of_shell_of_continuou
s (f : MultilinearMap 𝕜 E G) (hfc : Continuous f) {ε : ι -> Real} {C : Real} (hε
 : forall i, 0 < ε i) {c : ι -> 𝕜…

--- 原说明 ---
If a continuous alternating map in finitely many variables on normed spaces
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`
on a shell `ε / ‖c‖ < ‖m i‖ < ε` for some positive number `ε` and an elements `c
 : 𝕜`, `1 < ‖c‖`,
then it satisfies this inequality for all `m`.

If the domain is a Hausdorff space, then the continuity assumption is redundant,
see `bound_of_shell` below.
-/
theorem bound_of_shell_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hfc : Continuous f)
    {ε : ℝ} {C : ℝ} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ m : ι → E, (∀ i, ε / ‖c‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_continuous hfc (fun _ ↦ hε) (fun _ ↦ hc) hf m

/-- If an alternating map in finitely many variables on a seminormed space is continuous,
then it satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
for some `C` which can be chosen to be positive. -/
/-
**AlternatingMap.exists_bound_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngMap`。
形式化陈述：exists_bound_of_continuous (f : E [⋀^ι]->ₗ[𝕜] F) (hf : Continuous f) : exi
sts (C : Real), 0 < C ∧ (forall m, ‖f m‖ <= C * ∏ i, ‖m i‖)
参数：f : E [⋀^ι]->ₗ[𝕜] F；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.exists_bound_of_continuous`：exists_bound_of_continuous (f
 : MultilinearMap 𝕜 E G) (hf : Continuous f) : exists C : Real, 0 < C ∧ forall m
, ‖f m‖ <= C * ∏ i, ‖m i‖

--- 原说明 ---
If an alternating map in finitely many variables on a seminormed space is contin
uous,
then it satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
for some `C` which can be chosen to be positive.
-/
theorem exists_bound_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.1.exists_bound_of_continuous hf

/-- If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `AlternatingMap.norm_image_sub_le_of_bound` for a less precise but more usable version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
/-
**AlternatingMap.norm_image_sub_le_of_bound'** 是 Mathlib 中的一个定理，位于命名空间 `Alternat
ingMap`。
形式化陈述：norm_image_sub_le_of_bound' [DecidableEq ι] (f : E [⋀^ι]->ₗ[𝕜] F) {C : Rea
l} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : ι -> E) : ‖f m
₁ - f m₂‖ <= C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖
参数：f : E [⋀^ι]->ₗ[𝕜] F；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖；m₁ m₂ :
 ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound'`：norm_image_sub_le_of_bound' 
[DecidableEq ι] (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall 
m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ …

--- 原说明 ---
If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `AlternatingMap.norm_image_sub_le_of_bound` for a less precise but more usab
le version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n
‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by 
any `i`.
-/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

/-- If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a usable but not very precise version.
See `AlternatingMap.norm_image_sub_le_of_bound'` for a more precise but less usable version.
The bound is `‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
/-
**AlternatingMap.norm_image_sub_le_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngMap`。
形式化陈述：norm_image_sub_le_of_bound (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C) 
(H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) (m₁ m₂ : ι -> E) : ‖f m₁ - f m₂‖ <= C * 
(Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖
参数：f : E [⋀^ι]->ₗ[𝕜] F；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖；m₁ m₂ :
 ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.norm_image_sub_le_of_bound`：norm_image_sub_le_of_bound (f
 : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ 
i, ‖m i‖) (m₁ m₂ : forall i, E …

--- 原说明 ---
If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a usable but not very precise version.
See `AlternatingMap.norm_image_sub_le_of_bound'` for a more precise but less usa
ble version.
The bound is `‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 
1)`.
-/
theorem norm_image_sub_le_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

/-- If an alternating map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
then it is continuous. -/
/-
**AlternatingMap.continuous_of_bound** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：continuous_of_bound (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ 
<= C * ∏ i, ‖m i‖) : Continuous f
参数：f : E [⋀^ι]->ₗ[𝕜] F；C : Real；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.continuous_of_bound`：continuous_of_bound (f : Multilinear
Map 𝕜 E G) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : Continuous f

--- 原说明 ---
If an alternating map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
then it is continuous.
-/
theorem continuous_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    Continuous f :=
  f.toMultilinearMap.continuous_of_bound C H

/-- Construct a continuous alternating map
from an alternating map satisfying a boundedness condition. -/
/-
**AlternatingMap.mkContinuous** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：mkContinuous (f : E [⋀^ι]->ₗ[𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖) : E [⋀^ι]->L[𝕜] F
参数：f : E [⋀^ι]->ₗ[𝕜] F；C : Real；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.continuous_of_bound`：continuous_of_bound (f : E [⋀^ι]->ₗ[
𝕜] F) (C : Real) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : Continuous f

--- 原说明 ---
Construct a continuous alternating map
from an alternating map satisfying a boundedness condition.
-/
def mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [⋀^ι]→L[𝕜] F :=
  { f with cont := f.continuous_of_bound C H }
/-
**AlternatingMap.coe_mkContinuous** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ)   (H : ∀ (m : ι → E), ‖f m‖ ≤ C * ∏ i, ‖m i
‖), ⇑(f.mkContinuous C H) = ⇑f
参数：f : E [⋀^ι]→ₗ[𝕜] F；C : ℝ；H : ∀ (m : ι → E), ‖f m‖ ≤ C * ∏ i, ‖m i‖；f.mkContin
uous C H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    (f.mkContinuous C H : (ι → E) → F) = f :=
  rfl

end AlternatingMap

/-!
### Continuous alternating maps

We define the norm `‖f‖` of a continuous alternating map `f` in finitely many variables
as the smallest nonnegative number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.
We show that this defines a normed space structure on `E [⋀^ι]→L[𝕜] F`.
-/

namespace ContinuousAlternatingMap

variable [Fintype ι] {f : E [⋀^ι]→L[𝕜] F} {m : ι → E}

/-
**ContinuousAlternatingMap.bound** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlternatin
gMap`。
形式化陈述：bound (f : E [⋀^ι]->L[𝕜] F) : exists (C : Real), 0 < C ∧ (forall m, ‖f m‖ 
<= C * ∏ i, ‖m i‖)
参数：f : E [⋀^ι]->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.bound`：bound (f : ContinuousMultilinearMap 𝕜 E 
G) : exists C : Real, 0 < C ∧ forall m, ‖f m‖ <= C * ∏ i, ‖m i‖
-/
theorem bound (f : E [⋀^ι]→L[𝕜] F) : ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.toContinuousMultilinearMap.bound

/-- Continuous alternating maps form a seminormed additive commutative group.
We override projection to `PseudoMetricSpace` to ensure that instances commute
in `with_reducible_and_instances`. -/
/-
**ContinuousAlternatingMap.instSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 
`ContinuousAlternatingMap`。
形式化陈述：instSeminormedAddCommGroup : SeminormedAddCommGroup (E [⋀^ι]->L[𝕜] F) wher
e toPseudoMetricSpace
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Continuous alternating maps form a seminormed additive commutative group.
We override projection to `PseudoMetricSpace` to ensure that instances commute
in `with_reducible_and_instances`.
-/
instance instSeminormedAddCommGroup : SeminormedAddCommGroup (E [⋀^ι]→L[𝕜] F) where
  toPseudoMetricSpace := .induced toContinuousMultilinearMap inferInstance
  __ := SeminormedAddCommGroup.induced _ _ (toMultilinearAddHom : E [⋀^ι]→L[𝕜] F →+ _)
  norm f := ‖f.toContinuousMultilinearMap‖
/-
**ContinuousAlternatingMap.norm_toContinuousMultilinearMap** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] (f : E [⋀^ι]→L[𝕜] F), ‖f.toContinuousMultilinearMap‖ = ‖f‖
参数：f : E [⋀^ι]→L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem norm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖ = ‖f‖ := rfl
/-
**ContinuousAlternatingMap.nnnorm_toContinuousMultilinearMap** 是 Mathlib 中的一个定理，
位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] (f : E [⋀^ι]→L[𝕜] F), ‖f.toContinuousMultilinearMap‖₊ = ‖f‖₊
参数：f : E [⋀^ι]→L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem nnnorm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖₊ = ‖f‖₊ := rfl
/-
**ContinuousAlternatingMap.enorm_toContinuousMultilinearMap** 是 Mathlib 中的一个定理，位
于命名空间 `ContinuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] (f : E [⋀^ι]→L[𝕜] F), ‖f.toContinuousMultilinearMap‖ₑ = ‖f‖ₑ
参数：f : E [⋀^ι]→L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem enorm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖ₑ = ‖f‖ₑ := rfl

/-- The inclusion of `E [⋀^ι]→L[𝕜] F` into `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F`
as a linear isometry. -/
@[simps!]
/-
**ContinuousAlternatingMap.toContinuousMultilinearMapLI** 是 Mathlib 中的一个定义，位于命名空
间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMapLI : E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜] ContinuousMultiline
arMap 𝕜 (fun _ : ι => E) F where toLinearMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `E [⋀^ι]→L[𝕜] F` into `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ 
E) F`
as a linear isometry.
-/
def toContinuousMultilinearMapLI :
    E [⋀^ι]→L[𝕜] F →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F where
  toLinearMap := toContinuousMultilinearMapLinear
  norm_map' _ := rfl
/-
**ContinuousAlternatingMap.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlterna
tingMap`。
形式化陈述：norm_def (f : E [⋀^ι]->L[𝕜] F) : ‖f‖ = sInf {c : Real | 0 <= c ∧ forall m,
 ‖f m‖ <= c * ∏ i, ‖m i‖}
参数：f : E [⋀^ι]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (f : E [⋀^ι]→L[𝕜] F) :
    ‖f‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  rfl
/-
**ContinuousAlternatingMap.bounds_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：bounds_nonempty : exists c, c in {c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i,
 ‖m i‖}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.bounds_nonempty`：bounds_nonempty {f : Continuou
sMultilinearMap 𝕜 E G} : exists c, c in { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ 
i, ‖m i‖ }
-/
theorem bounds_nonempty :
    ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_nonempty
/-
**ContinuousAlternatingMap.bounds_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：bounds_bddBelow {f : E [⋀^ι]->L[𝕜] F} : BddBelow {c | 0 <= c ∧ forall m, ‖
f m‖ <= c * ∏ i, ‖m i‖}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.bounds_bddBelow`：bounds_bddBelow {f : Continuou
sMultilinearMap 𝕜 E G} : BddBelow { c | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, ‖m 
i‖ }
-/
theorem bounds_bddBelow {f : E [⋀^ι]→L[𝕜] F} :
    BddBelow {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_bddBelow
/-
**ContinuousAlternatingMap.isLeast_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：isLeast_opNorm (f : E [⋀^ι]->L[𝕜] F) : IsLeast {c : Real | 0 <= c ∧ forall
 m, ‖f m‖ <= c * ∏ i, ‖m i‖} ‖f‖
参数：f : E [⋀^ι]->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.isLeast_opNorm`：isLeast_opNorm (f : ContinuousM
ultilinearMap 𝕜 E G) : IsLeast {c : Real | 0 <= c ∧ forall m, ‖f m‖ <= c * ∏ i, 
‖m i‖} ‖f‖
-/
theorem isLeast_opNorm (f : E [⋀^ι]→L[𝕜] F) :
    IsLeast {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} ‖f‖ :=
  f.1.isLeast_opNorm

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
/-
**ContinuousAlternatingMap.le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：le_opNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
参数：f : E [⋀^ι]->L[𝕜] F；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖

--- 原说明 ---
The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`.
-/
theorem le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.1.le_opNorm m
/-
**ContinuousAlternatingMap.le_mul_prod_of_opNorm_le_of_le** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousAlternatingMap`。
形式化陈述：le_mul_prod_of_opNorm_le_of_le {m : ι -> E} {C : Real} {b : ι -> Real} (hC
 : ‖f‖ <= C) (hm : forall i, ‖m i‖ <= b i) : ‖f m‖ <= C * ∏ i, b i
参数：hC : ‖f‖ <= C；hm : forall i, ‖m i‖ <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le`：le_mul_prod_of_
opNorm_le_of_le {f : ContinuousMultilinearMap 𝕜 E G} {m : forall i, E i} {C : Re
al} {b : ι -> Real} (hC : ‖f‖ <= C) (hm : for…
-/
theorem le_mul_prod_of_opNorm_le_of_le
    {m : ι → E} {C : ℝ} {b : ι → ℝ} (hC : ‖f‖ ≤ C) (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ C * ∏ i, b i :=
  f.1.le_mul_prod_of_opNorm_le_of_le hC hm
/-
**ContinuousAlternatingMap.le_opNorm_mul_prod_of_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousAlternatingMap`。
形式化陈述：le_opNorm_mul_prod_of_le (f : E [⋀^ι]->L[𝕜] F) {b : ι -> Real} (hm : foral
l i, ‖m i‖ <= b i) : ‖f m‖ <= ‖f‖ * ∏ i, b i
参数：f : E [⋀^ι]->L[𝕜] F；hm : forall i, ‖m i‖ <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_prod_of_le`：le_opNorm_mul_prod_of
_le (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} {b : ι -> Real} (hm
 : forall i, ‖m i‖ <= b i) : ‖f m‖ <= ‖…
-/
theorem le_opNorm_mul_prod_of_le (f : E [⋀^ι]→L[𝕜] F) {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
  f.1.le_opNorm_mul_prod_of_le hm
/-
**ContinuousAlternatingMap.le_opNorm_mul_pow_card_of_le** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAlternatingMap`。
形式化陈述：le_opNorm_mul_pow_card_of_le (f : E [⋀^ι]->L[𝕜] F) {m b} (hm : ‖m‖ <= b) :
 ‖f m‖ <= ‖f‖ * b ^ Fintype.card ι
参数：f : E [⋀^ι]->L[𝕜] F；hm : ‖m‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_pow_card_of_le`：le_opNorm_mul_pow
_card_of_le (f : ContinuousMultilinearMap 𝕜 E G) {m b} (hm : ‖m‖ <= b) : ‖f m‖ <
= ‖f‖ * b ^ Fintype.card ι
-/
theorem le_opNorm_mul_pow_card_of_le (f : E [⋀^ι]→L[𝕜] F) {m b} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ Fintype.card ι :=
  f.1.le_opNorm_mul_pow_card_of_le hm
/-
**ContinuousAlternatingMap.le_opNorm_mul_pow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAlternatingMap`。
形式化陈述：le_opNorm_mul_pow_of_le {n} (f : E [⋀^Fin n]->L[𝕜] F) {m b} (hm : ‖m‖ <= b
) : ‖f m‖ <= ‖f‖ * b ^ n
参数：f : E [⋀^Fin n]->L[𝕜] F；hm : ‖m‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_pow_of_le`：le_opNorm_mul_pow_of_l
e {n : Nat} {Ei : Fin n -> Type*} [forall i, SeminormedAddCommGroup (Ei i)] [for
all i, NormedSpace 𝕜 (Ei i)] (f : Cont…
-/
theorem le_opNorm_mul_pow_of_le {n} (f : E [⋀^Fin n]→L[𝕜] F) {m b} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ n :=
  f.1.le_opNorm_mul_pow_of_le hm
/-
**ContinuousAlternatingMap.le_of_opNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：le_of_opNorm_le {C : Real} (h : ‖f‖ <= C) (m : ι -> E) : ‖f m‖ <= C * ∏ i,
 ‖m i‖
参数：h : ‖f‖ <= C；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_of_opNorm_le`：le_of_opNorm_le {f : Continuou
sMultilinearMap 𝕜 E G} {C : Real} (h : ‖f‖ <= C) (m : forall i, E i) : ‖f m‖ <= 
C * ∏ i, ‖m i‖
-/
theorem le_of_opNorm_le {C : ℝ} (h : ‖f‖ ≤ C) (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.le_of_opNorm_le h m
/-
**ContinuousAlternatingMap.ratio_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：ratio_le_opNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖ / ∏ i, ‖m i‖ <=
 ‖f‖
参数：f : E [⋀^ι]->L[𝕜] F；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.ratio_le_opNorm`：ratio_le_opNorm (f : Continuou
sMultilinearMap 𝕜 E G) (m : forall i, E i) : (‖f m‖ / ∏ i, ‖m i‖) <= ‖f‖
-/
theorem ratio_le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ / ∏ i, ‖m i‖ ≤ ‖f‖ :=
  f.1.ratio_le_opNorm m

/-- The image of the unit ball under a continuous alternating map is bounded. -/
/-
**ContinuousAlternatingMap.unit_le_opNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lternatingMap`。
形式化陈述：unit_le_opNorm (f : E [⋀^ι]->L[𝕜] F) (h : ‖m‖ <= 1) : ‖f m‖ <= ‖f‖
参数：f : E [⋀^ι]->L[𝕜] F；h : ‖m‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.unit_le_opNorm`：unit_le_opNorm (f : ContinuousM
ultilinearMap 𝕜 E G) {m : forall i, E i} (h : ‖m‖ <= 1) : ‖f m‖ <= ‖f‖

--- 原说明 ---
The image of the unit ball under a continuous alternating map is bounded.
-/
theorem unit_le_opNorm (f : E [⋀^ι]→L[𝕜] F) (h : ‖m‖ ≤ 1) : ‖f m‖ ≤ ‖f‖ := f.1.unit_le_opNorm h

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
/-
**ContinuousAlternatingMap.opNorm_le_bound** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：opNorm_le_bound (f : E [⋀^ι]->L[𝕜] F) {M : Real} (hMp : 0 <= M) (hM : fora
ll m, ‖f m‖ <= M * ∏ i, ‖m i‖) : ‖f‖ <= M
参数：f : E [⋀^ι]->L[𝕜] F；hMp : 0 <= M；hM : forall m, ‖f m‖ <= M * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M

--- 原说明 ---
If one controls the norm of every `f x`, then one controls the norm of `f`.
-/
theorem opNorm_le_bound (f : E [⋀^ι]→L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) : ‖f‖ ≤ M :=
  f.1.opNorm_le_bound hMp hM
/-
**ContinuousAlternatingMap.opNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：opNorm_le_iff {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖
参数：hC : 0 <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_iff`：opNorm_le_iff {f : ContinuousMul
tilinearMap 𝕜 E G} {C : Real} (hC : 0 <= C) : ‖f‖ <= C ↔ forall m, ‖f m‖ <= C * 
∏ i, ‖m i‖
-/
theorem opNorm_le_iff {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.opNorm_le_iff hC

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
/-
**ContinuousAlternatingMap.le_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：le_opNNNorm (f : E [⋀^ι]->L[𝕜] F) (m : ι -> E) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m 
i‖₊
参数：f : E [⋀^ι]->L[𝕜] F；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNNNorm`：le_opNNNorm (f : ContinuousMultili
nearMap 𝕜 E G) (m : forall i, E i) : ‖f m‖₊ <= ‖f‖₊ * ∏ i, ‖m i‖₊

--- 原说明 ---
The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version.
-/
theorem le_opNNNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ :=
  f.1.le_opNNNorm m
/-
**ContinuousAlternatingMap.le_of_opNNNorm_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：le_of_opNNNorm_le {C : Real>=0} (h : ‖f‖₊ <= C) (m : ι -> E) : ‖f m‖₊ <= C
 * ∏ i, ‖m i‖₊
参数：h : ‖f‖₊ <= C；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_of_opNNNorm_le`：le_of_opNNNorm_le (f : Conti
nuousMultilinearMap 𝕜 E G) {C : Real>=0} (h : ‖f‖₊ <= C) (m : forall i, E i) : ‖
f m‖₊ <= C * ∏ i, ‖m i‖₊
-/
theorem le_of_opNNNorm_le {C : ℝ≥0} (h : ‖f‖₊ ≤ C) (m : ι → E) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  f.1.le_of_opNNNorm_le h m
/-
**ContinuousAlternatingMap.opNNNorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：opNNNorm_le_iff {C : Real>=0} : ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, ‖
m i‖₊
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNNNorm_le_iff`：opNNNorm_le_iff {f : Continuou
sMultilinearMap 𝕜 E G} {C : Real>=0} : ‖f‖₊ <= C ↔ forall m, ‖f m‖₊ <= C * ∏ i, 
‖m i‖₊
-/
theorem opNNNorm_le_iff {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  f.1.opNNNorm_le_iff
/-
**ContinuousAlternatingMap.isLeast_opNNNorm** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlternatingMap`。
形式化陈述：isLeast_opNNNorm (f : E [⋀^ι]->L[𝕜] F) : IsLeast {C : Real>=0 | forall m, 
‖f m‖₊ <= C * ∏ i, ‖m i‖₊} ‖f‖₊
参数：f : E [⋀^ι]->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.isLeast_opNNNorm`：isLeast_opNNNorm (f : Continu
ousMultilinearMap 𝕜 E G) : IsLeast {C : Real>=0 | forall m, ‖f m‖₊ <= C * ∏ i, ‖
m i‖₊} ‖f‖₊
-/
theorem isLeast_opNNNorm (f : E [⋀^ι]→L[𝕜] F) :
    IsLeast {C : ℝ≥0 | ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊} ‖f‖₊ :=
  f.1.isLeast_opNNNorm
/-
**ContinuousAlternatingMap.opNNNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
ternatingMap`。
形式化陈述：opNNNorm_prod (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G) : ‖f.prod g‖₊ = 
max (‖f‖₊) (‖g‖₊)
参数：f : E [⋀^ι]->L[𝕜] F；g : E [⋀^ι]->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNNNorm_prod`：opNNNorm_prod (f : ContinuousMul
tilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') : ‖f.prod g‖₊ = max ‖f‖
₊ ‖g‖₊
-/
theorem opNNNorm_prod (f : E [⋀^ι]→L[𝕜] F) (g : E [⋀^ι]→L[𝕜] G) :
    ‖f.prod g‖₊ = max (‖f‖₊) (‖g‖₊) :=
  f.1.opNNNorm_prod g.1
/-
**ContinuousAlternatingMap.opNorm_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：opNorm_prod (f : E [⋀^ι]->L[𝕜] F) (g : E [⋀^ι]->L[𝕜] G) : ‖f.prod g‖ = max
 (‖f‖) (‖g‖)
参数：f : E [⋀^ι]->L[𝕜] F；g : E [⋀^ι]->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_prod`：opNorm_prod (f : ContinuousMultili
nearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') : ‖f.prod g‖ = max ‖f‖ ‖g‖
-/
theorem opNorm_prod (f : E [⋀^ι]→L[𝕜] F) (g : E [⋀^ι]→L[𝕜] G) : ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
  f.1.opNorm_prod g.1
/-
**ContinuousAlternatingMap.opNNNorm_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlte
rnatingMap`。
形式化陈述：opNNNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', Semino
rmedAddCommGroup (F i')] [forall i', NormedSpace 𝕜 (F i')] (f : forall i', E [⋀^
ι]->L[𝕜] F i') : ‖pi f‖₊ = ‖f‖₊
参数：F i'；F i'；f : forall i', E [⋀^ι]->L[𝕜] F i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNNNorm_pi`：opNNNorm_pi [forall i', Seminormed
AddCommGroup (E' i')] [forall i', NormedSpace 𝕜 (E' i')] (f : forall i', Continu
ousMultilinearMap 𝕜 E (E' …
-/
theorem opNNNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', SeminormedAddCommGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] (f : ∀ i', E [⋀^ι]→L[𝕜] F i') : ‖pi f‖₊ = ‖f‖₊ :=
  ContinuousMultilinearMap.opNNNorm_pi fun i ↦ (f i).1
/-
**ContinuousAlternatingMap.opNorm_pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAltern
atingMap`。
形式化陈述：opNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', Seminorm
edAddCommGroup (F i')] [forall i', NormedSpace 𝕜 (F i')] (f : forall i', E [⋀^ι]
->L[𝕜] F i') : ‖pi f‖ = ‖f‖
参数：F i'；F i'；f : forall i', E [⋀^ι]->L[𝕜] F i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_pi`：opNorm_pi {ι' : Type v'} [Fintype ι'
] {E' : ι' -> Type wE'} [forall i', SeminormedAddCommGroup (E' i')] [forall i', 
NormedSpace 𝕜 (E' i')] (…
-/
theorem opNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', SeminormedAddCommGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] (f : ∀ i', E [⋀^ι]→L[𝕜] F i') : ‖pi f‖ = ‖f‖ :=
  ContinuousMultilinearMap.opNorm_pi fun i ↦ (f i).1
/-
**ContinuousAlternatingMap.instNormedSpace** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
AlternatingMap`。
形式化陈述：instNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulComm
Class 𝕜 𝕜' F] : NormedSpace 𝕜' (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    NormedSpace 𝕜' (E [⋀^ι]→L[𝕜] F) :=
  ⟨fun c f ↦ f.1.opNorm_smul_le c⟩

section

/-
**ContinuousAlternatingMap.norm_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] [inst_6 : Subsingleton ι] (i : ι) (f : E →L[𝕜] F),   ‖(ContinuousAlterna
tingMap.ofSubsingleton 𝕜 E F i) f‖ = ‖f‖
参数：i : ι；f : E →L[𝕜] F；ContinuousAlternatingMap.ofSubsingleton 𝕜 E F i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton`：norm_ofSubsingleton [Subsi
ngleton ι] (i : ι) (f : G ->L[𝕜] G') : ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖
-/
@[simp] theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖ = ‖f‖ :=
  ContinuousMultilinearMap.norm_ofSubsingleton i f
/-
**ContinuousAlternatingMap.nnnorm_ofSubsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] [inst_6 : Subsingleton ι] (i : ι) (f : E →L[𝕜] F),   ‖(ContinuousAlterna
tingMap.ofSubsingleton 𝕜 E F i) f‖₊ = ‖f‖₊
参数：i : ι；f : E →L[𝕜] F；ContinuousAlternatingMap.ofSubsingleton 𝕜 E F i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousAlternatingMap.norm_ofSubsingleton`：∀ {𝕜 : Type u} {E : Type w
E} {F : Type wF} {ι : Type v} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Sem
inormedAddCommGroup E] [inst_2 : N…
-/
@[simp] theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖₊ = ‖f‖₊ :=
  NNReal.eq <| norm_ofSubsingleton i f

/-- `ContinuousAlternatingMap.ofSubsingleton` as a linear isometry. -/
@[simps +simpRhs]
/-
**ContinuousAlternatingMap.ofSubsingletonLIE** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：ofSubsingletonLIE [Subsingleton ι] (i : ι) : (E ->L[𝕜] F) ≃ₗᵢ[𝕜] (E [⋀^ι]-
>L[𝕜] F) where __
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.norm_ofSubsingleton`：∀ {𝕜 : Type u} {E : Type w
E} {F : Type wF} {ι : Type v} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Sem
inormedAddCommGroup E] [inst_2 : N…

--- 原说明 ---
`ContinuousAlternatingMap.ofSubsingleton` as a linear isometry.
-/
def ofSubsingletonLIE [Subsingleton ι] (i : ι) : (E →L[𝕜] F) ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] F) where
  __ := ofSubsingleton 𝕜 E F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_ofSubsingleton i
/-
**ContinuousAlternatingMap.norm_ofSubsingleton_id_le** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousAlternatingMap`。
形式化陈述：norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 E E
 i (.id _ _)‖ <= 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton_id_le`：norm_ofSubsingleton_
id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ <= 1
-/
theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖ ≤ 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id_le ..
/-
**ContinuousAlternatingMap.nnnorm_ofSubsingleton_id_le** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousAlternatingMap`。
形式化陈述：nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 E
 E i (.id _ _)‖₊ <= 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le`：nnnorm_ofSubsingle
ton_id_le [Subsingleton ι] (i : ι) : ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ <= 1
-/
theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖₊ ≤ 1 :=
  ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le ..

variable (𝕜 E)
/-
**ContinuousAlternatingMap.norm_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAlternatingMap`。
形式化陈述：∀ (𝕜 : Type u) (E : Type wE) {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] [inst_6 : IsEmpty ι] (x : F),   ‖ContinuousAlternatingMap.constOfIsEmpty
 𝕜 E ι x‖ = ‖x‖
参数：𝕜 : Type u；E : Type wE；x : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_constOfIsEmpty`：norm_constOfIsEmpty [IsEmp
ty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖
-/
@[simp] theorem norm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖ :=
  ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _
/-
**ContinuousAlternatingMap.nnnorm_constOfIsEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousAlternatingMap`。
形式化陈述：∀ (𝕜 : Type u) (E : Type wE) {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] [inst_6 : IsEmpty ι] (x : F),   ‖ContinuousAlternatingMap.constOfIsEmpty
 𝕜 E ι x‖₊ = ‖x‖₊
参数：𝕜 : Type u；E : Type wE；x : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousAlternatingMap.norm_constOfIsEmpty`：∀ (𝕜 : Type u) (E : Type w
E) {F : Type wF} {ι : Type v} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Sem
inormedAddCommGroup E] [inst_2 : N…
-/
@[simp] theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

variable (ι F) in
/-- `constOfIsEmpty` as a linear isometry equivalence. -/
@[simps]
/-
**ContinuousAlternatingMap.constOfIsEmptyLIE** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：constOfIsEmptyLIE [IsEmpty ι] : F ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] F) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.norm_constOfIsEmpty`：∀ (𝕜 : Type u) (E : Type w
E) {F : Type wF} {ι : Type v} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Sem
inormedAddCommGroup E] [inst_2 : N…

--- 原说明 ---
`constOfIsEmpty` as a linear isometry equivalence.
-/
def constOfIsEmptyLIE [IsEmpty ι] : F ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] F) where
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
/-
**ContinuousAlternatingMap.prodLIE** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternat
ingMap`。
形式化陈述：prodLIE : (E [⋀^ι]->L[𝕜] F) × (E [⋀^ι]->L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (F ×
 G)) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlternatingMap.prod` as a `LinearIsometryEquiv`.
-/
def prodLIE : (E [⋀^ι]→L[𝕜] F) × (E [⋀^ι]→L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] (F × G)) where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 F G).compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 F G).compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

variable (𝕜 E) in
/-- `ContinuousAlternatingMap.pi` as a `LinearIsometryEquiv`. -/
@[simps!]
/-
**ContinuousAlternatingMap.piLIE** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlternatin
gMap`。
形式化陈述：piLIE {ι' : Type*} [Fintype ι'] {F : ι' -> Type*} [forall i', SeminormedAd
dCommGroup (F i')] [forall i', NormedSpace 𝕜 (F i')] : (forall i', E [⋀^ι]->L[𝕜]
 F i') ≃ₗᵢ[𝕜] (E [⋀^ι]->L[𝕜] (forall i, F i)) where toLinearEquiv
参数：F i'；F i'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlternatingMap.opNorm_pi`：opNorm_pi {ι' : Type*} [Fintype ι'] 
{F : ι' -> Type*} [forall i', SeminormedAddCommGroup (F i')] [forall i', NormedS
pace 𝕜 (F i')] (f : fora…

--- 原说明 ---
`ContinuousAlternatingMap.pi` as a `LinearIsometryEquiv`.
-/
def piLIE {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', SeminormedAddCommGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] :
    (∀ i', E [⋀^ι]→L[𝕜] F i') ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] (∀ i, F i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

section restrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

/-
**ContinuousAlternatingMap.norm_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAlternatingMap`。
形式化陈述：∀ {𝕜 : Type u} {E : Type wE} {F : Type wF} {ι : Type v} [inst : Nontrivial
lyNormedField 𝕜]   [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E
] [inst_3 : SeminormedAddCommGroup F]   [inst_4 : NormedSpace 𝕜 F] [inst_5 : Fin
type ι] {f : E [⋀^ι]→L[𝕜] F} {𝕜' : Type u_1}   [inst_6 : NontriviallyNormedField
 𝕜'] [inst_7 : NormedAlgebra 𝕜' 𝕜] [inst_8 : NormedSpace 𝕜' F]   [inst_9 : IsSca
larTower 𝕜' 𝕜 F] [inst_10 : NormedSpace 𝕜' E] [inst_11 : IsScalarTower 𝕜' 𝕜 E], 
  ‖ContinuousAlternatingMap.restrictScalars 𝕜' f‖ = ‖f‖
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem norm_restrictScalars : ‖f.restrictScalars 𝕜'‖ = ‖f‖ := rfl

variable (𝕜')

/-- `ContinuousAlternatingMap.restrictScalars` as a `LinearIsometry`. -/
@[simps]
/-
**ContinuousAlternatingMap.restrictScalarsLI** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：restrictScalarsLI : E [⋀^ι]->L[𝕜] F ->ₗᵢ[𝕜'] E [⋀^ι]->L[𝕜'] F where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlternatingMap.restrictScalars` as a `LinearIsometry`.
-/
def restrictScalarsLI : E [⋀^ι]→L[𝕜] F →ₗᵢ[𝕜'] E [⋀^ι]→L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end restrictScalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
/-
**ContinuousAlternatingMap.norm_image_sub_le'** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousAlternatingMap`。
形式化陈述：norm_image_sub_le' [DecidableEq ι] (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E) 
: ‖f m₁ - f m₂‖ <= ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖
m₂ j‖
参数：f : E [⋀^ι]->L[𝕜] F；m₁ m₂ : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_image_sub_le'`：norm_image_sub_le' [Decidab
leEq ι] (f : ContinuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i) : ‖f m₁ - f
 m₂‖ <= ‖f‖ * ∑ i, ∏ j, if j = i …

--- 原说明 ---
The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, pr
ecise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound r
eads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m'
 n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by 
any `i`.
-/
theorem norm_image_sub_le' [DecidableEq ι] (f : E [⋀^ι]→L[𝕜] F) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.1.norm_image_sub_le' m₁ m₂

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`,
less precise version.
For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
/-
**ContinuousAlternatingMap.norm_image_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAlternatingMap`。
形式化陈述：norm_image_sub_le (f : E [⋀^ι]->L[𝕜] F) (m₁ m₂ : ι -> E) : ‖f m₁ - f m₂‖ <
= ‖f‖ * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖
参数：f : E [⋀^ι]->L[𝕜] F；m₁ m₂ : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_image_sub_le`：norm_image_sub_le (f : Conti
nuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i) : ‖f m₁ - f m₂‖ <= ‖f‖ * Fint
ype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fi…

--- 原说明 ---
The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`,
less precise version.
For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι 
- 1)`.
-/
theorem norm_image_sub_le (f : E [⋀^ι]→L[𝕜] F) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.1.norm_image_sub_le m₁ m₂

end ContinuousAlternatingMap

variable [Fintype ι]

/-- If a continuous alternating map is constructed from an alternating map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
/-
**AlternatingMap.mkContinuous_norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlternatingMap.mkContinuous_norm_le (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC :
 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= C
参数：f : E [⋀^ι]->ₗ[𝕜] F；hC : 0 <= C；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkContinuous_norm_le`：MultilinearMap.mkContinuous_norm_le
 (f : MultilinearMap 𝕜 E G) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C *
 ∏ i, ‖m i‖) : ‖f.mkConti…

--- 原说明 ---
If a continuous alternating map is constructed from an alternating map via the c
onstructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor i
f it is
nonnegative.
-/
theorem AlternatingMap.mkContinuous_norm_le (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  f.toMultilinearMap.mkContinuous_norm_le hC H

/-- If a continuous alternating map is constructed from an alternating map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
/-
**AlternatingMap.mkContinuous_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlternatingMap.mkContinuous_norm_le' (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (H :
 forall m, ‖f m‖ <= C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ <= max C 0
参数：f : E [⋀^ι]->ₗ[𝕜] F；H : forall m, ‖f m‖ <= C * ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If a continuous alternating map is constructed from an alternating map via the c
onstructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor i
f it is
nonnegative.
-/
theorem AlternatingMap.mkContinuous_norm_le' (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ}
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ max C 0 :=
  ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m ↦ (H m).trans <| by
    gcongr
    apply le_max_left

namespace ContinuousLinearMap

/-
**ContinuousLinearMap.norm_compContinuousAlternatingMap_le** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousLinearMap`。
形式化陈述：norm_compContinuousAlternatingMap_le (g : F ->L[𝕜] G) (f : E [⋀^ι]->L[𝕜] F
) : ‖g.compContinuousAlternatingMap f‖ <= ‖g‖ * ‖f‖
参数：g : F ->L[𝕜] G；f : E [⋀^ι]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`：norm_compConti
nuousMultilinearMap_le (g : G ->L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) : 
‖g.compContinuousMultilinearMap f‖ <= ‖g‖ * ‖f…
-/
theorem norm_compContinuousAlternatingMap_le (g : F →L[𝕜] G) (f : E [⋀^ι]→L[𝕜] F) :
    ‖g.compContinuousAlternatingMap f‖ ≤ ‖g‖ * ‖f‖ :=
  g.norm_compContinuousMultilinearMap_le f.1

/-- Flip arguments in `f : F →L[𝕜] E [⋀^ι]→L[𝕜] G` to get `⋀^ι⟮𝕜; E; F →L[𝕜] G⟯` -/
@[simps! apply_apply]
/-
**ContinuousLinearMap.flipAlternating** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：flipAlternating (f : F ->L[𝕜] (E [⋀^ι]->L[𝕜] G)) : E [⋀^ι]->L[𝕜] (F ->L[𝕜]
 G) where toContinuousMultilinearMap
参数：f : F ->L[𝕜] (E [⋀^ι]->L[𝕜] G)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Flip arguments in `f : F →L[𝕜] E [⋀^ι]→L[𝕜] G` to get `⋀^ι⟮𝕜; E; F →L[𝕜] G⟯`
-/
def flipAlternating (f : F →L[𝕜] (E [⋀^ι]→L[𝕜] G)) : E [⋀^ι]→L[𝕜] (F →L[𝕜] G) where
  toContinuousMultilinearMap :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

end ContinuousLinearMap

/-
**LinearIsometry.norm_compContinuousAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.norm_compContinuousAlternatingMap (g : F ->ₗᵢ[𝕜] G) (f : E 
[⋀^ι]->L[𝕜] F) : ‖g.toContinuousLinearMap.compContinuousAlternatingMap f‖ = ‖f‖
参数：g : F ->ₗᵢ[𝕜] G；f : E [⋀^ι]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_compContinuousMultilinearMap`：LinearIsometry.norm_co
mpContinuousMultilinearMap (g : G ->ₗᵢ[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E 
G) : ‖g.toContinuousLinearMap.compCont…
-/
theorem LinearIsometry.norm_compContinuousAlternatingMap (g : F →ₗᵢ[𝕜] G) (f : E [⋀^ι]→L[𝕜] F) :
    ‖g.toContinuousLinearMap.compContinuousAlternatingMap f‖ = ‖f‖ :=
  g.norm_compContinuousMultilinearMap f.1

open ContinuousAlternatingMap

section

namespace ContinuousAlternatingMap

/-
**ContinuousAlternatingMap.norm_compContinuousLinearMap_le** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAlternatingMap`。
形式化陈述：norm_compContinuousLinearMap_le (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F) : ‖
f.compContinuousLinearMap g‖ <= ‖f‖ * (‖g‖ ^ Fintype.card ι)
参数：f : F [⋀^ι]->L[𝕜] G；g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ContinuousMultilinearMap.norm_compContinuousLinearMap_le`：norm_compConti
nuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G) (f : forall i, E i ->L[𝕜
] E₁ i) : ‖g.compContinuousLinearMap f‖ <= ‖g‖…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_compContinuousLinearMap_le (f : F [⋀^ι]→L[𝕜] G)
    (g : E →L[𝕜] F) : ‖f.compContinuousLinearMap g‖ ≤ ‖f‖ * (‖g‖ ^ Fintype.card ι) :=
  (f.1.norm_compContinuousLinearMap_le _).trans_eq <| by simp

omit [Fintype ι] in
/-
**ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：continuous_compContinuousLinearMapCLM [Finite ι] : Continuous (compContinu
ousLinearMapCLM : (E ->L[𝕜] F) -> (F [⋀^ι]->L[𝕜] G) ->L[𝕜] (E [⋀^ι]->L[𝕜] G))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `UniformConvergenceCLM.isUniformInducing_postcomp`：isUniformInducing_post
comp [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] {𝕜₃ : Type*} [Norme
dField 𝕜₃] [Module 𝕜₃ G] {τ : 𝕜₂ ->+* …
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用引理 `ContinuousAlternatingMap.isUniformEmbedding_toContinuousMultilinearMap`：
isUniformEmbedding_toContinuousMultilinearMap : IsUniformEmbedding (toContinuous
MultilinearMap : (E [⋀^ι]->L[𝕜] F) -> _) where injective
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem continuous_compContinuousLinearMapCLM [Finite ι] :
    Continuous
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) := by
  rcases nonempty_fintype ι
  refine UniformConvergenceCLM.isUniformInducing_postcomp (.id 𝕜)
    (toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]→L[𝕜] G) →L[𝕜] _)
    isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing _ |>.isInducing
    |>.continuous_iff |>.mpr ?_
  change Continuous <|
    (toContinuousMultilinearMapCLM 𝕜 : (F [⋀^ι]→L[𝕜] G) →L[𝕜] _).precomp _ ∘
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι ↦ E) (fun _ ↦ F) G ∘
      (fun f _ ↦ f)
  fun_prop

variable [DecidableEq ι]

/-- Fréchet derivative of `compContinuousLinearMap f g` with respect to `g`.

Recall that `compContinuousLinearMap f g` is the pullback of `f : F [⋀^ι]→L[𝕜] G`
along `g : E →L[𝕜] F`.

This function is linear in `f`, so its derivative with respect to `f`
is given by `compContinuousLinearMapCLM f g`.

The derivative with respect to `g` is given by
`f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)`,
see `fderivCompContinuousLinearMap_apply` below.
-/
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名
空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMap (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜] F) : (E 
->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] G)
参数：f : F [⋀^ι]->L[𝕜] G；g : E ->L[𝕜] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Fréchet derivative of `compContinuousLinearMap f g` with respect to `g`.

Recall that `compContinuousLinearMap f g` is the pullback of `f : F [⋀^ι]→L[𝕜] G
`
along `g : E →L[𝕜] F`.

This function is linear in `f`, so its derivative with respect to `f`
is given by `compContinuousLinearMapCLM f g`.

The derivative with respect to `g` is given by
`f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j ↦ Function.update (fun _ 
↦ g) i dg j (v j)`,
see `fderivCompContinuousLinearMap_apply` below.
-/
def fderivCompContinuousLinearMap (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    (E →L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
  liftCLM (f.1.fderivCompContinuousLinearMap (fun _ : ι ↦ g) ∘L .pi fun _ ↦ .id _ _) <| by
    intro dg v a b heq hne
    trans ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)
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
/-
**ContinuousAlternatingMap.toContinuousMultilinearMapCLM_comp_fderivCompContinuo
usLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap (f : F [⋀
^ι]->L[𝕜] G) (g : E ->L[𝕜] F) : toContinuousMultilinearMapCLM 𝕜 ∘L f.fderivCompC
ontinuousLinearMap g = f.1.fderivCompContinuousLinearMap (fun _ : ι => g) ∘L .pi
 fun _ => .id _ _
参数：f : F [⋀^ι]->L[𝕜] G；g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap
    (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    toContinuousMultilinearMapCLM 𝕜 ∘L f.fderivCompContinuousLinearMap g =
      f.1.fderivCompContinuousLinearMap (fun _ : ι ↦ g) ∘L .pi fun _ ↦ .id _ _ :=
  rfl

@[simp]
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply** 是 Mathlib 中的一个引
理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMap_apply (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜]
 F) (v : ι -> E) : f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j => Func
tion.update (fun _ => g) i dg j (v j)
参数：f : F [⋀^ι]->L[𝕜] G；g dg : E ->L[𝕜] F；v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply`：fderivComp
ContinuousLinearMap_apply [DecidableEq ι] (f : ContinuousMultilinearMap 𝕜 E₁ G) 
(g : forall i, E i ->L[𝕜] E₁ i) (dg : forall i, E …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCompContinuousLinearMap_apply (f : F [⋀^ι]→L[𝕜] G) (g dg : E →L[𝕜] F) (v : ι → E) :
    f.fderivCompContinuousLinearMap g dg v =
      ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j) := by
  simp [fderivCompContinuousLinearMap]

@[nontriviality]
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMap_of_isEmpty** 是 Mathlib 
中的一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMap_of_isEmpty [IsEmpty ι] : fderivCompContinuou
sLinearMap (ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `ContinuousAlternatingMap.ext`：ext {f g : M [⋀^ι]->L[R] N} (H : forall x,
 f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply`：fderivComp
ContinuousLinearMap_apply (f : F [⋀^ι]->L[𝕜] G) (g dg : E ->L[𝕜] F) (v : ι -> E)
 : f.fderivCompContinuousLinearMap g dg v = ∑ i, f…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivCompContinuousLinearMap_of_isEmpty [IsEmpty ι] :
    fderivCompContinuousLinearMap (ι := ι) (𝕜 := 𝕜) (E := E) (F := F) (G := G) = 0 := by
  ext; simp

variable (G) in
/-- `fderivCompContinuousLinearMap` as a continuous linear map -/
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM** 是 Mathlib 中的一个定义，位
于命名空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMapCLM (g : E ->L[𝕜] F) : (F [⋀^ι]->L[𝕜] G) ->L[
𝕜] (E ->L[𝕜] F) ->L[𝕜] (E [⋀^ι]->L[𝕜] G)
参数：g : E ->L[𝕜] F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
`fderivCompContinuousLinearMap` as a continuous linear map
-/
def fderivCompContinuousLinearMapCLM (g : E →L[𝕜] F) :
    (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E →L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
  LinearMap.mkContinuous
    { toFun := (fderivCompContinuousLinearMap · g)
      map_add' f₁ f₂ := by ext; simp [Finset.sum_add_distrib]
      map_smul' c f := by ext; simp [Finset.smul_sum] }
    (Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1))
    fun f ↦ by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dg ↦ ?_
      refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
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
      rw [← Finset.card_singleton i, ← Finset.card_compl, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      gcongr with j hj
      simpa [Function.update_of_ne (by simpa using hj)] using g.le_opNorm _

@[simp]
/-
**ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM_apply** 是 Mathlib 中的
一个引理，位于命名空间 `ContinuousAlternatingMap`。
形式化陈述：fderivCompContinuousLinearMapCLM_apply (f : F [⋀^ι]->L[𝕜] G) (g : E ->L[𝕜]
 F) : fderivCompContinuousLinearMapCLM G g f = fderivCompContinuousLinearMap f g
参数：f : F [⋀^ι]->L[𝕜] G；g : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousAlternatingMap.instSMulCommClass`：∀ {M : Type u_2} {N : Type u
_4} {ι : Type u_6} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M]   [ins
t_2 : AddCommMonoid N] [inst_3 :…
-/
lemma fderivCompContinuousLinearMapCLM_apply (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    fderivCompContinuousLinearMapCLM G g f = fderivCompContinuousLinearMap f g :=
  rfl

end ContinuousAlternatingMap

end

open ContinuousAlternatingMap

namespace AlternatingMap

/-- Given a map `f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `F` to `E [⋀^ι]→L[𝕜] G`.

In order to lift, e.g., a map `f : (E [⋀^ι]→ₗ[𝕜] F) →ₗ[𝕜] E' [⋀^ι]→ₗ[𝕜] G`
to a map `(E [⋀^ι]→L[𝕜] F) →L[𝕜] E' [⋀^ι]→L[𝕜] G`,
one can apply this construction to `f.comp ContinuousAlternatingMap.toAlternatingMapLinear`
which is a linear map from `E [⋀^ι]→L[𝕜] F` to `E' [⋀^ι]→ₗ[𝕜] G`. -/
/-
**AlternatingMap.mkContinuousLinear** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：mkContinuousLinear (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real) (H : forall x
 m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : F ->L[𝕜] E [⋀^ι]->L[𝕜] G
参数：f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G；C : Real；H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ 
i, ‖m i‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `F` to `E [⋀^ι]→L[𝕜] G`.

In order to lift, e.g., a map `f : (E [⋀^ι]→ₗ[𝕜] F) →ₗ[𝕜] E' [⋀^ι]→ₗ[𝕜] G`
to a map `(E [⋀^ι]→L[𝕜] F) →L[𝕜] E' [⋀^ι]→L[𝕜] G`,
one can apply this construction to `f.comp ContinuousAlternatingMap.toAlternatin
gMapLinear`
which is a linear map from `E [⋀^ι]→L[𝕜] F` to `E' [⋀^ι]→ₗ[𝕜] G`.
-/
def mkContinuousLinear (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : F →L[𝕜] E [⋀^ι]→L[𝕜] G :=
  LinearMap.mkContinuous
    { toFun x := (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp }
    (max C 0) fun x ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact (mkContinuous_norm_le' _ _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]
/-
**AlternatingMap.mkContinuousLinear_norm_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Alter
natingMap`。
形式化陈述：mkContinuousLinear_norm_le_max (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real) (
H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ <=
 max C 0
参数：f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G；C : Real；H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ 
i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous_norm_le`：mkContinuous_norm_le (f : E ->ₛₗ[σ₁₂] F)
 {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) : ‖f.mkContinuous C h
‖ <= C
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mkContinuousLinear_norm_le_max (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _
/-
**AlternatingMap.mkContinuousLinear_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Alternati
ngMap`。
形式化陈述：mkContinuousLinear_norm_le (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) {C : Real} (hC :
 0 <= C) (H : forall x m, ‖f x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear
 f C H‖ <= C
参数：f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G；hC : 0 <= C；H : forall x m, ‖f x m‖ <= C * ‖x‖ *
 ∏ i, ‖m i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AlternatingMap.mkContinuousLinear_norm_le_max`：mkContinuousLinear_norm_l
e_max (f : F ->ₗ[𝕜] E [⋀^ι]->ₗ[𝕜] G) (C : Real) (H : forall x m, ‖f x m‖ <= C * 
‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLi…
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mkContinuousLinear_norm_le (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ C :=
  (mkContinuousLinear_norm_le_max f C H).trans_eq (max_eq_left hC)

variable {ι' : Type*} [Fintype ι']

/-- Given a map `f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `AlternatingMap`s in the type
to `ContinuousAlternatingMap`s. -/
/-
**AlternatingMap.mkContinuousAlternating** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingM
ap`。
形式化陈述：mkContinuousAlternating (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) (C : Real) 
(H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) : E [⋀^ι]->L[𝕜]
 (F [⋀^ι']->L[𝕜] G)
参数：f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)；C : Real；H : forall m₁ m₂, ‖f m₁ m₂‖ <= 
(C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `AlternatingM
ap`s in the type
to `ContinuousAlternatingMap`s.
-/
def mkContinuousAlternating (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G))
    (C : ℝ) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    E [⋀^ι]→L[𝕜] (F [⋀^ι']→L[𝕜] G) :=
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
      rw [max_mul_of_nonneg, zero_mul]
      positivity

@[simp]
/-
**AlternatingMap.mkContinuousAlternating_apply** 是 Mathlib 中的一个定理，位于命名空间 `Altern
atingMap`。
形式化陈述：mkContinuousAlternating_apply (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : 
Real} (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι ->
 E) : ⇑(mkContinuousAlternating f C H m) = f m
参数：f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)；H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i,
 ‖m₁ i‖) * ∏ i, ‖m₂ i‖；m : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem mkContinuousAlternating_apply (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι → E) :
    ⇑(mkContinuousAlternating f C H m) = f m :=
  rfl
/-
**AlternatingMap.mkContinuousAlternating_norm_le_max** 是 Mathlib 中的一个定理，位于命名空间 `
AlternatingMap`。
形式化陈述：mkContinuousAlternating_norm_le_max (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G))
 {C : Real} (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) : ‖
mkContinuousAlternating f C H‖ <= max C 0
参数：f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)；H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i,
 ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AlternatingMap.mkContinuous_norm_le`：AlternatingMap.mkContinuous_norm_le
 (f : E [⋀^ι]->ₗ[𝕜] F) {C : Real} (hC : 0 <= C) (H : forall m, ‖f m‖ <= C * ∏ i,
 ‖m i‖) : ‖f.mkContinuous…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mkContinuousAlternating_norm_le_max (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _
/-
**AlternatingMap.mkContinuousAlternating_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Alte
rnatingMap`。
形式化陈述：mkContinuousAlternating_norm_le (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C 
: Real} (hC : 0 <= C) (H : forall m₁ m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖
m₂ i‖) : ‖mkContinuousAlternating f C H‖ <= C
参数：f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)；hC : 0 <= C；H : forall m₁ m₂, ‖f m₁ m₂‖ 
<= (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AlternatingMap.mkContinuousAlternating_norm_le_max`：mkContinuousAlternat
ing_norm_le_max (f : E [⋀^ι]->ₗ[𝕜] (F [⋀^ι']->ₗ[𝕜] G)) {C : Real} (H : forall m₁
 m₂, ‖f m₁ m₂‖ <= (C * ∏ i, ‖m₁ i‖) * ∏ …
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mkContinuousAlternating_norm_le (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ C :=
  (mkContinuousAlternating_norm_le_max f H).trans_eq (max_eq_left hC)

end AlternatingMap

end Seminorm

section Norm

/-! Results that are only true if the target space is a `NormedAddCommGroup`
(and not just a `SeminormedAddCommGroup`). -/

universe u wE wF v
variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {ι : Type v}
  [Fintype ι]
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousAlternatingMap

/-- Continuous alternating maps themselves form a normed group with respect to the operator norm. -/
/-
**ContinuousAlternatingMap.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Con
tinuousAlternatingMap`。
形式化陈述：instNormedAddCommGroup : NormedAddCommGroup (E [⋀^ι]->L[𝕜] F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous alternating maps themselves form a normed group with respect to the o
perator norm.
-/
instance instNormedAddCommGroup : NormedAddCommGroup (E [⋀^ι]→L[𝕜] F) :=
  NormedAddCommGroup.ofSeparation fun _f hf ↦
    toContinuousMultilinearMap_injective <| norm_eq_zero.mp hf

variable (𝕜 F) in
/-
**ContinuousAlternatingMap.norm_ofSubsingleton_id** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAlternatingMap`。
形式化陈述：norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) : ‖ofSubsin
gleton 𝕜 F F i (.id _ _)‖ = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.norm_ofSubsingleton_id`：norm_ofSubsingleton_id 
[Subsingleton ι] [Nontrivial G] (i : ι) : ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ = 1
-/
theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖ = 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id 𝕜 F i

variable (𝕜 F) in
/-
**ContinuousAlternatingMap.nnnorm_ofSubsingleton_id** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousAlternatingMap`。
形式化陈述：nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) : ‖ofSubs
ingleton 𝕜 F F i (.id _ _)‖₊ = 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `ContinuousAlternatingMap.norm_ofSubsingleton_id`：norm_ofSubsingleton_id 
[Subsingleton ι] [Nontrivial F] (i : ι) : ‖ofSubsingleton 𝕜 F F i (.id _ _)‖ = 1
-/
theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖₊ = 1 :=
  NNReal.eq <| norm_ofSubsingleton_id ..

end ContinuousAlternatingMap

namespace AlternatingMap

/-- If an alternating map in finitely many variables on a normed space satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
/-
**AlternatingMap.bound_of_shell** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：bound_of_shell (f : F [⋀^ι]->ₗ[𝕜] E) {ε : ι -> Real} {C : Real} {c : ι -> 
𝕜} (hε : forall i, 0 < ε i) (hc : forall i, 1 < ‖c i‖) (hf : forall m : ι -> F, 
(forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f m‖ <= C * ∏ i,
 ‖m i‖) (m : ι -> F) : ‖f m‖ <= C * ∏ i, ‖m i‖
参数：f : F [⋀^ι]->ₗ[𝕜] E；hε : forall i, 0 < ε i；hc : forall i, 1 < ‖c i‖；hf : fora
ll m : ι -> F, (forall i, ε i / ‖c i‖ <= ‖m i‖) -> (forall i, ‖m i‖ < ε i) -> ‖f
 m‖ <= C * ∏ i, ‖m i‖；m : ι -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.bound_of_shell`：bound_of_shell (f : MultilinearMap 𝕜 E G)
 {ε : ι -> Real} {C : Real} {c : ι -> 𝕜} (hε : forall i, 0 < ε i) (hc : forall i
, 1 < ‖c i‖) (hf : …

--- 原说明 ---
If an alternating map in finitely many variables on a normed space satisfies the
 inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positiv
e numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `
m`.
-/
theorem bound_of_shell (f : F [⋀^ι]→ₗ[𝕜] E) {ε : ι → ℝ} {C : ℝ} {c : ι → 𝕜}
    (hε : ∀ i, 0 < ε i) (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ι → F, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → F) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell hε hc hf m

end AlternatingMap

end Norm

