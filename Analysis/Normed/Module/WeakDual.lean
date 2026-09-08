/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov, Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-\*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`StrongDual 𝕜 E` or `WeakDual 𝕜 E`, depending on whether it is viewed as equipped with its usual
operator norm topology or the weak-\* topology.

It is shown that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous, and
as a consequence the weak-\* topology is coarser than the topology obtained from the operator norm
(dual norm).

The file also equips `WeakDual 𝕜 E` with the norm bornology inherited from `StrongDual 𝕜 E`, so
that `IsBounded` refers to operator-norm boundedness. This is a pragmatic choice discussed
further in the implementation notes.

We establish the Banach-Alaoglu theorem about the compactness of closed balls in the dual of `E`
(as well as sets of somewhat more general form) with respect to the weak-\* topology.

The first main result concerns the comparison of the operator norm topology on `StrongDual 𝕜 E` and
the weak-\* topology on (its type synonym) `WeakDual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-\* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `WeakDual.isCompact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `WeakDual _ E`, if the
  nontrivially normed field `𝕜` is proper as a topological space.
* `WeakDual.isCompact_closedBall` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

## Main definitions

* `StrongDual.toWeakDual` and `WeakDual.toStrongDual`: Linear equivalences between the dual types.
* `WeakDual.instBornology`: The norm bornology on `WeakDual 𝕜 E`.
* `WeakDual.seminormFamily`: The family of seminorms `fun x f ↦ ‖f x‖` generating the weak-\*
  topology.
* `WeakDual.polar`: The polar set of `s : Set E` viewed as a subset of `WeakDual 𝕜 E`.

## Main results

### Topology comparison
* `NormedSpace.Dual.toWeakDual_continuous`: The weak-\* topology is coarser than the norm topology.

### Bornology and pointwise bounds
* `WeakDual.isBounded_iff_isVonNBounded`: Equivalence of norm and weak-\* boundedness for
  Banach spaces.

### Compactness and Banach-Alaoglu
* `WeakDual.isCompact_polar`: Polars of neighborhoods of the origin are weak-\* compact.
* `WeakDual.isCompact_closedBall`: Closed balls are weak-\* compact.
* `WeakDual.isSeqCompact_closedBall`: Sequential version for separable spaces.

## Implementation notes

* **Topology synonym:** When `M` is a vector space, the duals `StrongDual 𝕜 M` and `WeakDual 𝕜 M`
  are type synonyms with different topology instances.
* **Bornology choice:** The `Bornology` instance on `WeakDual 𝕜 E` is inherited from
  `StrongDual 𝕜 E` via `inferInstanceAs` and corresponds to the operator-norm bornology.
  While the natural bornology for a weak topology is technically the von Neumann bornology
  (pointwise boundedness), we use the norm bornology for several pragmatic reasons:
  1. **Practicality:** In the normed setting, "bounded" is almost universally synonymous with
     "norm-bounded". This allows `IsBounded` to be used directly in statements like Banach-Alaoglu.
  2. **Clarity:** It preserves a clear distinction between norm-boundedness (`IsBounded`) and
     topological weak-\* boundedness (`IsVonNBounded`).
  3. **Consistency:** By the Uniform Boundedness Principle, these notions coincide whenever
     `E` is a Banach space (`isBounded_iff_isVonNBounded`).
* **Polar sets:** The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a
  subset of the dual `StrongDual 𝕜 E`. We care about properties of these w.r.t. weak-\* topology,
  and for this purpose give the definition `WeakDual.polar 𝕜 s` for the "same" subset viewed as a
  subset of `WeakDual 𝕜 E` (a type synonym of the dual but with a different topology instance).
* **Banach-Alaoglu Proof:** The weak dual of `E` is embedded in the space of functions `E → 𝕜`
  with the topology of pointwise convergence.

## TODO
* Add that in finite dimensions, the weak-\* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-\* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `WeakDual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## References
* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/

@[expose] public section

noncomputable section

open Filter Function Bornology Metric Set Topology Filter

variable {𝕜 M E : Type*}
variable [NontriviallyNormedField 𝕜]
variable [AddCommGroup M] [TopologicalSpace M] [Module 𝕜 M]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace WeakDual

section Bornology

/-- The bornology on `WeakDual 𝕜 F` is the norm bornology inherited from `StrongDual 𝕜 F`.

Note: This is a pragmatic choice. To be precise, the bornology of a weak topology should be
the von Neumann bornology (pointwise boundedness). However, in the normed setting,
`IsBounded` is most useful when referring to the operator norm (e.g., to state
Banach-Alaoglu concisely).

Pointwise boundedness is instead captured by `Bornology.IsVonNBounded`.
For Banach spaces, these notions coincide via `isBounded_iff_isVonNBounded`.
See the module docstring for more details. -/
/-
**WeakDual.instBornology** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：instBornology : Bornology (WeakDual 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bornology on `WeakDual 𝕜 F` is the norm bornology inherited from `StrongDual
 𝕜 F`.

Note: This is a pragmatic choice. To be precise, the bornology of a weak topolog
y should be
the von Neumann bornology (pointwise boundedness). However, in the normed settin
g,
`IsBounded` is most useful when referring to the operator norm (e.g., to state
Banach-Alaoglu concisely).

Pointwise boundedness is instead captured by `Bornology.IsVonNBounded`.
For Banach spaces, these notions coincide via `isBounded_iff_isVonNBounded`.
See the module docstring for more details.
-/
instance instBornology : Bornology (WeakDual 𝕜 E) := inferInstanceAs (Bornology (StrongDual 𝕜 E))

/-- A set in `WeakDual 𝕜 E` is bounded iff its image in `StrongDual 𝕜 E` is bounded. -/
@[simp]
/-
**WeakDual.isBounded_toStrongDual_preimage_iff_isBounded** 是 Mathlib 中的一个定理，位于命名
空间 `WeakDual`。
形式化陈述：isBounded_toStrongDual_preimage_iff_isBounded {s : Set (StrongDual 𝕜 E)} :
 IsBounded (WeakDual.toStrongDual ⁻¹' s) ↔ IsBounded s
参数：StrongDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
A set in `WeakDual 𝕜 E` is bounded iff its image in `StrongDual 𝕜 E` is bounded.
-/
theorem isBounded_toStrongDual_preimage_iff_isBounded {s : Set (StrongDual 𝕜 E)} :
    IsBounded (WeakDual.toStrongDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

/-- A set in `StrongDual 𝕜 E` is bounded iff its image in `WeakDual 𝕜 E` is bounded. -/
@[simp]
/-
**WeakDual.isBounded_toWeakDual_preimage_iff_isBounded** 是 Mathlib 中的一个定理，位于命名空间
 `WeakDual`。
形式化陈述：isBounded_toWeakDual_preimage_iff_isBounded {s : Set (WeakDual 𝕜 E)} : IsB
ounded (StrongDual.toWeakDual ⁻¹' s) ↔ IsBounded s
参数：WeakDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
A set in `StrongDual 𝕜 E` is bounded iff its image in `WeakDual 𝕜 E` is bounded.
-/
theorem isBounded_toWeakDual_preimage_iff_isBounded {s : Set (WeakDual 𝕜 E)} :
    IsBounded (StrongDual.toWeakDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

end Bornology

end WeakDual

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-\* topology on duals of normed spaces.
We prove in particular that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous,
i.e., that the weak-\* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

namespace NormedSpace

namespace Dual

@[fun_prop]
/-
**NormedSpace.Dual.toWeakDual_continuous** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace.
Dual`。
形式化陈述：toWeakDual_continuous : Continuous fun x' : StrongDual 𝕜 E => StrongDual.t
oWeakDual x'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakBilin.continuous_of_continuous_eval`：continuous_of_continuous_eval [
TopologicalSpace α] {g : α -> WeakBilin B} (h : forall y, Continuous fun a => B 
(g a) y) : Continuous g
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
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
theorem toWeakDual_continuous : Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x' :=
  WeakBilin.continuous_of_continuous_eval _ fun z => (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous

/-- For a normed space `E`, according to `toWeakDual_continuous` the "identity mapping"
`StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
/-
**NormedSpace.Dual.continuousLinearMapToWeakDual** 是 Mathlib 中的一个定义，位于命名空间 `Norm
edSpace.Dual`。
形式化陈述：continuousLinearMapToWeakDual : StrongDual 𝕜 E ->L[𝕜] WeakDual 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a normed space `E`, according to `toWeakDual_continuous` the "identity mappi
ng"
`StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous. This definition implements it as 
a continuous linear
map.
-/
def continuousLinearMapToWeakDual : StrongDual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { StrongDual.toWeakDual with }

set_option backward.isDefEq.respectTransparency false in
/-- The weak-star topology is coarser than the dual-norm topology. -/
/-
**NormedSpace.Dual.dual_norm_topology_le_weak_dual_topology** 是 Mathlib 中的一个定理，位
于命名空间 `NormedSpace.Dual`。
形式化陈述：dual_norm_topology_le_weak_dual_topology : (UniformSpace.toTopologicalSpac
e : TopologicalSpace (StrongDual 𝕜 E)) <= (instTopologicalSpaceWeakDual .. : Top
ologicalSpace (WeakDual 𝕜 E))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `induced_id`：induced_id [t : TopologicalSpace α] : t.induced id = t
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用定理 `NormedSpace.Dual.toWeakDual_continuous`：toWeakDual_continuous : Continuo
us fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x'

--- 原说明 ---
The weak-star topology is coarser than the dual-norm topology.
-/
theorem dual_norm_topology_le_weak_dual_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (StrongDual 𝕜 E)) ≤
      (instTopologicalSpaceWeakDual .. : TopologicalSpace (WeakDual 𝕜 E)) := by
  convert! (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

/-!
### Bornology and pointwise bounds

This section relates the inherited norm bornology (`IsBounded`) to the intrinsic
von Neumann bornology of the weak-\* topology (`IsVonNBounded`).

The following results justify using the norm bornology as the default instance: by the
Uniform Boundedness Principle, it coincides with the von Neumann bornology whenever
$E$ is a Banach space.
-/

variable (𝕜 E) in
/-- The family of seminorms on `WeakDual 𝕜 E` given by `fun x f ↦ ‖f x‖`, indexed by `E`.
This is the seminorm family associated to the weak-\* topology via `topDualPairing`. -/
/-
**WeakDual.seminormFamily** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：seminormFamily : SeminormFamily 𝕜 (WeakDual 𝕜 E) E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms on `WeakDual 𝕜 E` given by `fun x f ↦ ‖f x‖`, indexed by
 `E`.
This is the seminorm family associated to the weak-\* topology via `topDualPairi
ng`.
-/
def seminormFamily : SeminormFamily 𝕜 (WeakDual 𝕜 E) E := (topDualPairing 𝕜 E).toSeminormFamily

@[simp]
/-
**WeakDual.seminormFamily_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：seminormFamily_apply (x : E) (f : WeakDual 𝕜 E) : seminormFamily 𝕜 E x f =
 ‖f x‖
参数：x : E；f : WeakDual 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma seminormFamily_apply (x : E) (f : WeakDual 𝕜 E) : seminormFamily 𝕜 E x f = ‖f x‖ := rfl

variable (𝕜 E) in
/-
**WeakDual.withSeminorms** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：withSeminorms : WithSeminorms (seminormFamily 𝕜 E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.weakBilin_withSeminorms`：LinearMap.weakBilin_withSeminorms (B 
: E ->ₗ[𝕜] F ->ₗ[𝕜] 𝕜) : WithSeminorms (LinearMap.toSeminormFamily B : F -> Semi
norm 𝕜 (WeakBilin B))
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
-/
lemma withSeminorms : WithSeminorms (seminormFamily 𝕜 E) :=
  (topDualPairing 𝕜 E).weakBilin_withSeminorms

/-- By the Uniform Boundedness Principle, norm-boundedness (the default bornology)
and pointwise-boundedness (`IsVonNBounded`) coincide on the weak dual of a Banach space. -/
/-
**WeakDual.isBounded_iff_isVonNBounded** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isBounded_iff_isVonNBounded [CompleteSpace E] {s : Set (WeakDual 𝕜 E)} : I
sBounded s ↔ Bornology.IsVonNBounded 𝕜 s
参数：WeakDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Bornology.IsVonNBounded.of_topologicalSpace_le`：∀ {𝕜 : Type u_1} {E : Ty
pe u_3} [inst : SeminormedRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mod
ule 𝕜 E]   {t t' : TopologicalSpace …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `NormedSpace.Dual.dual_norm_topology_le_weak_dual_topology`：dual_norm_top
ology_le_weak_dual_topology : (UniformSpace.toTopologicalSpace : TopologicalSpac
e (StrongDual 𝕜 E)) <= (instTopologicalSpaceWea…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithSeminorms.isVonNBounded_iff_seminorm_bounded`：WithSeminorms.isVonNBo
unded_iff_seminorm_bounded {s : Set E} (hp : WithSeminorms p) : IsVonNBounded 𝕜 
s ↔ forall i : ι, exists r > 0, forall…
· 使用引理 `WeakDual.withSeminorms`：withSeminorms : WithSeminorms (seminormFamily 𝕜 
E)
· 使用定理 `banach_steinhaus`：banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι 
-> E ->SL[σ₁₂] F} (h : forall x, exists C, forall i, ‖g i x‖ <= C) : exists C', 
forall…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WeakDual.isBounded_toWeakDual_preimage_iff_isBounded`：isBounded_toWeakDu
al_preimage_iff_isBounded {s : Set (WeakDual 𝕜 E)} : IsBounded (StrongDual.toWea
kDual ⁻¹' s) ↔ IsBounded s
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C

--- 原说明 ---
By the Uniform Boundedness Principle, norm-boundedness (the default bornology)
and pointwise-boundedness (`IsVonNBounded`) coincide on the weak dual of a Banac
h space.
-/
theorem isBounded_iff_isVonNBounded [CompleteSpace E] {s : Set (WeakDual 𝕜 E)} :
    IsBounded s ↔ Bornology.IsVonNBounded 𝕜 s := by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff 𝕜).mpr h).of_topologicalSpace_le
      Dual.dual_norm_topology_le_weak_dual_topology
  · intro h_vN
    have h_ptwise := (withSeminorms 𝕜 E).isVonNBounded_iff_seminorm_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i : s ↦ WeakDual.toStrongDual i.val) fun x ↦
      let ⟨M, _, hM⟩ := h_ptwise x
      ⟨M, fun i ↦ le_of_lt (hM i.val i.property)⟩
    rw [← isBounded_toWeakDual_preimage_iff_isBounded, isBounded_iff_forall_norm_le]
    exact ⟨C, fun f hf ↦ hC ⟨StrongDual.toWeakDual f, hf⟩⟩

/-!
### Compactness of bounded closed sets

While the coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets.
-/

/-- The coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` sends bounded closed sets to closed sets. -/
/-
**WeakDual.isClosed_image_coe_of_bounded_of_closed** 是 Mathlib 中的一个定理，位于命名空间 `We
akDual`。
形式化陈述：isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)} (hb : IsB
ounded s) (hc : IsClosed s) : IsClosed (((↑) : WeakDual 𝕜 E -> E -> 𝕜) '' s)
参数：WeakDual 𝕜 E；hb : IsBounded s；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed`：isClos
ed_image_coe_of_bounded_of_weak_closed {s : Set (E' ->SL[σ₁₂] F)} (hb : IsBounde
d s) (hc : forall f : E' ->SL[σ₁₂] F, (⇑f : E' -> F) i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_induced_iff'`：isClosed_induced_iff' {f : α -> β} {s : Set α} : 
IsClosed[t.induced f] s ↔ forall a, f a in closure (f '' s) -> a in s

--- 原说明 ---
The coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` sends bounded closed sets to closed se
ts.
-/
theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

/-- Bounded closed sets in `WeakDual 𝕜 E` are compact when `𝕜` is a proper space. -/
/-
**WeakDual.isCompact_of_bounded_of_closed** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)} (h
b : IsBounded s) (hc : IsClosed s) : IsCompact s
参数：WeakDual 𝕜 E；hb : IsBounded s；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsEmbedding.isCompact_iff`：Topology.IsEmbedding.isCompact_iff {
f : X -> Y} (hf : IsEmbedding f) : IsCompact s ↔ IsCompact (f '' s)
· 使用定理 `Function.Injective.isEmbedding_induced`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbeddin
g f
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image`：isCo
mpact_image_coe_of_bounded_of_closed_image [ProperSpace F] {s : Set (E' ->SL[σ₁₂
] F)} (hb : IsBounded s) (hc : IsClosed (((↑) : (E' ->SL…
· 使用定理 `WeakDual.isClosed_image_coe_of_bounded_of_closed`：isClosed_image_coe_of_
bounded_of_closed {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) 
: IsClosed (((↑) : WeakDual 𝕜 E -> E -…

--- 原说明 ---
Bounded closed sets in `WeakDual 𝕜 E` are compact when `𝕜` is a proper space.
-/
theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) : IsCompact s :=
  DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr <|
    ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb <|
      isClosed_image_coe_of_bounded_of_closed hb hc

/-!
### Closed balls
-/

/-- Closed balls in `StrongDual 𝕜 E` pull back to closed sets in `WeakDual 𝕜 E`. -/
/-
**WeakDual.isClosed_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isClosed_closedBall (x' : StrongDual 𝕜 E) (r : Real) : IsClosed (toStrongD
ual ⁻¹' closedBall x' r)
参数：x' : StrongDual 𝕜 E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `isClosed_induced_iff'`：isClosed_induced_iff' {f : α -> β} {s : Set α} : 
IsClosed[t.induced f] s ↔ forall a, f a in closure (f '' s) -> a in s
· 使用定理 `ContinuousLinearMap.is_weak_closed_closedBall`：is_weak_closed_closedBall
 (f₀ : E' ->SL[σ₁₂] F) (r : Real) ⦃f : E' ->SL[σ₁₂] F⦄ (hf : ⇑f in closure (((↑)
 : (E' ->SL[σ₁₂] F) -> E' -> F) '' …

--- 原说明 ---
Closed balls in `StrongDual 𝕜 E` pull back to closed sets in `WeakDual 𝕜 E`.
-/
theorem isClosed_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsClosed (toStrongDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

/-- Closed balls are bounded in the weak dual. -/
/-
**WeakDual.isBounded_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isBounded_closedBall (x' : StrongDual 𝕜 E) (r : Real) : IsBounded (toStron
gDual ⁻¹' closedBall x' r)
参数：x' : StrongDual 𝕜 E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakDual.isBounded_toStrongDual_preimage_iff_isBounded`：isBounded_toStro
ngDual_preimage_iff_isBounded {s : Set (StrongDual 𝕜 E)} : IsBounded (WeakDual.t
oStrongDual ⁻¹' s) ↔ IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)

--- 原说明 ---
Closed balls are bounded in the weak dual.
-/
theorem isBounded_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsBounded (toStrongDual ⁻¹' closedBall x' r) :=
  isBounded_toStrongDual_preimage_iff_isBounded.mpr Metric.isBounded_closedBall

/-- The weak-\* closure of a norm-bounded set is norm-bounded, because norm-closed balls
are weak-\* closed. -/
/-
**WeakDual.isBounded_closure** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isBounded_closure {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) : IsBounded 
(closure s)
参数：WeakDual 𝕜 E；hb : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff_subset_closedBall`：isBounded_iff_subset_closedBall 
(c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakDual.isBounded_closedBall`：isBounded_closedBall (x' : StrongDual 𝕜 E
) (r : Real) : IsBounded (toStrongDual ⁻¹' closedBall x' r)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `WeakDual.isClosed_closedBall`：isClosed_closedBall (x' : StrongDual 𝕜 E) 
(r : Real) : IsClosed (toStrongDual ⁻¹' closedBall x' r)

--- 原说明 ---
The weak-\* closure of a norm-bounded set is norm-bounded, because norm-closed b
alls
are weak-\* closed.
-/
theorem isBounded_closure {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) :
    IsBounded (closure s) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : StrongDual 𝕜 E)).mp hb
  exact (isBounded_closedBall 0 R).subset
    (closure_minimal (fun y hy ↦ hR (a := toStrongDual y) hy) (isClosed_closedBall 0 R))

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
/-
**WeakDual.isCompact_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isCompact_closedBall [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : Real) : Is
Compact (toStrongDual ⁻¹' closedBall x' r)
参数：x' : StrongDual 𝕜 E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.isCompact_of_bounded_of_closed`：isCompact_of_bounded_of_closed 
[ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) : 
IsCompact s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakDual.isBounded_closedBall`：isBounded_closedBall (x' : StrongDual 𝕜 E
) (r : Real) : IsBounded (toStrongDual ⁻¹' closedBall x' r)
· 使用定理 `WeakDual.isClosed_closedBall`：isClosed_closedBall (x' : StrongDual 𝕜 E) 
(r : Real) : IsClosed (toStrongDual ⁻¹' closedBall x' r)

--- 原说明 ---
The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` a
re compact in
the weak-star topology.
-/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact (toStrongDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed (isBounded_closedBall x' r) (isClosed_closedBall x' r)

/-!
### Polar sets in the weak dual space
-/

section PolarSets

variable (𝕜)

/-- The polar set `polar 𝕜 s` of `s : Set E` seen as a subset of the dual of `E` with the
weak-star topology is `WeakDual.polar 𝕜 s`. -/
/-
**WeakDual.polar** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：polar (s : Set M) : Set (WeakDual 𝕜 M)
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar set `polar 𝕜 s` of `s : Set E` seen as a subset of the dual of `E` wit
h the
weak-star topology is `WeakDual.polar 𝕜 s`.
-/
def polar (s : Set M) : Set (WeakDual 𝕜 M) := toStrongDual ⁻¹' (StrongDual.polar 𝕜) s
/-
**WeakDual.polar_def** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：polar_def (s : Set M) : polar 𝕜 s = { f : WeakDual 𝕜 M | forall x in s, ‖f
 x‖ <= 1 }
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem polar_def (s : Set M) : polar 𝕜 s = { f : WeakDual 𝕜 M | ∀ x ∈ s, ‖f x‖ ≤ 1 } := rfl

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
/-
**WeakDual.isClosed_polar** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isClosed_polar (s : Set M) : IsClosed (polar 𝕜 s)
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star top
ology
is used.
-/
theorem isClosed_polar (s : Set M) : IsClosed (polar 𝕜 s) := by
  simp only [polar_def, ofPred_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

/-- Polar sets of neighborhoods of the origin are bounded in the weak dual. -/
/-
**WeakDual.isBounded_polar** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isBounded_polar {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : IsBounded (polar 𝕜
 s)
参数：s_nhds : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakDual.isBounded_toStrongDual_preimage_iff_isBounded`：isBounded_toStro
ngDual_preimage_iff_isBounded {s : Set (StrongDual 𝕜 E)} : IsBounded (WeakDual.t
oStrongDual ⁻¹' s) ↔ IsBounded s
· 使用定理 `NormedSpace.isBounded_polar_of_mem_nhds_zero`：isBounded_polar_of_mem_nhd
s_zero {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : IsBounded (StrongDual.polar 𝕜 s)

--- 原说明 ---
Polar sets of neighborhoods of the origin are bounded in the weak dual.
-/
theorem isBounded_polar {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) : IsBounded (polar 𝕜 s) :=
  isBounded_toStrongDual_preimage_iff_isBounded.mpr
  (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of a polar `WeakDual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
/-
**WeakDual.isClosed_image_polar_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`
。
形式化陈述：isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : I
sClosed (((↑) : WeakDual 𝕜 E -> E -> 𝕜) '' polar 𝕜 s)
参数：s_nhds : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.isClosed_image_coe_of_bounded_of_closed`：isClosed_image_coe_of_
bounded_of_closed {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) 
: IsClosed (((↑) : WeakDual 𝕜 E -> E -…
· 使用定理 `WeakDual.isBounded_polar`：isBounded_polar {s : Set E} (s_nhds : s in 𝓝 (
0 : E)) : IsBounded (polar 𝕜 s)
· 使用定理 `WeakDual.isClosed_polar`：isClosed_polar (s : Set M) : IsClosed (polar 𝕜 
s)

--- 原说明 ---
The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of a polar `WeakDual.polar 𝕜 s` of 
a
neighborhood `s` of the origin is a closed set.
-/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

/-- The image under `↑ : StrongDual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
/-
**WeakDual._root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds** 是 Mathlib 
中的一个定理，位于命名空间 `WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image under `↑ : StrongDual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set.
-/
theorem _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds {s : Set E}
    (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : StrongDual 𝕜 E → E → 𝕜) '' StrongDual.polar 𝕜 s) :=
  WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `WeakDual 𝕜 E`. -/
/-
**WeakDual.isCompact_polar** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : Is
Compact (polar 𝕜 s)
参数：s_nhds : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.isCompact_of_bounded_of_closed`：isCompact_of_bounded_of_closed 
[ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) : 
IsCompact s
· 使用定理 `WeakDual.isBounded_polar`：isBounded_polar {s : Set E} (s_nhds : s in 𝓝 (
0 : E)) : IsBounded (polar 𝕜 s)
· 使用定理 `WeakDual.isClosed_polar`：isClosed_polar (s : Set M) : IsClosed (polar 𝕜 
s)

--- 原说明 ---
The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origi
n in a
normed space `E` is a compact subset of `WeakDual 𝕜 E`.
-/
theorem isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) :=
  isCompact_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

end PolarSets

/-!
### Sequential compactness
-/

open TopologicalSpace

variable (𝕜 E) [TopologicalSpace.SeparableSpace E] (K : Set (WeakDual 𝕜 E))

/-- In a separable normed space, there exists a sequence of continuous functions that
separates points of the weak dual. -/
/-
**WeakDual.exists_countable_separating** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：exists_countable_separating : exists (gs : Nat -> (WeakDual 𝕜 E) -> 𝕜), (f
orall n, Continuous (gs n)) ∧ (forall ⦃x y⦄, x != y -> exists n, gs n x != gs n 
y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `WeakDual.eval_continuous`：eval_continuous (y : E) : Continuous fun x : W
eakDual 𝕜 E => x y
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `TopologicalSpace.denseRange_denseSeq`：denseRange_denseSeq [SeparableSpac
e α] [Nonempty α] : DenseRange (denseSeq α)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `instContinuousLinearMapClassWeakDual`：∀ (𝕜 : Type u_1) (E : Type u_2) [i
nst : CommSemiring 𝕜] [inst_1 : TopologicalSpace 𝕜] [inst_2 : ContinuousAdd 𝕜]  
 [inst_3 : ContinuousConst…
· 使用定理 `Set.eqOn_range`：eqOn_range {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β} : E
qOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
In a separable normed space, there exists a sequence of continuous functions tha
t
separates points of the weak dual.
-/
lemma exists_countable_separating : ∃ (gs : ℕ → (WeakDual 𝕜 E) → 𝕜),
    (∀ n, Continuous (gs n)) ∧ (∀ ⦃x y⦄, x ≠ y → ∃ n, gs n x ≠ gs n y) := by
  use (fun n φ ↦ φ (denseSeq E n))
  constructor
  · exact fun _ ↦ eval_continuous _
  · intro w y w_ne_y
    contrapose! w_ne_y
    exact DFunLike.ext'_iff.mpr <| (map_continuous w).ext_on
      (denseRange_denseSeq E) (map_continuous y) (Set.eqOn_range.mpr (funext w_ne_y))

/-- A compact subset of the weak dual of a separable normed space is metrizable. -/
/-
**WeakDual.metrizable_of_isCompact** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：metrizable_of_isCompact (K_cpt : IsCompact K) : TopologicalSpace.Metrizabl
eSpace K
参数：K_cpt : IsCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用引理 `WeakDual.exists_countable_separating`：exists_countable_separating : exis
ts (gs : Nat -> (WeakDual 𝕜 E) -> 𝕜), (forall n, Continuous (gs n)) ∧ (forall ⦃x
 y⦄, x != y -> exists n, g…
· 使用定理 `Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separati
ng`：∀ {ι : Type u_2} {X : Type u_3} {Y : ι → Type u_4} [Encodable ι] [inst : (i 
: ι) → MetricSpace (Y i)]   [inst_1 : TopologicalSpace X] [Compa…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
A compact subset of the weak dual of a separable normed space is metrizable.
-/
lemma metrizable_of_isCompact (K_cpt : IsCompact K) : TopologicalSpace.MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_countable_separating 𝕜 E
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n k ↦ gs n k) (fun n ↦ (gs_cont n).comp continuous_subtype_val)
    fun x y hxy ↦ gs_sep <| Subtype.val_injective.ne hxy

variable [ProperSpace 𝕜] (K_cpt : IsCompact K)

/-- Bounded closed sets in the weak dual of a separable normed space are sequentially compact. -/
/-
**WeakDual.isSeqCompact_of_isBounded_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Weak
Dual`。
形式化陈述：isSeqCompact_of_isBounded_of_isClosed {s : Set (WeakDual 𝕜 E)} (hb : IsBou
nded s) (hc : IsClosed s) : IsSeqCompact s
参数：WeakDual 𝕜 E；hb : IsBounded s；hc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `WeakDual.isCompact_of_bounded_of_closed`：isCompact_of_bounded_of_closed 
[ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) : 
IsCompact s
· 使用引理 `WeakDual.metrizable_of_isCompact`：metrizable_of_isCompact (K_cpt : IsCom
pact K) : TopologicalSpace.MetrizableSpace K
· 使用定理 `continuous_iff_seqContinuous`：continuous_iff_seqContinuous [SequentialSp
ace X] {f : X -> Y} : Continuous f ↔ SeqContinuous f
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `IsSeqCompact.range`：IsSeqCompact.range [SeqCompactSpace X] (f_cont : Seq
Continuous f) : IsSeqCompact (Set.range f)
· 使用定理 `FirstCountableTopology.seq_compact_of_compact`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X], SeqCompactSpace
 X

--- 原说明 ---
Bounded closed sets in the weak dual of a separable normed space are sequentiall
y compact.
-/
theorem isSeqCompact_of_isBounded_of_isClosed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsSeqCompact s := by
  have b_isCompact' : CompactSpace s :=
    isCompact_iff_compactSpace.mp <| isCompact_of_bounded_of_closed hb hc
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
    metrizable_of_isCompact 𝕜 E s <| isCompact_of_bounded_of_closed hb hc
  have seq_cont_phi : SeqContinuous (fun φ : s ↦ (φ : WeakDual 𝕜 E)) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  simpa using IsSeqCompact.range seq_cont_phi

/-- The **Sequential Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in
a separable normed space `V` is a sequentially compact subset of `WeakDual 𝕜 V`. -/
/-
**WeakDual.isSeqCompact_polar** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isSeqCompact_polar {s : Set E} (s_nhd : s in 𝓝 (0 : E)) : IsSeqCompact (po
lar 𝕜 s)
参数：s_nhd : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.isSeqCompact_of_isBounded_of_isClosed`：isSeqCompact_of_isBounde
d_of_isClosed {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) : Is
SeqCompact s
· 使用定理 `WeakDual.isBounded_polar`：isBounded_polar {s : Set E} (s_nhds : s in 𝓝 (
0 : E)) : IsBounded (polar 𝕜 s)
· 使用定理 `WeakDual.isClosed_polar`：isClosed_polar (s : Set M) : IsClosed (polar 𝕜 
s)

--- 原说明 ---
The **Sequential Banach-Alaoglu theorem**: the polar set of a neighborhood `s` o
f the origin in
a separable normed space `V` is a sequentially compact subset of `WeakDual 𝕜 V`.
-/
theorem isSeqCompact_polar {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsSeqCompact (polar 𝕜 s) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_polar 𝕜 s_nhd) (isClosed_polar _ _)

/-- The **Sequential Banach-Alaoglu theorem**: closed balls of the dual of a separable
normed space `V` are sequentially compact in the weak-\* topology. -/
/-
**WeakDual.isSeqCompact_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`。
形式化陈述：isSeqCompact_closedBall (x' : StrongDual 𝕜 E) (r : Real) : IsSeqCompact (t
oStrongDual ⁻¹' Metric.closedBall x' r)
参数：x' : StrongDual 𝕜 E；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeakDual.isSeqCompact_of_isBounded_of_isClosed`：isSeqCompact_of_isBounde
d_of_isClosed {s : Set (WeakDual 𝕜 E)} (hb : IsBounded s) (hc : IsClosed s) : Is
SeqCompact s
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `WeakDual.isBounded_closedBall`：isBounded_closedBall (x' : StrongDual 𝕜 E
) (r : Real) : IsBounded (toStrongDual ⁻¹' closedBall x' r)
· 使用定理 `WeakDual.isClosed_closedBall`：isClosed_closedBall (x' : StrongDual 𝕜 E) 
(r : Real) : IsClosed (toStrongDual ⁻¹' closedBall x' r)

--- 原说明 ---
The **Sequential Banach-Alaoglu theorem**: closed balls of the dual of a separab
le
normed space `V` are sequentially compact in the weak-\* topology.
-/
theorem isSeqCompact_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsSeqCompact (toStrongDual ⁻¹' Metric.closedBall x' r) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 _ (isBounded_closedBall x' r) (isClosed_closedBall x' r)

end WeakDual

section RCLike

open RCLike
open scoped NNReal Topology

namespace WeakDual

-- we shadow the variables for this section because they don't fit with the rest of the file.
variable {α 𝕜 E F : Type*} [TopologicalSpace α] [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- A map into `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` over `𝕜` (with `RCLike 𝕜`) is
continuous if the real parts of all the evaluation maps `a ↦ B (g a) y` are
continuous for each `y : F`. -/
/-
**WeakDual._root_.WeakBilin.continuous_of_continuous_eval_re** 是 Mathlib 中的一个定理，
位于命名空间 `WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map into `WeakBilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)` over `𝕜` (with `RCLike 𝕜`) is
continuous if the real parts of all the evaluation maps `a ↦ B (g a) y` are
continuous for each `y : F`.
-/
theorem _root_.WeakBilin.continuous_of_continuous_eval_re (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)
    {g : α → WeakBilin B} (h : ∀ y, Continuous fun a ↦ re (B (g a) y)) :
    Continuous g := by
  refine WeakBilin.continuous_of_continuous_eval _ fun x ↦ ?_
  suffices Continuous fun a ↦ (re (B (g a) x) : 𝕜) - re (B (g a) ((I : 𝕜) • x)) * I by simpa
  fun_prop

variable [TopologicalSpace F]

/-- A map into `WeakDual 𝕜 F` over `𝕜` (with `RCLike 𝕜`) is continuous if the real parts of all
the evaluation maps `a ↦ g a y` are continuous for each `y : F`. -/
/-
**WeakDual.continuous_of_continuous_eval_re** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual`
。
形式化陈述：continuous_of_continuous_eval_re {g : α -> WeakDual 𝕜 F} (h : forall x, Co
ntinuous fun a => re (g a x)) : Continuous g
参数：h : forall x, Continuous fun a => re (g a x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `WeakBilin.continuous_of_continuous_eval_re`：∀ {α : Type u_4} {𝕜 : Type u
_5} {E : Type u_6} {F : Type u_7} [inst : TopologicalSpace α] [inst_1 : RCLike 𝕜
]   [inst_2 : AddCommGroup E] [i…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
A map into `WeakDual 𝕜 F` over `𝕜` (with `RCLike 𝕜`) is continuous if the real p
arts of all
the evaluation maps `a ↦ g a y` are continuous for each `y : F`.
-/
theorem continuous_of_continuous_eval_re {g : α → WeakDual 𝕜 F}
    (h : ∀ x, Continuous fun a ↦ re (g a x)) :
    Continuous g :=
  WeakBilin.continuous_of_continuous_eval_re _ h

variable [ContinuousConstSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F]

open StrongDual

/-- The extension `StrongDual.extendRCLike` as a continuous linear equivalence between
the weak duals. -/
@[simps! -isSimp apply symm_apply]
/-
**WeakDual.extendRCLikeL** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：extendRCLikeL : WeakDual Real F ≃L[Real] WeakDual 𝕜 F where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension `StrongDual.extendRCLike` as a continuous linear equivalence betwe
en
the weak duals.
-/
noncomputable def extendRCLikeL : WeakDual ℝ F ≃L[ℝ] WeakDual 𝕜 F where
  toLinearEquiv := toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars ℝ
  continuous_toFun := continuous_of_continuous_eval_re fun x ↦ by
    simpa [extendRCLikeₗ_apply] using eval_continuous x
  continuous_invFun :=
    continuous_of_continuous_eval fun x ↦ RCLike.continuous_re.comp (eval_continuous x)

@[simp]
/-
**WeakDual.toLinearEquiv_extendRCLikeL** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：toLinearEquiv_extendRCLikeL : (extendRCLikeL (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toLinearEquiv_extendRCLikeL :
    (extendRCLikeL (𝕜 := 𝕜) (F := F)).toLinearEquiv =
      toStrongDual ≪≫ₗ extendRCLikeₗ ≪≫ₗ toWeakDual.restrictScalars ℝ := by
  rfl
/-
**WeakDual.extendRCLikeL_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) : extendRCLikeL (𝕜
参数：f : WeakDual Real F；x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma extendRCLikeL_apply_apply (f : WeakDual ℝ F) (x : F) :
    extendRCLikeL (𝕜 := 𝕜) f x = f x - (I : 𝕜) • f ((I : 𝕜) • x) := by
  rfl
/-
**WeakDual.extendRCLikeL_symm_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：extendRCLikeL_symm_apply_apply (f : WeakDual 𝕜 F) (x : F) : extendRCLikeL.
symm f x = re (f x)
参数：f : WeakDual 𝕜 F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma extendRCLikeL_symm_apply_apply (f : WeakDual 𝕜 F) (x : F) :
    extendRCLikeL.symm f x = re (f x) :=
  rfl

@[simp]
/-
**WeakDual.re_extendRCLikeL_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：re_extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) : re (extendRCL
ikeL (𝕜
参数：f : WeakDual Real F；x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用引理 `WeakDual.extendRCLikeL_apply_apply`：extendRCLikeL_apply_apply (f : WeakD
ual Real F) (x : F) : extendRCLikeL (𝕜
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma re_extendRCLikeL_apply_apply (f : WeakDual ℝ F) (x : F) :
    re (extendRCLikeL (𝕜 := 𝕜) f x) = f x := by
  simp [extendRCLikeL_apply_apply]

@[simp]
/-
**WeakDual.im_extendRCLikeL_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`。
形式化陈述：im_extendRCLikeL_apply_apply (f : WeakDual Real F) (x : F) : im (extendRCL
ikeL (𝕜
参数：f : WeakDual Real F；x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `WeakDual.extendRCLikeL_apply`：∀ {𝕜 : Type u_5} {F : Type u_7} [inst : RC
Like 𝕜] [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topol
ogicalSpace F] [in…
· 使用定理 `StrongDual.extendRCLikeₗ_apply`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {F : 
Type u_2} [inst_1 : TopologicalSpace F] [inst_2 : AddCommGroup F]   [inst_3 : _r
oot_.Module 𝕜 F] [in…
· 使用引理 `StrongDual.im_extendRCLike_apply`：im_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : im ((extendRCLike g) x : 𝕜) = - g ((I : 𝕜) • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma im_extendRCLikeL_apply_apply (f : WeakDual ℝ F) (x : F) :
    im (extendRCLikeL (𝕜 := 𝕜) f x) = - f ((I : 𝕜) • x) := by
  simp [extendRCLikeL_apply, extendRCLikeₗ_apply]

@[simp high]
/-
**WeakDual.toStrongDual_extendRCLikeL_apply** 是 Mathlib 中的一个引理，位于命名空间 `WeakDual`
。
形式化陈述：toStrongDual_extendRCLikeL_apply (f : WeakDual Real F) : (extendRCLikeL (𝕜
参数：f : WeakDual Real F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma toStrongDual_extendRCLikeL_apply (f : WeakDual ℝ F) :
    (extendRCLikeL (𝕜 := 𝕜) f).toStrongDual = extendRCLikeₗ f :=
  rfl

@[simp high]
/-
**WeakDual._root_.StrongDual.toWeakDual_extendRCLike** 是 Mathlib 中的一个引理，位于命名空间 `
WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.StrongDual.toWeakDual_extendRCLikeₗ_apply (f : StrongDual ℝ F) :
    (extendRCLikeₗ f).toWeakDual = extendRCLikeL (𝕜 := 𝕜) f.toWeakDual :=
  rfl

end WeakDual

end RCLike

