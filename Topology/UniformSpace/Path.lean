/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Path
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.ContinuousMap.Interval

/-!
# Paths in uniform spaces

In this file we define a `UniformSpace` structure on `Path`s
between two points in a uniform space
and prove that various functions associated with `Path`s are uniformly continuous.

The uniform space structure is induced from the space of continuous maps `C(I, X)`,
and corresponds to uniform convergence of paths on `I`, see `Path.hasBasis_uniformity`.
-/

public section

open scoped unitInterval Topology Uniformity

variable {X : Type*} [UniformSpace X] {x y z : X}

namespace Path

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (Path x y)
  body: .comap ((↑) : _ -> C(I, X)) ContinuousMap.compactConvergenceUniformSpace

中文:
实例 instUniformSpace
  签名: : UniformSpace (Path x y)
  定义体: .comap ((↑) : _ -> C(I, X)) ContinuousMap.compactConvergenceUniformSpace

Depends on / 依赖: ContinuousMap, ContinuousMap.compactConvergenceUniformSpace, compactConvergenceUniformSpace
-/
instance instUniformSpace : UniformSpace (Path x y) :=
  .comap ((↑) : _ -> C(I, X)) ContinuousMap.compactConvergenceUniformSpace

/--
theorem `isUniformEmbedding_coe` / 定理 `isUniformEmbedding_coe`

English:
theorem isUniformEmbedding_coe
  statement: IsUniformEmbedding ((↑) : Path x y -> C(I, X)) where
  proof: rfl
  injective := ContinuousMap.coe_injective'

中文:
定理 isUniformEmbedding_coe
  结论: IsUniformEmbedding ((↑) : Path x y -> C(I, X)) where
  证明: rfl
  injective := ContinuousMap.coe_injective'
-/
theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Path x y -> C(I, X)) where
  comap_uniformity := rfl
  injective := ContinuousMap.coe_injective'

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (γ : Path x y)
  statement: UniformContinuous γ
  proof: CompactSpace.uniformContinuous_of_continuous map_continuous _

中文:
定理 uniformContinuous
  条件: (γ : Path x y)
  结论: UniformContinuous γ
  证明: CompactSpace.uniformContinuous_of_continuous map_continuous _

Depends on / 依赖: CompactSpace, CompactSpace.uniformContinuous_of_continuous, map_continuous, uniformContinuous_of_continuous
-/
theorem uniformContinuous (γ : Path x y) : UniformContinuous γ :=
CompactSpace.uniformContinuous_of_continuous map_continuous _

/--
theorem `uniformContinuous_extend` / 定理 `uniformContinuous_extend`

English:
theorem uniformContinuous_extend
  given: (γ : Path x y)
  statement: UniformContinuous γ.extend
  proof: γ.uniformContinuous.comp .uniformContinuous LipschitzWith.projIcc _

中文:
定理 uniformContinuous_extend
  条件: (γ : Path x y)
  结论: UniformContinuous γ.extend
  证明: γ.uniformContinuous.comp .uniformContinuous LipschitzWith.projIcc _

Depends on / 依赖: LipschitzWith, LipschitzWith.projIcc, projIcc, uniformContinuous, uniformContinuous.comp
-/
theorem uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend :=
γ.uniformContinuous.comp .uniformContinuous LipschitzWith.projIcc _

/--
theorem `uniformContinuous_extend_left` / 定理 `uniformContinuous_extend_left`

English:
theorem uniformContinuous_extend_left
  statement: UniformContinuous (Path.extend : Path x y -> C(Real, X))
  proof: ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

中文:
定理 uniformContinuous_extend_left
  结论: UniformContinuous (Path.extend : Path x y -> C(实数, X))
  证明: ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

Depends on / 依赖: ContinuousMap, ContinuousMap.projIccCM.uniformContinuous_comp_left.comp, isUniformEmbedding_coe, isUniformEmbedding_coe.uniformContinuous, projIccCM, uniformContinuous, uniformContinuous_comp_left
-/
theorem uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y -> C(Real, X)) :=
  ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

/--
theorem `_root_.Filter.HasBasis.uniformityPath` / 定理 `_root_.Filter.HasBasis.uniformityPath`

English:
theorem _root_.Filter.HasBasis.uniformityPath
  statement: {ι : Sort*} {p : ι -> Prop} {U : ι -> Set (X × X)}
  proof: hU.compactConvergenceUniformity_of_compact.comap _

中文:
定理 _root_.Filter.HasBasis.uniformityPath
  结论: {ι : Sort*} {p : ι -> 命题} {U : ι -> Set (X × X)}
  证明: hU.compactConvergenceUniformity_of_compact.comap _

Depends on / 依赖: compactConvergenceUniformity_of_compact, hU.compactConvergenceUniformity_of_compact.comap
-/
theorem _root_.Filter.HasBasis.uniformityPath {ι : Sort*} {p : ι -> Prop} {U : ι -> Set (X × X)}
    (hU : (𝓤 X).HasBasis p U) :
    (𝓤 (Path x y)).HasBasis p fun i => {γ | forall t, (γ.1 t, γ.2 t) in U i} :=
  hU.compactConvergenceUniformity_of_compact.comap _

/--
theorem `hasBasis_uniformity` / 定理 `hasBasis_uniformity`

English:
theorem hasBasis_uniformity
  proof: (𝓤 X).basis_sets.uniformityPath

中文:
定理 hasBasis_uniformity
  证明: (𝓤 X).basis_sets.uniformityPath

Depends on / 依赖: basis_sets, basis_sets.uniformityPath, uniformityPath
-/
theorem hasBasis_uniformity :
    (𝓤 (Path x y)).HasBasis (· in 𝓤 X) ({γ | forall t, (γ.1 t, γ.2 t) in ·}) :=
  (𝓤 X).basis_sets.uniformityPath

/--
theorem `uniformContinuous_symm` / 定理 `uniformContinuous_symm`

English:
theorem uniformContinuous_symm
  statement: UniformContinuous (Path.symm : Path x y -> Path y x)
  proof: .mpr fun U hU => hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity
    ⟨U, hU, fun _ _ h x => h (σ x)⟩

中文:
定理 uniformContinuous_symm
  结论: UniformContinuous (Path.symm : Path x y -> Path y x)
  证明: .mpr fun U hU => hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity
    ⟨U, hU, fun _ _ h x => h (σ x)⟩

Depends on / 依赖: hasBasis_uniformity, hasBasis_uniformity.uniformContinuous_iff, uniformContinuous_iff
-/
theorem uniformContinuous_symm : UniformContinuous (Path.symm : Path x y -> Path y x) :=
.mpr fun U hU => hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity
    ⟨U, hU, fun _ _ h x => h (σ x)⟩

/--
theorem `uniformContinuous_trans` / 定理 `uniformContinuous_trans`

English:
theorem uniformContinuous_trans
  proof: hasBasis_uniformity.uniformity_prod hasBasis_uniformity
.mpr fun U hU => .uniformContinuous_iff hasBasis_uniformity
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t => by
        by_cases ht : (t : Real) <= 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

中文:
定理 uniformContinuous_trans
  证明: hasBasis_uniformity.uniformity_prod hasBasis_uniformity
.mpr fun U hU => .uniformContinuous_iff hasBasis_uniformity
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t => by
        by_cases ht : (t : Real) <= 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

Depends on / 依赖: Path.trans_apply, hasBasis_uniformity, hasBasis_uniformity.uniformity_prod, trans_apply, uniformContinuous_iff, uniformity_prod
-/
theorem uniformContinuous_trans :
    UniformContinuous (Path.trans : Path x y -> Path y z -> Path x z).uncurry :=
  hasBasis_uniformity.uniformity_prod hasBasis_uniformity
.mpr fun U hU => .uniformContinuous_iff hasBasis_uniformity
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t => by
        by_cases ht : (t : Real) <= 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace X]
  body: isUniformEmbedding_coe.completeSpace by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOfPred_eqOn (Function.update (fun _ : I => y) 0 x) {0, 1}

中文:
实例 instCompleteSpace
  签名: [CompleteSpace X]
  定义体: isUniformEmbedding_coe.completeSpace by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOfPred_eqOn (Function.update (fun _ : I => y) 0 x) {0, 1}

Depends on / 依赖: ContinuousMap, ContinuousMap.isComplete_setOfPred_eqOn, Function, Function.update, Set.EqOn, completeSpace, isComplete_setOfPred_eqOn, isUniformEmbedding_coe, isUniformEmbedding_coe.completeSpace, range_coe, update
-/
instance instCompleteSpace [CompleteSpace X] : CompleteSpace (Path x y) :=
isUniformEmbedding_coe.completeSpace by simpa [Set.EqOn, range_coe]
    using ContinuousMap.isComplete_setOfPred_eqOn (Function.update (fun _ : I => y) 0 x) {0, 1}

end Path
