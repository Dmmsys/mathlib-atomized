/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

public section

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

namespace ContinuousLinearMap

variable (f : E ->L[𝕜] E') {s : Set E} {x : E}

/--
theorem `hasMFDerivWithinAt` / 定理 `hasMFDerivWithinAt`

English:
theorem hasMFDerivWithinAt
  statement: HasMFDerivAt[s] f x f
  proof: f.hasFDerivWithinAt.hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt
  结论: HasMFDerivAt[s] f x f
  证明: f.hasFDerivWithinAt.hasMFDerivWithinAt
-/
protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

/--
theorem `hasMFDerivAt` / 定理 `hasMFDerivAt`

English:
theorem hasMFDerivAt
  statement: HasMFDerivAt% f x f
  proof: f.hasFDerivAt.hasMFDerivAt

中文:
定理 hasMFDerivAt
  结论: HasMFDerivAt% f x f
  证明: f.hasFDerivAt.hasMFDerivAt
-/
protected theorem hasMFDerivAt : HasMFDerivAt% f x f :=
  f.hasFDerivAt.hasMFDerivAt

/--
theorem `mdifferentiableWithinAt` / 定理 `mdifferentiableWithinAt`

English:
theorem mdifferentiableWithinAt
  statement: MDiffAt[s] f x
  proof: f.differentiableWithinAt.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt
  结论: MDiffAt[s] f x
  证明: f.differentiableWithinAt.mdifferentiableWithinAt
-/
protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

/--
theorem `mdifferentiableOn` / 定理 `mdifferentiableOn`

English:
theorem mdifferentiableOn
  statement: MDiff[s] f
  proof: f.differentiableOn.mdifferentiableOn

中文:
定理 mdifferentiableOn
  结论: MDiff[s] f
  证明: f.differentiableOn.mdifferentiableOn
-/
protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  statement: MDiffAt f x
  proof: f.differentiableAt.mdifferentiableAt

中文:
定理 mdifferentiableAt
  结论: MDiffAt f x
  证明: f.differentiableAt.mdifferentiableAt
-/
protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  statement: MDiff f
  proof: f.differentiable.mdifferentiable

中文:
定理 mdifferentiable
  结论: MDiff f
  证明: f.differentiable.mdifferentiable
-/
protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

/--
theorem `mfderiv_eq` / 定理 `mfderiv_eq`

English:
theorem mfderiv_eq
  statement: mfderiv% f x = f
  proof: f.hasMFDerivAt.mfderiv

中文:
定理 mfderiv_eq
  结论: mfderiv% f x = f
  证明: f.hasMFDerivAt.mfderiv

Depends on / 依赖: f.hasMFDerivAt.mfderiv, hasMFDerivAt, mfderiv
-/
theorem mfderiv_eq : mfderiv% f x = f :=
  f.hasMFDerivAt.mfderiv

/--
theorem `mfderivWithin_eq` / 定理 `mfderivWithin_eq`

English:
theorem mfderivWithin_eq
  given: (hs : UniqueMDiffAt[s] x)
  statement: mfderiv[s] f x = f
  proof: f.hasMFDerivWithinAt.mfderivWithin hs

中文:
定理 mfderivWithin_eq
  条件: (hs : UniqueMDiffAt[s] x)
  结论: mfderiv[s] f x = f
  证明: f.hasMFDerivWithinAt.mfderivWithin hs

Depends on / 依赖: f.hasMFDerivWithinAt.mfderivWithin, hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

/--
theorem `hasMFDerivWithinAt` / 定理 `hasMFDerivWithinAt`

English:
theorem hasMFDerivWithinAt
  statement: HasMFDerivAt[s] f x (f : E ->L[𝕜] E')
  proof: f.hasFDerivWithinAt.hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt
  结论: HasMFDerivAt[s] f x (f : E ->L[𝕜] E')
  证明: f.hasFDerivWithinAt.hasMFDerivWithinAt
-/
protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x (f : E ->L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

/--
theorem `hasMFDerivAt` / 定理 `hasMFDerivAt`

English:
theorem hasMFDerivAt
  statement: HasMFDerivAt% f x (f : E ->L[𝕜] E')
  proof: f.hasFDerivAt.hasMFDerivAt

中文:
定理 hasMFDerivAt
  结论: HasMFDerivAt% f x (f : E ->L[𝕜] E')
  证明: f.hasFDerivAt.hasMFDerivAt
-/
protected theorem hasMFDerivAt : HasMFDerivAt% f x (f : E ->L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt

/--
theorem `mdifferentiableWithinAt` / 定理 `mdifferentiableWithinAt`

English:
theorem mdifferentiableWithinAt
  statement: MDiffAt[s] f x
  proof: f.differentiableWithinAt.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt
  结论: MDiffAt[s] f x
  证明: f.differentiableWithinAt.mdifferentiableWithinAt
-/
protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

/--
theorem `mdifferentiableOn` / 定理 `mdifferentiableOn`

English:
theorem mdifferentiableOn
  statement: MDiff[s] f
  proof: f.differentiableOn.mdifferentiableOn

中文:
定理 mdifferentiableOn
  结论: MDiff[s] f
  证明: f.differentiableOn.mdifferentiableOn
-/
protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

/--
theorem `mdifferentiableAt` / 定理 `mdifferentiableAt`

English:
theorem mdifferentiableAt
  statement: MDiffAt f x
  proof: f.differentiableAt.mdifferentiableAt

中文:
定理 mdifferentiableAt
  结论: MDiffAt f x
  证明: f.differentiableAt.mdifferentiableAt
-/
protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

/--
theorem `mdifferentiable` / 定理 `mdifferentiable`

English:
theorem mdifferentiable
  statement: MDiff f
  proof: f.differentiable.mdifferentiable

中文:
定理 mdifferentiable
  结论: MDiff f
  证明: f.differentiable.mdifferentiable
-/
protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

/--
theorem `mfderiv_eq` / 定理 `mfderiv_eq`

English:
theorem mfderiv_eq
  statement: mfderiv% f x = (f : E ->L[𝕜] E')
  proof: f.hasMFDerivAt.mfderiv

中文:
定理 mfderiv_eq
  结论: mfderiv% f x = (f : E ->L[𝕜] E')
  证明: f.hasMFDerivAt.mfderiv

Depends on / 依赖: f.hasMFDerivAt.mfderiv, hasMFDerivAt, mfderiv
-/
theorem mfderiv_eq : mfderiv% f x = (f : E ->L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv

/--
theorem `mfderivWithin_eq` / 定理 `mfderivWithin_eq`

English:
theorem mfderivWithin_eq
  given: (hs : UniqueMDiffAt[s] x)
  proof: f.hasMFDerivWithinAt.mfderivWithin hs

中文:
定理 mfderivWithin_eq
  条件: (hs : UniqueMDiffAt[s] x)
  证明: f.hasMFDerivWithinAt.mfderivWithin hs

Depends on / 依赖: f.hasMFDerivWithinAt.mfderivWithin, hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = (f : E ->L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id


/--
theorem `hasMFDerivAt_id` / 定理 `hasMFDerivAt_id`

English:
theorem hasMFDerivAt_id
  given: (x : M)
  proof: by
  refine ⟨continuousAt_id, ?_⟩
  have : forallᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _

中文:
定理 hasMFDerivAt_id
  条件: (x : M)
  证明: by
  refine ⟨continuousAt_id, ?_⟩
  have : forallᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _

Depends on / 依赖: Filter, Filter.mem_of_superset, HasFDerivWithinAt, HasFDerivWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq, continuousAt_id, extChartAt, extChartAt_target_mem_nhdsWithin, hasFDerivWithinAt_id, mem_of_superset, mfld_set_tac, mfld_simps
-/
theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt% (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : forallᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

/--
theorem `hasMFDerivWithinAt_id` / 定理 `hasMFDerivWithinAt_id`

English:
theorem hasMFDerivWithinAt_id
  given: (s : Set M) (x : M)
  proof: (hasMFDerivAt_id x).hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt_id
  条件: (s : Set M) (x : M)
  证明: (hasMFDerivAt_id x).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivAt_id, hasMFDerivWithinAt
-/
theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivAt[s] (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt

/--
theorem `mdifferentiableAt_id` / 定理 `mdifferentiableAt_id`

English:
theorem mdifferentiableAt_id
  statement: MDiffAt (@id M) x
  proof: (hasMFDerivAt_id x).mdifferentiableAt

中文:
定理 mdifferentiableAt_id
  结论: MDiffAt (@id M) x
  证明: (hasMFDerivAt_id x).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt_id, mdifferentiableAt
-/
theorem mdifferentiableAt_id : MDiffAt (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_id` / 定理 `mdifferentiableWithinAt_id`

English:
theorem mdifferentiableWithinAt_id
  statement: MDiffAt[s] (@id M) x
  proof: mdifferentiableAt_id.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_id
  结论: MDiffAt[s] (@id M) x
  证明: mdifferentiableAt_id.mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_id, mdifferentiableAt_id.mdifferentiableWithinAt, mdifferentiableWithinAt
-/
theorem mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x :=
  mdifferentiableAt_id.mdifferentiableWithinAt

/--
theorem `mdifferentiable_id` / 定理 `mdifferentiable_id`

English:
theorem mdifferentiable_id
  statement: MDiff (@id M)
  proof: fun _ => mdifferentiableAt_id

中文:
定理 mdifferentiable_id
  结论: MDiff (@id M)
  证明: fun _ => mdifferentiableAt_id

Depends on / 依赖: mdifferentiableAt_id
-/
theorem mdifferentiable_id : MDiff (@id M) := fun _ => mdifferentiableAt_id

/--
theorem `mdifferentiableOn_id` / 定理 `mdifferentiableOn_id`

English:
theorem mdifferentiableOn_id
  statement: MDiff[s] (@id M)
  proof: mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]

中文:
定理 mdifferentiableOn_id
  结论: MDiff[s] (@id M)
  证明: mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableOn, mdifferentiable_id, mdifferentiable_id.mdifferentiableOn
-/
theorem mdifferentiableOn_id : MDiff[s] (@id M) :=
  mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]
/--
theorem `mfderiv_id` / 定理 `mfderiv_id`

English:
theorem mfderiv_id
  statement: mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
  proof: (hasMFDerivAt_id x).mfderiv

中文:
定理 mfderiv_id
  结论: mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x)
  证明: (hasMFDerivAt_id x).mfderiv

Depends on / 依赖: hasMFDerivAt_id, mfderiv
-/
theorem mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) :=
  (hasMFDerivAt_id x).mfderiv

/--
theorem `mfderivWithin_id` / 定理 `mfderivWithin_id`

English:
theorem mfderivWithin_id
  given: (hxs : UniqueMDiffAt[s] x)
  proof: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

中文:
定理 mfderivWithin_id
  条件: (hxs : UniqueMDiffAt[s] x)
  证明: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

Depends on / 依赖: MDifferentiable, MDifferentiable.mfderivWithin, mdifferentiableAt_id, mfderivWithin, mfderiv_id
-/
theorem mfderivWithin_id (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/--
theorem `tangentMap_id` / 定理 `tangentMap_id`

English:
theorem tangentMap_id
  statement: tangentMap% (@id M) = id
  proof: by ext1 ⟨x, v⟩; simp [tangentMap]

中文:
定理 tangentMap_id
  结论: tangentMap% (@id M) = id
  证明: by ext1 ⟨x, v⟩; simp [tangentMap]

Depends on / 依赖: tangentMap
-/
theorem tangentMap_id : tangentMap% (@id M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]

/--
theorem `tangentMapWithin_id` / 定理 `tangentMapWithin_id`

English:
theorem tangentMapWithin_id
  given: {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj)
  proof: by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

中文:
定理 tangentMapWithin_id
  条件: {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj)
  证明: by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

Depends on / 依赖: mfderivWithin_id, tangentMapWithin
-/
theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (id : M -> M) p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivAt_const` / 定理 `hasMFDerivAt_const`

English:
theorem hasMFDerivAt_const
  given: (c : M') (x : M)
  proof: ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

中文:
定理 hasMFDerivAt_const
  条件: (c : M') (x : M)
  证明: ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

Depends on / 依赖: Function, Function.comp_def, comp_def, fun_prop, hasFDerivWithinAt_const
-/
theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt% (fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c) :=
  ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

/--
theorem `hasMFDerivWithinAt_const` / 定理 `hasMFDerivWithinAt_const`

English:
theorem hasMFDerivWithinAt_const
  given: (c : M') (s : Set M) (x : M)
  proof: (hasMFDerivAt_const c x).hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt_const
  条件: (c : M') (s : Set M) (x : M)
  证明: (hasMFDerivAt_const c x).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivAt_const, hasMFDerivWithinAt
-/
theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivAt[s] (fun _ : M => c) x (0 : TangentSpace% x ->L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).hasMFDerivWithinAt

/--
theorem `mdifferentiableAt_const` / 定理 `mdifferentiableAt_const`

English:
theorem mdifferentiableAt_const
  statement: MDiffAt (fun _ : M => c) x
  proof: (hasMFDerivAt_const c x).mdifferentiableAt

中文:
定理 mdifferentiableAt_const
  结论: MDiffAt (fun _ : M => c) x
  证明: (hasMFDerivAt_const c x).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt_const, mdifferentiableAt
-/
theorem mdifferentiableAt_const : MDiffAt (fun _ : M => c) x :=
  (hasMFDerivAt_const c x).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_const` / 定理 `mdifferentiableWithinAt_const`

English:
theorem mdifferentiableWithinAt_const
  statement: MDiffAt[s] (fun _ : M => c) x
  proof: mdifferentiableAt_const.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_const
  结论: MDiffAt[s] (fun _ : M => c) x
  证明: mdifferentiableAt_const.mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_const, mdifferentiableAt_const.mdifferentiableWithinAt, mdifferentiableWithinAt
-/
theorem mdifferentiableWithinAt_const : MDiffAt[s] (fun _ : M => c) x :=
  mdifferentiableAt_const.mdifferentiableWithinAt

/--
theorem `mdifferentiable_const` / 定理 `mdifferentiable_const`

English:
theorem mdifferentiable_const
  statement: MDiff fun _ : M => c
  proof: fun _ => mdifferentiableAt_const

中文:
定理 mdifferentiable_const
  结论: MDiff fun _ : M => c
  证明: fun _ => mdifferentiableAt_const

Depends on / 依赖: mdifferentiableAt_const
-/
theorem mdifferentiable_const : MDiff fun _ : M => c := fun _ => mdifferentiableAt_const

/--
theorem `mdifferentiableOn_const` / 定理 `mdifferentiableOn_const`

English:
theorem mdifferentiableOn_const
  statement: MDiff[s] (fun _ : M => c)
  proof: mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]

中文:
定理 mdifferentiableOn_const
  结论: MDiff[s] (fun _ : M => c)
  证明: mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableOn, mdifferentiable_const, mdifferentiable_const.mdifferentiableOn
-/
theorem mdifferentiableOn_const : MDiff[s] (fun _ : M => c) :=
  mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]
/--
theorem `mfderiv_const` / 定理 `mfderiv_const`

English:
theorem mfderiv_const
  proof: (hasMFDerivAt_const c x).mfderiv

中文:
定理 mfderiv_const
  证明: (hasMFDerivAt_const c x).mfderiv

Depends on / 依赖: hasMFDerivAt_const, mfderiv
-/
theorem mfderiv_const :
    mfderiv% (fun _ : M => c) x = (0 : TangentSpace% x ->L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).mfderiv

/--
theorem `mfderivWithin_const` / 定理 `mfderivWithin_const`

English:
theorem mfderivWithin_const
  proof: (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

中文:
定理 mfderivWithin_const
  证明: (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

Depends on / 依赖: hasMFDerivWithinAt_const, mfderivWithin_eq_zero
-/
theorem mfderivWithin_const :
    mfderiv[s] (fun _ : M => c) x = (0 : TangentSpace% x ->L[𝕜] TangentSpace% c) :=
  (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

end Const

section Prod


/--
theorem `MDifferentiableWithinAt.prodMk` / 定理 `MDifferentiableWithinAt.prodMk`

English:
theorem MDifferentiableWithinAt.prodMk
  statement: {f : M -> M'} {g : M -> M''}
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 MDifferentiableWithinAt.prodMk
  结论: {f : M -> M'} {g : M -> M''}
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem MDifferentiableWithinAt.prodMk {f : M -> M'} {g : M -> M''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
theorem `HasMFDerivWithinAt.prodMk` / 定理 `HasMFDerivWithinAt.prodMk`

English:
theorem HasMFDerivWithinAt.prodMk
  statement: {f : M -> M'} {g : M -> M''}
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 HasMFDerivWithinAt.prodMk
  结论: {f : M -> M'} {g : M -> M''}
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem HasMFDerivWithinAt.prodMk {f : M -> M'} {g : M -> M''}
    {df : TangentSpace% x ->L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s] f x df)
    {dg : TangentSpace% x ->L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt[s] g x dg) :
    HasMFDerivAt[s] (fun y => (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
lemma `mfderivWithin_prodMk` / 引理 `mfderivWithin_prodMk`

English:
lemma mfderivWithin_prodMk
  statement: {f : M -> M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
  proof: (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

中文:
引理 mfderivWithin_prodMk
  结论: {f : M -> M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
  证明: (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.prodMk, hg.hasMFDerivWithinAt, mfderivWithin, prodMk
-/
lemma mfderivWithin_prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (fun x => (f x, g x)) x = (mfderiv[s] f x).prod (mfderiv[s] g x) :=
  (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

/--
lemma `mfderiv_prodMk` / 引理 `mfderiv_prodMk`

English:
lemma mfderiv_prodMk
  given: {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

中文:
引理 mfderiv_prodMk
  条件: {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

Depends on / 依赖: hf.mdifferentiableWithinAt, hg.mdifferentiableWithinAt, mdifferentiableWithinAt, mfderivWithin_prodMk, mfderivWithin_univ, simp_rw, uniqueMDiffWithinAt_univ
-/
lemma mfderiv_prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (fun x => (f x, g x)) x = (mfderiv% f x).prod (mfderiv% g x) := by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

/--
theorem `MDifferentiableAt.prodMk` / 定理 `MDifferentiableAt.prodMk`

English:
theorem MDifferentiableAt.prodMk
  given: {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x)
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 MDifferentiableAt.prodMk
  条件: {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x)
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem MDifferentiableAt.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDiffAt (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
theorem `HasMFDerivAt.prodMk` / 定理 `HasMFDerivAt.prodMk`

English:
theorem HasMFDerivAt.prodMk
  statement: {f : M -> M'} {g : M -> M''}
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 HasMFDerivAt.prodMk
  结论: {f : M -> M'} {g : M -> M''}
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem HasMFDerivAt.prodMk {f : M -> M'} {g : M -> M''}
    {df : TangentSpace% x ->L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt% f x df)
    {dg : TangentSpace% x ->L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt% g x dg) :
    HasMFDerivAt% (fun y => (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
theorem `MDifferentiableWithinAt.prodMk_space` / 定理 `MDifferentiableWithinAt.prodMk_space`

English:
theorem MDifferentiableWithinAt.prodMk_space
  statement: {f : M -> E'} {g : M -> E''}
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 MDifferentiableWithinAt.prodMk_space
  结论: {f : M -> E'} {g : M -> E''}
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem MDifferentiableWithinAt.prodMk_space {f : M -> E'} {g : M -> E''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
theorem `MDifferentiableAt.prodMk_space` / 定理 `MDifferentiableAt.prodMk_space`

English:
theorem MDifferentiableAt.prodMk_space
  statement: {f : M -> E'} {g : M -> E''}
  proof: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

中文:
定理 MDifferentiableAt.prodMk_space
  结论: {f : M -> E'} {g : M -> E''}
  证明: ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

Depends on / 依赖: prodMk
-/
theorem MDifferentiableAt.prodMk_space {f : M -> E'} {g : M -> E''}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/--
theorem `MDifferentiableOn.prodMk` / 定理 `MDifferentiableOn.prodMk`

English:
theorem MDifferentiableOn.prodMk
  given: {f : M -> M'} {g : M -> M''} (hf : MDiff[s] f) (hg : MDiff[s] g)
  proof: fun x hx => (hf x hx).prodMk (hg x hx)

中文:
定理 MDifferentiableOn.prodMk
  条件: {f : M -> M'} {g : M -> M''} (hf : MDiff[s] f) (hg : MDiff[s] g)
  证明: fun x hx => (hf x hx).prodMk (hg x hx)

Depends on / 依赖: prodMk
-/
theorem MDifferentiableOn.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (fun x => (f x, g x)) := fun x hx => (hf x hx).prodMk (hg x hx)

/--
theorem `MDifferentiable.prodMk` / 定理 `MDifferentiable.prodMk`

English:
theorem MDifferentiable.prodMk
  given: {f : M -> M'} {g : M -> M''} (hf : MDiff f) (hg : MDiff g)
  proof: fun x => (hf x).prodMk (hg x)

中文:
定理 MDifferentiable.prodMk
  条件: {f : M -> M'} {g : M -> M''} (hf : MDiff f) (hg : MDiff g)
  证明: fun x => (hf x).prodMk (hg x)

Depends on / 依赖: prodMk
-/
theorem MDifferentiable.prodMk {f : M -> M'} {g : M -> M''} (hf : MDiff f) (hg : MDiff g) :
    MDiff fun x => (f x, g x) := fun x => (hf x).prodMk (hg x)

/--
theorem `MDifferentiableOn.prodMk_space` / 定理 `MDifferentiableOn.prodMk_space`

English:
theorem MDifferentiableOn.prodMk_space
  statement: {f : M -> E'} {g : M -> E''}
  proof: fun x hx => (hf x hx).prodMk_space (hg x hx)

中文:
定理 MDifferentiableOn.prodMk_space
  结论: {f : M -> E'} {g : M -> E''}
  证明: fun x hx => (hf x hx).prodMk_space (hg x hx)

Depends on / 依赖: prodMk_space
-/
theorem MDifferentiableOn.prodMk_space {f : M -> E'} {g : M -> E''}
    (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prodMk_space (hg x hx)

/--
theorem `MDifferentiable.prodMk_space` / 定理 `MDifferentiable.prodMk_space`

English:
theorem MDifferentiable.prodMk_space
  given: {f : M -> E'} {g : M -> E''} (hf : MDiff f) (hg : MDiff g)
  proof: fun x => (hf x).prodMk_space (hg x)

中文:
定理 MDifferentiable.prodMk_space
  条件: {f : M -> E'} {g : M -> E''} (hf : MDiff f) (hg : MDiff g)
  证明: fun x => (hf x).prodMk_space (hg x)

Depends on / 依赖: prodMk_space
-/
theorem MDifferentiable.prodMk_space {f : M -> E'} {g : M -> E''} (hf : MDiff f) (hg : MDiff g) :
    MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
fun x => (hf x).prodMk_space (hg x)

/--
theorem `hasMFDerivAt_fst` / 定理 `hasMFDerivAt_fst`

English:
theorem hasMFDerivAt_fst
  given: (x : M × M')
  proof: by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.

中文:
定理 hasMFDerivAt_fst
  条件: (x : M × M')
  证明: by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.

Depends on / 依赖: I.prod, Prod.fst, continuousAt, continuous_fst, continuous_fst.continuousAt, extChartAt
-/
theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt% (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
exact (extChartAt I x.1).right_inv (extChartAt I x.1).map_source (mem_extChartAt_source _)

/--
theorem `hasMFDerivWithinAt_fst` / 定理 `hasMFDerivWithinAt_fst`

English:
theorem hasMFDerivWithinAt_fst
  given: (s : Set (M × M')) (x : M × M')
  proof: (hasMFDerivAt_fst x).hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt_fst
  条件: (s : Set (M × M')) (x : M × M')
  证明: (hasMFDerivAt_fst x).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivAt_fst, hasMFDerivWithinAt
-/
theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_fst x).hasMFDerivWithinAt

/--
theorem `mdifferentiableAt_fst` / 定理 `mdifferentiableAt_fst`

English:
theorem mdifferentiableAt_fst
  given: {x : M × M'}
  statement: MDiffAt (@Prod.fst M M') x
  proof: (hasMFDerivAt_fst x).mdifferentiableAt

中文:
定理 mdifferentiableAt_fst
  条件: {x : M × M'}
  结论: MDiffAt (@Prod.fst M M') x
  证明: (hasMFDerivAt_fst x).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt_fst, mdifferentiableAt
-/
theorem mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Prod.fst M M') x :=
  (hasMFDerivAt_fst x).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_fst` / 定理 `mdifferentiableWithinAt_fst`

English:
theorem mdifferentiableWithinAt_fst
  given: {s : Set (M × M')} {x : M × M'}
  proof: mdifferentiableAt_fst.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_fst
  条件: {s : Set (M × M')} {x : M × M'}
  证明: mdifferentiableAt_fst.mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_fst, mdifferentiableAt_fst.mdifferentiableWithinAt, mdifferentiableWithinAt
-/
theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.fst M M') x :=
  mdifferentiableAt_fst.mdifferentiableWithinAt

/--
theorem `mdifferentiable_fst` / 定理 `mdifferentiable_fst`

English:
theorem mdifferentiable_fst
  statement: MDiff (@Prod.fst M M')
  proof: fun _ => mdifferentiableAt_fst

中文:
定理 mdifferentiable_fst
  结论: MDiff (@Prod.fst M M')
  证明: fun _ => mdifferentiableAt_fst

Depends on / 依赖: mdifferentiableAt_fst
-/
theorem mdifferentiable_fst : MDiff (@Prod.fst M M') := fun _ => mdifferentiableAt_fst

/--
theorem `mdifferentiableOn_fst` / 定理 `mdifferentiableOn_fst`

English:
theorem mdifferentiableOn_fst
  given: {s : Set (M × M')}
  statement: MDiff[s] (@Prod.fst M M')
  proof: mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]

中文:
定理 mdifferentiableOn_fst
  条件: {s : Set (M × M')}
  结论: MDiff[s] (@Prod.fst M M')
  证明: mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableOn, mdifferentiable_fst, mdifferentiable_fst.mdifferentiableOn
-/
theorem mdifferentiableOn_fst {s : Set (M × M')} : MDiff[s] (@Prod.fst M M') :=
  mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]
/--
theorem `mfderiv_fst` / 定理 `mfderiv_fst`

English:
theorem mfderiv_fst
  given: {x : M × M'}
  proof: (hasMFDerivAt_fst x).mfderiv

中文:
定理 mfderiv_fst
  条件: {x : M × M'}
  证明: (hasMFDerivAt_fst x).mfderiv

Depends on / 依赖: hasMFDerivAt_fst, mfderiv
-/
theorem mfderiv_fst {x : M × M'} :
    mfderiv% (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_fst x).mfderiv

/--
theorem `mfderivWithin_fst` / 定理 `mfderivWithin_fst`

English:
theorem mfderivWithin_fst
  statement: {s : Set (M × M')} {x : M × M'}
  proof: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]

中文:
定理 mfderivWithin_fst
  结论: {s : Set (M × M')} {x : M × M'}
  证明: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]

Depends on / 依赖: MDifferentiable, MDifferentiable.mfderivWithin, mdifferentiableAt_fst, mfderivWithin, mfderiv_fst
-/
theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]
/--
theorem `tangentMap_prodFst` / 定理 `tangentMap_prodFst`

English:
theorem tangentMap_prodFst
  given: {p : TangentBundle (I.prod I') (M × M')}
  proof: by
  simp [tangentMap]; rfl

中文:
定理 tangentMap_prodFst
  条件: {p : TangentBundle (I.prod I') (M × M')}
  证明: by
  simp [tangentMap]; rfl

Depends on / 依赖: tangentMap
-/
theorem tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp [tangentMap]; rfl

/--
theorem `tangentMapWithin_prodFst` / 定理 `tangentMapWithin_prodFst`

English:
theorem tangentMapWithin_prodFst
  statement: {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
  proof: by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

中文:
定理 tangentMapWithin_prodFst
  结论: {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
  证明: by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

Depends on / 依赖: mfderivWithin_fst, tangentMapWithin
-/
theorem tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

/--
theorem `hasMFDerivAt_snd` / 定理 `hasMFDerivAt_snd`

English:
theorem hasMFDerivAt_snd
  given: (x : M × M')
  proof: by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I

中文:
定理 hasMFDerivAt_snd
  条件: (x : M × M')
  证明: by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I

Depends on / 依赖: I.prod, Prod.snd, continuousAt, continuous_snd, continuous_snd.continuousAt, extChartAt
-/
theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt% (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    forallᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
exact (extChartAt I' x.2).right_inv (extChartAt I' x.2).map_source (mem_extChartAt_source _)

/--
theorem `hasMFDerivWithinAt_snd` / 定理 `hasMFDerivWithinAt_snd`

English:
theorem hasMFDerivWithinAt_snd
  given: (s : Set (M × M')) (x : M × M')
  proof: (hasMFDerivAt_snd x).hasMFDerivWithinAt

中文:
定理 hasMFDerivWithinAt_snd
  条件: (s : Set (M × M')) (x : M × M')
  证明: (hasMFDerivAt_snd x).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivAt_snd, hasMFDerivWithinAt
-/
theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_snd x).hasMFDerivWithinAt

/--
theorem `mdifferentiableAt_snd` / 定理 `mdifferentiableAt_snd`

English:
theorem mdifferentiableAt_snd
  given: {x : M × M'}
  statement: MDiffAt (@Prod.snd M M') x
  proof: (hasMFDerivAt_snd x).mdifferentiableAt

中文:
定理 mdifferentiableAt_snd
  条件: {x : M × M'}
  结论: MDiffAt (@Prod.snd M M') x
  证明: (hasMFDerivAt_snd x).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt_snd, mdifferentiableAt
-/
theorem mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Prod.snd M M') x :=
  (hasMFDerivAt_snd x).mdifferentiableAt

/--
theorem `mdifferentiableWithinAt_snd` / 定理 `mdifferentiableWithinAt_snd`

English:
theorem mdifferentiableWithinAt_snd
  given: {s : Set (M × M')} {x : M × M'}
  proof: mdifferentiableAt_snd.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_snd
  条件: {s : Set (M × M')} {x : M × M'}
  证明: mdifferentiableAt_snd.mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableAt_snd, mdifferentiableAt_snd.mdifferentiableWithinAt, mdifferentiableWithinAt
-/
theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.snd M M') x := mdifferentiableAt_snd.mdifferentiableWithinAt

/--
theorem `mdifferentiable_snd` / 定理 `mdifferentiable_snd`

English:
theorem mdifferentiable_snd
  statement: MDiff (@Prod.snd M M')
  proof: fun _ => mdifferentiableAt_snd

中文:
定理 mdifferentiable_snd
  结论: MDiff (@Prod.snd M M')
  证明: fun _ => mdifferentiableAt_snd

Depends on / 依赖: mdifferentiableAt_snd
-/
theorem mdifferentiable_snd : MDiff (@Prod.snd M M') := fun _ => mdifferentiableAt_snd

/--
theorem `mdifferentiableOn_snd` / 定理 `mdifferentiableOn_snd`

English:
theorem mdifferentiableOn_snd
  given: {s : Set (M × M')}
  statement: MDiff[s] (@Prod.snd M M')
  proof: mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]

中文:
定理 mdifferentiableOn_snd
  条件: {s : Set (M × M')}
  结论: MDiff[s] (@Prod.snd M M')
  证明: mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableOn, mdifferentiable_snd, mdifferentiable_snd.mdifferentiableOn
-/
theorem mdifferentiableOn_snd {s : Set (M × M')} : MDiff[s] (@Prod.snd M M') :=
  mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]
/--
theorem `mfderiv_snd` / 定理 `mfderiv_snd`

English:
theorem mfderiv_snd
  given: {x : M × M'}
  proof: (hasMFDerivAt_snd x).mfderiv

中文:
定理 mfderiv_snd
  条件: {x : M × M'}
  证明: (hasMFDerivAt_snd x).mfderiv

Depends on / 依赖: hasMFDerivAt_snd, mfderiv
-/
theorem mfderiv_snd {x : M × M'} :
    mfderiv% (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_snd x).mfderiv

/--
theorem `mfderivWithin_snd` / 定理 `mfderivWithin_snd`

English:
theorem mfderivWithin_snd
  statement: {s : Set (M × M')} {x : M × M'}
  proof: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

中文:
定理 mfderivWithin_snd
  结论: {s : Set (M × M')} {x : M × M'}
  证明: by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

Depends on / 依赖: MDifferentiable, MDifferentiable.mfderivWithin, mdifferentiableAt_snd, mfderivWithin, mfderiv_snd
-/
theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

/--
theorem `MDifferentiableWithinAt.fst` / 定理 `MDifferentiableWithinAt.fst`

English:
theorem MDifferentiableWithinAt.fst
  statement: {f : N -> M × M'} {s : Set N} {x : N}
  proof: mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

中文:
定理 MDifferentiableWithinAt.fst
  结论: {f : N -> M × M'} {s : Set N} {x : N}
  证明: mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

Depends on / 依赖: comp_mdifferentiableWithinAt, mdifferentiableAt_fst, mdifferentiableAt_fst.comp_mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.fst {f : N -> M × M'} {s : Set N} {x : N}
    (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x => (f x).1) x :=
  mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

/--
theorem `MDifferentiableAt.fst` / 定理 `MDifferentiableAt.fst`

English:
theorem MDifferentiableAt.fst
  given: {f : N -> M × M'} {x : N} (hf : MDiffAt f x)
  proof: mdifferentiableAt_fst.comp x hf

中文:
定理 MDifferentiableAt.fst
  条件: {f : N -> M × M'} {x : N} (hf : MDiffAt f x)
  证明: mdifferentiableAt_fst.comp x hf

Depends on / 依赖: mdifferentiableAt_fst, mdifferentiableAt_fst.comp
-/
theorem MDifferentiableAt.fst {f : N -> M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x => (f x).1) x :=
  mdifferentiableAt_fst.comp x hf

/--
theorem `MDifferentiable.fst` / 定理 `MDifferentiable.fst`

English:
theorem MDifferentiable.fst
  given: {f : N -> M × M'} (hf : MDiff f)
  statement: MDiff fun x => (f x).1
  proof: mdifferentiable_fst.comp hf

中文:
定理 MDifferentiable.fst
  条件: {f : N -> M × M'} (hf : MDiff f)
  结论: MDiff fun x => (f x).1
  证明: mdifferentiable_fst.comp hf

Depends on / 依赖: mdifferentiable_fst, mdifferentiable_fst.comp
-/
theorem MDifferentiable.fst {f : N -> M × M'} (hf : MDiff f) : MDiff fun x => (f x).1 :=
  mdifferentiable_fst.comp hf

/--
theorem `MDifferentiableWithinAt.snd` / 定理 `MDifferentiableWithinAt.snd`

English:
theorem MDifferentiableWithinAt.snd
  given: {f : N -> M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x)
  proof: mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

中文:
定理 MDifferentiableWithinAt.snd
  条件: {f : N -> M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x)
  证明: mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

Depends on / 依赖: comp_mdifferentiableWithinAt, mdifferentiableAt_snd, mdifferentiableAt_snd.comp_mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.snd {f : N -> M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x => (f x).2) x :=
  mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

/--
theorem `MDifferentiableAt.snd` / 定理 `MDifferentiableAt.snd`

English:
theorem MDifferentiableAt.snd
  given: {f : N -> M × M'} {x : N} (hf : MDiffAt f x)
  proof: mdifferentiableAt_snd.comp x hf

中文:
定理 MDifferentiableAt.snd
  条件: {f : N -> M × M'} {x : N} (hf : MDiffAt f x)
  证明: mdifferentiableAt_snd.comp x hf

Depends on / 依赖: mdifferentiableAt_snd, mdifferentiableAt_snd.comp
-/
theorem MDifferentiableAt.snd {f : N -> M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x => (f x).2) x :=
  mdifferentiableAt_snd.comp x hf

/--
theorem `MDifferentiable.snd` / 定理 `MDifferentiable.snd`

English:
theorem MDifferentiable.snd
  given: {f : N -> M × M'} (hf : MDiff f)
  statement: MDiff fun x => (f x).2
  proof: mdifferentiable_snd.comp hf

中文:
定理 MDifferentiable.snd
  条件: {f : N -> M × M'} (hf : MDiff f)
  结论: MDiff fun x => (f x).2
  证明: mdifferentiable_snd.comp hf

Depends on / 依赖: mdifferentiable_snd, mdifferentiable_snd.comp
-/
theorem MDifferentiable.snd {f : N -> M × M'} (hf : MDiff f) : MDiff fun x => (f x).2 :=
  mdifferentiable_snd.comp hf

/--
theorem `mdifferentiableWithinAt_prod_iff` / 定理 `mdifferentiableWithinAt_prod_iff`

English:
theorem mdifferentiableWithinAt_prod_iff
  given: (f : M -> M' × N')
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 mdifferentiableWithinAt_prod_iff
  条件: (f : M -> M' × N')
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
theorem mdifferentiableWithinAt_prod_iff (f : M -> M' × N') :
    MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

/--
theorem `mdifferentiableWithinAt_prod_module_iff` / 定理 `mdifferentiableWithinAt_prod_module_iff`

English:
theorem mdifferentiableWithinAt_prod_module_iff
  given: (f : M -> F₁ × F₂)
  proof: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

中文:
定理 mdifferentiableWithinAt_prod_module_iff
  条件: (f : M -> F₁ × F₂)
  证明: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

Depends on / 依赖: chartedSpaceSelf_prod, mdifferentiableWithinAt_prod_iff, modelWithCornersSelf_prod
-/
theorem mdifferentiableWithinAt_prod_module_iff (f : M -> F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔
      MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

/--
theorem `mdifferentiableAt_prod_iff` / 定理 `mdifferentiableAt_prod_iff`

English:
theorem mdifferentiableAt_prod_iff
  given: (f : M -> M' × N')
  proof: by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

中文:
定理 mdifferentiableAt_prod_iff
  条件: (f : M -> M' × N')
  证明: by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

Depends on / 依赖: mdifferentiableWithinAt_prod_iff, mdifferentiableWithinAt_univ, simp_rw
-/
theorem mdifferentiableAt_prod_iff (f : M -> M' × N') :
    MDiffAt f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

/--
theorem `mdifferentiableAt_prod_module_iff` / 定理 `mdifferentiableAt_prod_module_iff`

English:
theorem mdifferentiableAt_prod_module_iff
  given: (f : M -> F₁ × F₂)
  proof: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

中文:
定理 mdifferentiableAt_prod_module_iff
  条件: (f : M -> F₁ × F₂)
  证明: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

Depends on / 依赖: chartedSpaceSelf_prod, mdifferentiableAt_prod_iff, modelWithCornersSelf_prod
-/
theorem mdifferentiableAt_prod_module_iff (f : M -> F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) f x ↔
      MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

/--
theorem `mdifferentiableOn_prod_iff` / 定理 `mdifferentiableOn_prod_iff`

English:
theorem mdifferentiableOn_prod_iff
  given: (f : M -> M' × N')
  proof: ⟨fun h => ⟨fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx => (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

中文:
定理 mdifferentiableOn_prod_iff
  条件: (f : M -> M' × N')
  证明: ⟨fun h => ⟨fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx => (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

Depends on / 依赖: mdifferentiableWithinAt_prod_iff
-/
theorem mdifferentiableOn_prod_iff (f : M -> M' × N') :
    MDiff[s] f ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) :=
  ⟨fun h => ⟨fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx => ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx => (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

/--
theorem `mdifferentiableOn_prod_module_iff` / 定理 `mdifferentiableOn_prod_module_iff`

English:
theorem mdifferentiableOn_prod_module_iff
  given: (f : M -> F₁ × F₂)
  proof: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

中文:
定理 mdifferentiableOn_prod_module_iff
  条件: (f : M -> F₁ × F₂)
  证明: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

Depends on / 依赖: chartedSpaceSelf_prod, mdifferentiableOn_prod_iff, modelWithCornersSelf_prod
-/
theorem mdifferentiableOn_prod_module_iff (f : M -> F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) f s ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

/--
theorem `mdifferentiable_prod_iff` / 定理 `mdifferentiable_prod_iff`

English:
theorem mdifferentiable_prod_iff
  given: (f : M -> M' × N')
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert! h.1.prodMk h.2⟩

中文:
定理 mdifferentiable_prod_iff
  条件: (f : M -> M' × N')
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert! h.1.prodMk h.2⟩

Depends on / 依赖: convert, h.fst, h.snd, prodMk
-/
theorem mdifferentiable_prod_iff (f : M -> M' × N') :
    MDiff f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => by convert! h.1.prodMk h.2⟩

/--
theorem `mdifferentiable_prod_module_iff` / 定理 `mdifferentiable_prod_module_iff`

English:
theorem mdifferentiable_prod_module_iff
  given: (f : M -> F₁ × F₂)
  proof: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f

中文:
定理 mdifferentiable_prod_module_iff
  条件: (f : M -> F₁ × F₂)
  证明: by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f

Depends on / 依赖: chartedSpaceSelf_prod, mdifferentiable_prod_iff, modelWithCornersSelf_prod
-/
theorem mdifferentiable_prod_module_iff (f : M -> F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod]; rw [← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f


section prodMap

variable {f : M -> M'} {g : N -> N'} {r : Set N} {y : N}

/--
theorem `MDifferentiableWithinAt.prodMap'` / 定理 `MDifferentiableWithinAt.prodMap'`

English:
theorem MDifferentiableWithinAt.prodMap'
  statement: {p : M × N}
  proof: (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

中文:
定理 MDifferentiableWithinAt.prodMap'
  结论: {p : M × N}
  证明: (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

Depends on / 依赖: hf.comp, hg.comp, mdifferentiableWithinAt_fst, mdifferentiableWithinAt_snd, prodMk, prod_subset_preimage_fst, prod_subset_preimage_snd
-/
theorem MDifferentiableWithinAt.prodMap' {p : M × N}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[r] g p.2) :
    MDiffAt[s ×ˢ r] (Prod.map f g) p :=
(hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

/--
theorem `MDifferentiableWithinAt.prodMap` / 定理 `MDifferentiableWithinAt.prodMap`

English:
theorem MDifferentiableWithinAt.prodMap
  given: (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y)
  proof: hf.prodMap' hg

中文:
定理 MDifferentiableWithinAt.prodMap
  条件: (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y)
  证明: hf.prodMap' hg

Depends on / 依赖: hf.prodMap, prodMap
-/
theorem MDifferentiableWithinAt.prodMap (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y) :
    MDiffAt[s ×ˢ r] (Prod.map f g) (x, y) :=
  hf.prodMap' hg

/--
theorem `MDifferentiableAt.prodMap` / 定理 `MDifferentiableAt.prodMap`

English:
theorem MDifferentiableAt.prodMap
  given: (hf : MDiffAt f x) (hg : MDiffAt g y)
  proof: by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

中文:
定理 MDifferentiableAt.prodMap
  条件: (hf : MDiffAt f x) (hg : MDiffAt g y)
  证明: by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

Depends on / 依赖: convert, hf.prodMap, mdifferentiableWithinAt_univ, prodMap, univ_prod_univ, univ_prod_univ.symm
-/
theorem MDifferentiableAt.prodMap (hf : MDiffAt f x) (hg : MDiffAt g y) :
    MDiffAt (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

/--
theorem `MDifferentiableAt.prodMap'` / 定理 `MDifferentiableAt.prodMap'`

English:
theorem MDifferentiableAt.prodMap'
  statement: {p : M × N}
  proof: hf.prodMap hg

中文:
定理 MDifferentiableAt.prodMap'
  结论: {p : M × N}
  证明: hf.prodMap hg

Depends on / 依赖: hf.prodMap, prodMap
-/
theorem MDifferentiableAt.prodMap' {p : M × N}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) : MDiffAt (Prod.map f g) p :=
  hf.prodMap hg

/--
theorem `MDifferentiableOn.prodMap` / 定理 `MDifferentiableOn.prodMap`

English:
theorem MDifferentiableOn.prodMap
  given: (hf : MDiff[s] f) (hg : MDiff[r] g)
  proof: (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

中文:
定理 MDifferentiableOn.prodMap
  条件: (hf : MDiff[s] f) (hg : MDiff[r] g)
  证明: (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

Depends on / 依赖: hf.comp, hg.comp, mdifferentiableOn_fst, mdifferentiableOn_snd, prodMk, prod_subset_preimage_fst, prod_subset_preimage_snd
-/
theorem MDifferentiableOn.prodMap (hf : MDiff[s] f) (hg : MDiff[r] g) :
    MDiff[s ×ˢ r] (Prod.map f g) :=
(hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

/--
theorem `MDifferentiable.prodMap` / 定理 `MDifferentiable.prodMap`

English:
theorem MDifferentiable.prodMap
  given: (hf : MDiff f) (hg : MDiff g)
  statement: MDiff (Prod.map f g)
  proof: fun p =>
  (hf p.1).prodMap' (hg p.2)

中文:
定理 MDifferentiable.prodMap
  条件: (hf : MDiff f) (hg : MDiff g)
  结论: MDiff (Prod.map f g)
  证明: fun p =>
  (hf p.1).prodMap' (hg p.2)
-/
theorem MDifferentiable.prodMap (hf : MDiff f) (hg : MDiff g) : MDiff (Prod.map f g) := fun p =>
  (hf p.1).prodMap' (hg p.2)

/--
lemma `HasMFDerivWithinAt.prodMap` / 引理 `HasMFDerivWithinAt.prodMap`

English:
lemma HasMFDerivWithinAt.prodMap
  statement: {s : Set <| M × M'} {p : M × M'} {f : M -> N} {g : M' -> N'}
  proof: by
.mono (by grind), ?_⟩ refine ⟨hf.1.prodMap hg.1
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s inter range ↑(I.prod I')) subseteq
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) inter range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) inter range I') := by
    simp only 

中文:
引理 HasMFDerivWithinAt.prodMap
  结论: {s : Set <| M × M'} {p : M × M'} {f : M -> N} {g : M' -> N'}
  证明: by
.mono (by grind), ?_⟩ refine ⟨hf.1.prodMap hg.1
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s inter range ↑(I.prod I')) subseteq
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) inter range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) inter range I') := by
    simp only 

Depends on / 依赖: I.prod, I.toPartialEquiv.prod_symm, Prod.fst, Prod.snd, better, chartAt, extChartAt, mfld_simps, prodMap, prod_symm, range_prodMap, subseteq, toPartialEquiv, toPartialEquiv.prod_symm
-/
lemma HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M -> N} {g : M' -> N'}
    {df : TangentSpace% p.1 ->L[𝕜] TangentSpace% (f p.1)}
    (hf : HasMFDerivAt[Prod.fst '' s] f p.1 df)
    {dg : TangentSpace% p.2 ->L[𝕜] TangentSpace% (g p.2)}
    (hg : HasMFDerivAt[Prod.snd '' s] g p.2 dg) :
    HasMFDerivAt[s] (Prod.map f g) p (df.prodMap dg) := by
.mono (by grind), ?_⟩ refine ⟨hf.1.prodMap hg.1
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s inter range ↑(I.prod I')) subseteq
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) inter range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) inter range I') := by
    simp only [mfld_simps]
    rw [range_prodMap]; rw [I.toPartialEquiv.prod_symm]; rw [(chartAt H p.1).toPartialEquiv.prod_symm]
    intro p₀ ⟨hp₀, ⟨hp₁₁, hp₁₂⟩⟩
    exact ⟨⟨by simp_all; grind, by assumption⟩, ⟨by simp_all; grind, by assumption⟩⟩
  rw [writtenInExtChartAt_prod]
  apply HasFDerivWithinAt.mono ?_ better
  apply HasFDerivWithinAt.prodMap
  exacts [hf.2.mono (fst_image_prod_subset ..), hg.2.mono (snd_image_prod_subset ..)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasMFDerivAt.prodMap` / 引理 `HasMFDerivAt.prodMap`

English:
lemma HasMFDerivAt.prodMap
  statement: {p : M × M'} {f : M -> N} {g : M' -> N'}
  proof: by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

中文:
引理 HasMFDerivAt.prodMap
  结论: {p : M × M'} {f : M -> N} {g : M' -> N'}
  证明: by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

Depends on / 依赖: convert, hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hf.hasMFDerivWithinAt.prodMap, hf.mfderiv, hg.hasMFDerivWithinAt, hg.mfderiv, mfderiv, mfderivWithin_univ, prodMap, simp_rw, univ_prod_univ
-/
lemma HasMFDerivAt.prodMap {p : M × M'} {f : M -> N} {g : M' -> N'}
    {df : TangentSpace% p.1 ->L[𝕜] TangentSpace% (f p.1)} (hf : HasMFDerivAt% f p.1 df)
    {dg : TangentSpace% p.2 ->L[𝕜] TangentSpace% (g p.2)} (hg : HasMFDerivAt% g p.2 dg) :
    HasMFDerivAt% (Prod.map f g) p
      ((mfderiv% f p.1).prodMap (mfderiv% g p.2)) := by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

-- Note: this lemma does not apply easily to an arbitrary subset `s ⊆ M × M'` as
-- unique differentiability on `(Prod.fst '' s)` and `(Prod.snd '' s)` does not imply
-- unique differentiability on `s`: a priori, `(Prod.fst '' s) × (Prod.fst '' s)`
-- could be a strict superset of `s`.
/--
lemma `mfderivWithin_prodMap` / 引理 `mfderivWithin_prodMap`

English:
lemma mfderivWithin_prodMap
  statement: {p : M × M'} {t : Set M'} {f : M -> N} {g : M' -> N'}
  proof: by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

中文:
引理 mfderivWithin_prodMap
  结论: {p : M × M'} {t : Set M'} {f : M -> N} {g : M' -> N'}
  证明: by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

Depends on / 依赖: HasMFDerivAt, Prod.fst, Prod.snd, hasMFDerivWithinAt, hf.hasMFDerivWithinAt.mono, hg.hasMFDerivWithinAt.mono, hs.prod, mfderiv, mfderivWithin, prodMap
-/
lemma mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M -> N} {g : M' -> N'}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2)
    (hs : UniqueMDiffAt[s] p.1) (ht : UniqueMDiffAt[t] p.2) :
    mfderiv[s ×ˢ t] (Prod.map f g) p = (mfderiv[s] f p.1).prodMap (mfderiv[t] g p.2) := by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

/--
lemma `mfderiv_prodMap` / 引理 `mfderiv_prodMap`

English:
lemma mfderiv_prodMap
  statement: {p : M × M'} {f : M -> N} {g : M' -> N'}
  proof: by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

中文:
引理 mfderiv_prodMap
  结论: {p : M × M'} {f : M -> N} {g : M' -> N'}
  证明: by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

Depends on / 依赖: hf.mdifferentiableWithinAt, hg.mdifferentiableWithinAt, mdifferentiableWithinAt, mfderivWithin_prodMap, mfderivWithin_univ, simp_rw, uniqueMDiffWithinAt_univ, univ_prod_univ
-/
lemma mfderiv_prodMap {p : M × M'} {f : M -> N} {g : M' -> N'}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) :
    mfderiv% (Prod.map f g) p = (mfderiv% f p.1).prodMap (mfderiv% g p.2) := by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

end prodMap

@[simp, mfld_simps]
/--
theorem `tangentMap_prodSnd` / 定理 `tangentMap_prodSnd`

English:
theorem tangentMap_prodSnd
  given: {p : TangentBundle (I.prod I') (M × M')}
  proof: by
  simp [tangentMap]; rfl

中文:
定理 tangentMap_prodSnd
  条件: {p : TangentBundle (I.prod I') (M × M')}
  证明: by
  simp [tangentMap]; rfl

Depends on / 依赖: tangentMap
-/
theorem tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp [tangentMap]; rfl

/--
theorem `tangentMapWithin_prodSnd` / 定理 `tangentMapWithin_prodSnd`

English:
theorem tangentMapWithin_prodSnd
  statement: {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
  proof: by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

中文:
定理 tangentMapWithin_prodSnd
  结论: {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
  证明: by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

Depends on / 依赖: mfderivWithin_snd, tangentMapWithin
-/
theorem tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

-- Kept as an alias for discoverability.
alias MDifferentiableAt.mfderiv_prod := mfderiv_prodMk

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mfderiv_prod_left` / 定理 `mfderiv_prod_left`

English:
theorem mfderiv_prod_left
  given: {x₀ : M} {y₀ : M'}
  proof: by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inl]

中文:
定理 mfderiv_prod_left
  条件: {x₀ : M} {y₀ : M'}
  证明: by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inl]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inl, mdifferentiableAt_const, mdifferentiableAt_id, mdifferentiableAt_id.mfderiv_prod, mfderiv_const, mfderiv_id, mfderiv_prod
-/
theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (x : M) => (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inl]

-- TODO: better error when the type of x is left open
/--
theorem `tangentMap_prod_left` / 定理 `tangentMap_prod_left`

English:
theorem tangentMap_prod_left
  given: {p : TangentBundle I M} {y₀ : M'}
  proof: by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

中文:
定理 tangentMap_prod_left
  条件: {p : TangentBundle I M} {y₀ : M'}
  证明: by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

Depends on / 依赖: mfderiv_prod_left, tangentMap
-/
theorem tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} :
    tangentMap% (fun (x : M) => (x, y₀)) p = ⟨(p.1, y₀), (p.2, 0)⟩ := by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mfderiv_prod_right` / 定理 `mfderiv_prod_right`

English:
theorem mfderiv_prod_right
  given: {x₀ : M} {y₀ : M'}
  proof: by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inr]

中文:
定理 mfderiv_prod_right
  条件: {x₀ : M} {y₀ : M'}
  证明: by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inr]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.inr, mdifferentiableAt_const, mdifferentiableAt_const.mfderiv_prod, mdifferentiableAt_id, mfderiv_const, mfderiv_id, mfderiv_prod
-/
theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (y : M') => (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id]; rw [mfderiv_const]; rw [ContinuousLinearMap.inr]

/--
theorem `tangentMap_prod_right` / 定理 `tangentMap_prod_right`

English:
theorem tangentMap_prod_right
  given: {p : TangentBundle I' M'} {x₀ : M}
  proof: by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

中文:
定理 tangentMap_prod_right
  条件: {p : TangentBundle I' M'} {x₀ : M}
  证明: by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

Depends on / 依赖: mfderiv_prod_right, tangentMap
-/
theorem tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} :
    tangentMap% (fun (y : M') => (x₀, y)) p = ⟨(x₀, p.1), (0, p.2)⟩ := by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

/--
theorem `mfderiv_prod_eq_add` / 定理 `mfderiv_prod_eq_add`

English:
theorem mfderiv_prod_eq_add
  statement: {f : M × M' -> M''} {p : M × M'}
  proof: by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_

中文:
定理 mfderiv_prod_eq_add
  结论: {f : M × M' -> M''} {p : M × M'}
  证明: by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id, ContinuousLinearMap.coprod_inl_inr, comp_add, comp_id, convert, coprod_inl_inr, mdifferentiableAt_const, mdifferentiableAt_const.mfderiv_prod, mdifferentiableAt_const.prodMk, mdifferentiableAt_fst, mdifferentiableAt_fst.mfderiv_prod, mdifferentiableAt_fst.prodMk, mdifferentiableAt_snd, mfderiv, mfderiv_comp_of_eq, mfderiv_const, mfderiv_fst, mfderiv_prod
-/
theorem mfderiv_prod_eq_add {f : M × M' -> M''} {p : M × M'}
    (hf : MDiffAt f p) :
    mfderiv% f p =
        mfderiv% (fun z : M × M' => f (z.1, p.2)) p +
        mfderiv% (fun z : M × M' => f (p.1, z.2)) p := by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_snd, mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
convert! ContinuousLinearMap.comp_id mfderiv% f (p.1, p.2)
  exact ContinuousLinearMap.coprod_inl_inr

/--
theorem `mfderiv_prod_eq_add_comp` / 定理 `mfderiv_prod_eq_add_comp`

English:
theorem mfderiv_prod_eq_add_comp
  given: {f : M × M' -> M''} {p : M × M'} (hf : MDiffAt f p)
  proof: by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' => f (z.1, p.2)) = (fun z : M => f (z, p.2)) ∘ Prod.fst := rfl
    rw [this]; rw [mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exac

中文:
定理 mfderiv_prod_eq_add_comp
  条件: {f : M × M' -> M''} {p : M × M'} (hf : MDiffAt f p)
  证明: by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' => f (z.1, p.2)) = (fun z : M => f (z, p.2)) ∘ Prod.fst := rfl
    rw [this]; rw [mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exac

Depends on / 依赖: Prod.fst, Prod.snd, hf.comp, mdifferentiableAt_const, mdifferentiableAt_const.pr, mdifferentiableAt_fst, mdifferentiableAt_id, mdifferentiableAt_id.prodMk, mfderiv_comp, mfderiv_fst, mfderiv_prod_eq_add, mfderiv_snd, prodMk
-/
theorem mfderiv_prod_eq_add_comp {f : M × M' -> M''} {p : M × M'} (hf : MDiffAt f p) :
    mfderiv% f p =
        (mfderiv% (fun z : M => f (z, p.2)) p.1) ∘L (id (ContinuousLinearMap.fst 𝕜 E E') :
          (TangentSpace% p) ->L[𝕜] (TangentSpace% p.1)) +
        (mfderiv% (fun z : M' => f (p.1, z)) p.2) ∘L (id (ContinuousLinearMap.snd 𝕜 E E') :
          (TangentSpace% p) ->L[𝕜] (TangentSpace% p.2)) := by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' => f (z.1, p.2)) = (fun z : M => f (z, p.2)) ∘ Prod.fst := rfl
    rw [this]; rw [mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exact mdifferentiableAt_fst
  · have : (fun z : M × M' => f (p.1, z.2)) = (fun z : M' => f (p.1, z)) ∘ Prod.snd := rfl
    rw [this]; rw [mfderiv_comp (I' := I')]
    · simp only [mfderiv_snd]
      rfl
    · exact hf.comp _ (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    · exact mdifferentiableAt_snd

/--
theorem `mfderiv_prod_eq_add_apply` / 定理 `mfderiv_prod_eq_add_apply`

English:
theorem mfderiv_prod_eq_add_apply
  statement: {f : M × M' -> M''} {p : M × M'} {v : TangentSpace% p}
  proof: by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

中文:
定理 mfderiv_prod_eq_add_apply
  结论: {f : M × M' -> M''} {p : M × M'} {v : TangentSpace% p}
  证明: by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

Depends on / 依赖: mfderiv_prod_eq_add_comp
-/
theorem mfderiv_prod_eq_add_apply {f : M × M' -> M''} {p : M × M'} {v : TangentSpace% p}
    (hf : MDiffAt f p) :
    mfderiv% f p v =
      mfderiv% (fun z : M => f (z, p.2)) p.1 v.1 + mfderiv% (fun z : M' => f (p.1, z)) p.2 v.2 := by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

end Prod

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {p : M oplus M'}

/--
lemma `writtenInExtChartAt_sumSwap_eventuallyEq_id` / 引理 `writtenInExtChartAt_sumSwap_eventuallyEq_id`

English:
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id
  proof: by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target inter range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_in

中文:
引理 writtenInExtChartAt_sumSwap_eventuallyEq_id
  证明: by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target inter range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_in

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr, Filter, Filter.eventually_of_mem, Filter.inter_mem_iff, I.continuousWithinAt_symm, I.right_inv, I.symm, Sum.inl, Sum.inr_injective.extend_apply, Sum.swap, Sum.swap_inl, chartAt, continuousWithinAt_symm, eventually_of_mem, extChartAt, extend_apply, inr_injective, inter_mem_iff
-/
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id :
    writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id := by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target inter range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inr_injective.extend_apply]; rw [(chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
    | inr x =>
      let t := I.symm ⁻¹' (chartAt H x).target inter range I
      have : EqOn (writtenInExtChartAt I I (Sum.inr x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inr,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inl_injective.extend_apply]; rw [(chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)

/--
theorem `hasMFDerivAt_sumSwap` / 定理 `hasMFDerivAt_sumSwap`

English:
theorem hasMFDerivAt_sumSwap
  proof: by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]

中文:
定理 hasMFDerivAt_sumSwap
  证明: by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]

Depends on / 依赖: congr_of_eventuallyEq, fun_prop, hasFDerivWithinAt_id, mfld_simps, writtenInExtChartAt_sumSwap_eventuallyEq_id
-/
theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt% (@Sum.swap M M') p (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]
/--
theorem `mfderivWithin_sumSwap` / 定理 `mfderivWithin_sumSwap`

English:
theorem mfderivWithin_sumSwap
  given: {s : Set (M oplus M')} (hs : UniqueMDiffAt[s] p)
  proof: hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]

中文:
定理 mfderivWithin_sumSwap
  条件: {s : Set (M oplus M')} (hs : UniqueMDiffAt[s] p)
  证明: hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]

Depends on / 依赖: hasMFDerivAt_sumSwap, hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin, hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_sumSwap {s : Set (M oplus M')} (hs : UniqueMDiffAt[s] p) :
    mfderiv[s] (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]
/--
theorem `mfderiv_sumSwap` / 定理 `mfderiv_sumSwap`

English:
theorem mfderiv_sumSwap
  proof: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

中文:
定理 mfderiv_sumSwap
  证明: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

Depends on / 依赖: mfderivWithin_sumSwap, mfderivWithin_univ, uniqueMDiffWithinAt_univ
-/
theorem mfderiv_sumSwap :
    mfderiv% (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

variable {f : M -> N} (g : M' -> N') {q : M} {q' : M'}

/--
lemma `writtenInExtChartAt_sumInl_eventuallyEq_id` / 引理 `writtenInExtChartAt_sumInl_eventuallyEq_id`

English:
lemma writtenInExtChartAt_sumInl_eventuallyEq_id
  proof: by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target inter Set.range I in 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩

中文:
引理 writtenInExtChartAt_sumInl_eventuallyEq_id
  证明: by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target inter Set.range I in 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inl, I.image_eq, I.left_inv, I.symm, Set.mem_preimage, Set.range, Sum.inl_injective.extend_apply, chartAt, extChartAt, extend_apply, extend_image_target_mem_nhds, filter_upwards, image_eq, inl_injective, left_inv, mem_chart_source, mem_preimage, right_inv, sum_chartAt_inl
-/
lemma writtenInExtChartAt_sumInl_eventuallyEq_id :
    (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target inter Set.range I in 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inl,
Sum.inl_injective.extend_apply chartAt H q,
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

/--
lemma `writtenInExtChartAt_sumInr_eventuallyEq_id` / 引理 `writtenInExtChartAt_sumInr_eventuallyEq_id`

English:
lemma writtenInExtChartAt_sumInr_eventuallyEq_id
  proof: by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target inter Set.range I in 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z

中文:
引理 writtenInExtChartAt_sumInr_eventuallyEq_id
  证明: by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target inter Set.range I in 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z

Depends on / 依赖: ChartedSpace, ChartedSpace.sum_chartAt_inr, I.image_eq, I.left_inv, I.symm, Set.mem_preimage, Set.range, Sum.inr_injective.extend_apply, chartAt, extChartAt, extend_apply, extend_image_target_mem_nhds, filter_upwards, image_eq, inr_injective, left_inv, mem_chart_source, mem_preimage, right_inv, sum_chartAt_inr
-/
lemma writtenInExtChartAt_sumInr_eventuallyEq_id :
    (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target inter Set.range I in 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inr,
Sum.inr_injective.extend_apply chartAt H q',
    (chartAt H q').right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

/--
theorem `hasMFDerivWithinAt_inl` / 定理 `hasMFDerivWithinAt_inl`

English:
theorem hasMFDerivWithinAt_inl
  proof: by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s inter Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id (ext

中文:
定理 hasMFDerivWithinAt_inl
  证明: by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s inter Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id (ext

Depends on / 依赖: Set.range, Sum.inl, congr_of_eventuallyEq, extChartAt, filter_mono, fun_prop, hasFDerivWithinAt_id, nhdsWithin_mono, writtenInExtChartAt, writtenInExtChartAt_sumInl_eventuallyEq_id, writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono
-/
theorem hasMFDerivWithinAt_inl :
    HasMFDerivAt[s] (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% q)) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s inter Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q q) _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivAt_inl` / 定理 `hasMFDerivAt_inl`

English:
theorem hasMFDerivAt_inl
  proof: by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)

中文:
定理 hasMFDerivAt_inl
  证明: by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)

Depends on / 依赖: HasMFDerivAt, Set.univ, hasMFDerivWithinAt_inl, hasMFDerivWithinAt_univ
-/
theorem hasMFDerivAt_inl :
    HasMFDerivAt% (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)

/--
theorem `hasMFDerivWithinAt_inr` / 定理 `hasMFDerivWithinAt_inr`

English:
theorem hasMFDerivWithinAt_inr
  given: {t : Set M'}
  proof: by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t inter Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id 

中文:
定理 hasMFDerivWithinAt_inr
  条件: {t : Set M'}
  证明: by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t inter Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id 

Depends on / 依赖: Set.range, Sum.inr, congr_of_eventuallyEq, extChartAt, filter_mono, fun_prop, hasFDerivWithinAt_id, nhdsWithin_mono, writtenInExtChartAt, writtenInExtChartAt_sumInr_eventuallyEq_id, writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono
-/
theorem hasMFDerivWithinAt_inr {t : Set M'} :
    HasMFDerivAt[t] (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% q')) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t inter Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy => hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q' q') _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivAt_inr` / 定理 `hasMFDerivAt_inr`

English:
theorem hasMFDerivAt_inr
  proof: by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)

中文:
定理 hasMFDerivAt_inr
  证明: by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)

Depends on / 依赖: HasMFDerivAt, Set.univ, hasMFDerivWithinAt_inr, hasMFDerivWithinAt_univ
-/
theorem hasMFDerivAt_inr :
    HasMFDerivAt% (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)

/--
theorem `mfderivWithin_sumInl` / 定理 `mfderivWithin_sumInl`

English:
theorem mfderivWithin_sumInl
  given: (hU : UniqueMDiffAt[s] q)
  proof: hasMFDerivWithinAt_inl.mfderivWithin hU

中文:
定理 mfderivWithin_sumInl
  条件: (hU : UniqueMDiffAt[s] q)
  证明: hasMFDerivWithinAt_inl.mfderivWithin hU

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, hasMFDerivWithinAt_inl, hasMFDerivWithinAt_inl.mfderivWithin, mfderivWithin, toIntLinearEquiv
-/
theorem mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) :
    mfderiv[s] (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivWithinAt_inl.mfderivWithin hU

/--
theorem `mfderiv_sumInl` / 定理 `mfderiv_sumInl`

English:
theorem mfderiv_sumInl
  proof: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

中文:
定理 mfderiv_sumInl
  证明: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

Depends on / 依赖: mfderivWithin_sumInl, mfderivWithin_univ, uniqueMDiffWithinAt_univ
-/
theorem mfderiv_sumInl :
    mfderiv% (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

/--
theorem `mfderivWithin_sumInr` / 定理 `mfderivWithin_sumInr`

English:
theorem mfderivWithin_sumInr
  given: {t : Set M'} (hU : UniqueMDiffAt[t] q')
  proof: hasMFDerivWithinAt_inr.mfderivWithin hU

中文:
定理 mfderivWithin_sumInr
  条件: {t : Set M'} (hU : UniqueMDiffAt[t] q')
  证明: hasMFDerivWithinAt_inr.mfderivWithin hU

Depends on / 依赖: hasMFDerivWithinAt_inr, hasMFDerivWithinAt_inr.mfderivWithin, mfderivWithin
-/
theorem mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffAt[t] q') :
    mfderiv[t] (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') :=
  hasMFDerivWithinAt_inr.mfderivWithin hU

/--
theorem `mfderiv_sumInr` / 定理 `mfderiv_sumInr`

English:
theorem mfderiv_sumInr
  proof: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

中文:
定理 mfderiv_sumInr
  证明: by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

Depends on / 依赖: mfderivWithin_sumInr, mfderivWithin_univ, uniqueMDiffWithinAt_univ
-/
theorem mfderiv_sumInr :
    mfderiv% (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

end disjointUnion

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
-/

section Group

variable {z : M} {f g : M -> E'} {f' g' : TangentSpace% z ->L[𝕜] E'}

/--
theorem `HasMFDerivWithinAt.add` / 定理 `HasMFDerivWithinAt.add`

English:
theorem HasMFDerivWithinAt.add
  statement: {s : Set M}
  proof: ⟨hf.1.add hg.1, hf.2.add hg.2⟩

中文:
定理 HasMFDerivWithinAt.add
  结论: {s : Set M}
  证明: ⟨hf.1.add hg.1, hf.2.add hg.2⟩
-/
theorem HasMFDerivWithinAt.add {s : Set M}
    (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/--
theorem `HasMFDerivAt.add` / 定理 `HasMFDerivAt.add`

English:
theorem HasMFDerivAt.add
  given: (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g')
  proof: ⟨hf.1.add hg.1, hf.2.add hg.2⟩

中文:
定理 HasMFDerivAt.add
  条件: (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g')
  证明: ⟨hf.1.add hg.1, hf.2.add hg.2⟩
-/
theorem HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

/--
theorem `MDifferentiableWithinAt.add` / 定理 `MDifferentiableWithinAt.add`

English:
theorem MDifferentiableWithinAt.add
  given: {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  proof: (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.add
  条件: {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  证明: (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.add, hg.hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f + g) z :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt

/--
theorem `MDifferentiableAt.add` / 定理 `MDifferentiableAt.add`

English:
theorem MDifferentiableAt.add
  given: (hf : MDiffAt f z) (hg : MDiffAt g z)
  statement: MDiffAt (f + g) z
  proof: (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

中文:
定理 MDifferentiableAt.add
  条件: (hf : MDiffAt f z) (hg : MDiffAt g z)
  结论: MDiffAt (f + g) z
  证明: (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt.add, hg.hasMFDerivAt, mdifferentiableAt
-/
theorem MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

/--
theorem `MDifferentiableOn.add` / 定理 `MDifferentiableOn.add`

English:
theorem MDifferentiableOn.add
  given: {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g)
  statement: MDiff[s] (f + g)
  proof: fun x hx => (hf x hx).add (hg x hx)

中文:
定理 MDifferentiableOn.add
  条件: {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g)
  结论: MDiff[s] (f + g)
  证明: fun x hx => (hf x hx).add (hg x hx)
-/
theorem MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f + g) :=
  fun x hx => (hf x hx).add (hg x hx)

/--
theorem `MDifferentiable.add` / 定理 `MDifferentiable.add`

English:
theorem MDifferentiable.add
  given: (hf : MDiff f) (hg : MDiff g)
  statement: MDiff (f + g)
  proof: fun x => (hf x).add (hg x)

中文:
定理 MDifferentiable.add
  条件: (hf : MDiff f) (hg : MDiff g)
  结论: MDiff (f + g)
  证明: fun x => (hf x).add (hg x)
-/
theorem MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
  fun x => (hf x).add (hg x)

-- TODO: this lemma (and others below) uses the identification of tangent spaces silently
-- Deprecate all these lemmas in favour of a version using `mvfderiv(Within)`
-- Porting note: forcing types using `by exact`
/--
theorem `mfderiv_add` / 定理 `mfderiv_add`

English:
theorem mfderiv_add
  given: (hf : MDiffAt f z) (hg : MDiffAt g z)
  proof: (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

中文:
定理 mfderiv_add
  条件: (hf : MDiffAt f z) (hg : MDiffAt g z)
  证明: (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt.add, hg.hasMFDerivAt, mfderiv
-/
theorem mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f + g) z : TangentSpace% z ->L[𝕜] E') =
      (by exact mfderiv% f z) + (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

/--
theorem `mfderivWithin_add` / 定理 `mfderivWithin_add`

English:
theorem mfderivWithin_add
  statement: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  proof: (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

中文:
定理 mfderivWithin_add
  结论: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  证明: (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.add, hg.hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f + g) z : TangentSpace% z ->L[𝕜] E') =
      (by exact mfderiv[s] f z) + (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

section sum
variable {ι : Type} {t : Finset ι} {f : ι -> M -> E'} {f' : ι -> TangentSpace% z ->L[𝕜] E'}

/--
lemma `HasMFDerivWithinAt.sum` / 引理 `HasMFDerivWithinAt.sum`

English:
lemma HasMFDerivWithinAt.sum
  given: (hf : forall i in t, HasMFDerivAt[s] (f i) z (f' i))
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

中文:
引理 HasMFDerivWithinAt.sum
  条件: (hf : 对任意 i in t, HasMFDerivAt[s] (f i) z (f' i))
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

Depends on / 依赖: Finset, Finset.induction_on, HasMFDerivWithinAt, HasMFDerivWithinAt.add, IsTorsionFree, classical, hasMFDerivWithinAt_const, induction_on, insert, instIsTorsionFree
-/
lemma HasMFDerivWithinAt.sum (hf : forall i in t, HasMFDerivAt[s] (f i) z (f' i)) :
    HasMFDerivAt[s] (∑ i in t, f i) z (∑ i in t, f' i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasMFDerivAt.sum` / 引理 `HasMFDerivAt.sum`

English:
lemma HasMFDerivAt.sum
  given: (hf : forall i in t, HasMFDerivAt% (f i) z (f' i))
  proof: by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

中文:
引理 HasMFDerivAt.sum
  条件: (hf : 对任意 i in t, HasMFDerivAt% (f i) z (f' i))
  证明: by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.sum, hasMFDerivWithinAt_univ
-/
lemma HasMFDerivAt.sum (hf : forall i in t, HasMFDerivAt% (f i) z (f' i)) :
    HasMFDerivAt% (∑ i in t, f i) z (∑ i in t, f' i) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

/--
lemma `MDifferentiableWithinAt.sum` / 引理 `MDifferentiableWithinAt.sum`

English:
lemma MDifferentiableWithinAt.sum
  proof: (HasMFDerivWithinAt.sum fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

中文:
引理 MDifferentiableWithinAt.sum
  证明: (HasMFDerivWithinAt.sum fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.sum, hasMFDerivWithinAt, mdifferentiableWithinAt
-/
lemma MDifferentiableWithinAt.sum
    (hf : forall i in t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i in t, f i) z :=
  (HasMFDerivWithinAt.sum fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

/--
lemma `MDifferentiableAt.sum` / 引理 `MDifferentiableAt.sum`

English:
lemma MDifferentiableAt.sum
  given: (hf : forall i in t, MDiffAt (f i) z)
  statement: MDiffAt (∑ i in t, f i) z
  proof: by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

中文:
引理 MDifferentiableAt.sum
  条件: (hf : 对任意 i in t, MDiffAt (f i) z)
  结论: MDiffAt (∑ i in t, f i) z
  证明: by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

Depends on / 依赖: mdifferentiableWithinAt_univ
-/
lemma MDifferentiableAt.sum (hf : forall i in t, MDiffAt (f i) z) : MDiffAt (∑ i in t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

/--
lemma `MDifferentiableOn.sum` / 引理 `MDifferentiableOn.sum`

English:
lemma MDifferentiableOn.sum
  given: (hf : forall i in t, MDiff[s] (f i))
  statement: MDiff[s] (∑ i in t, f i)
  proof: fun z hz => .sum fun i hi => hf i hi z hz

中文:
引理 MDifferentiableOn.sum
  条件: (hf : 对任意 i in t, MDiff[s] (f i))
  结论: MDiff[s] (∑ i in t, f i)
  证明: fun z hz => .sum fun i hi => hf i hi z hz
-/
lemma MDifferentiableOn.sum (hf : forall i in t, MDiff[s] (f i)) : MDiff[s] (∑ i in t, f i) :=
  fun z hz => .sum fun i hi => hf i hi z hz

/--
lemma `MDifferentiable.sum` / 引理 `MDifferentiable.sum`

English:
lemma MDifferentiable.sum
  given: (hf : forall i in t, MDiff (f i))
  statement: MDiff (∑ i in t, f i)
  proof: fun z => .sum fun i hi => hf i hi z

中文:
引理 MDifferentiable.sum
  条件: (hf : 对任意 i in t, MDiff (f i))
  结论: MDiff (∑ i in t, f i)
  证明: fun z => .sum fun i hi => hf i hi z
-/
lemma MDifferentiable.sum (hf : forall i in t, MDiff (f i)) : MDiff (∑ i in t, f i) :=
  fun z => .sum fun i hi => hf i hi z

end sum

/--
theorem `HasMFDerivWithinAt.const_smul` / 定理 `HasMFDerivWithinAt.const_smul`

English:
theorem HasMFDerivWithinAt.const_smul
  given: (hf : HasMFDerivAt[s] f z f') (a : 𝕜)
  proof: ⟨hf.1.const_smul a, hf.2.const_smul a⟩

中文:
定理 HasMFDerivWithinAt.const_smul
  条件: (hf : HasMFDerivAt[s] f z f') (a : 𝕜)
  证明: ⟨hf.1.const_smul a, hf.2.const_smul a⟩

Depends on / 依赖: const_smul
-/
theorem HasMFDerivWithinAt.const_smul (hf : HasMFDerivAt[s] f z f') (a : 𝕜) :
    HasMFDerivAt[s] (a • f) z (a • f') :=
  ⟨hf.1.const_smul a, hf.2.const_smul a⟩

/--
theorem `HasMFDerivAt.const_smul` / 定理 `HasMFDerivAt.const_smul`

English:
theorem HasMFDerivAt.const_smul
  given: (hf : HasMFDerivAt% f z f') (s : 𝕜)
  proof: ⟨hf.1.const_smul s, hf.2.const_smul s⟩

中文:
定理 HasMFDerivAt.const_smul
  条件: (hf : HasMFDerivAt% f z f') (s : 𝕜)
  证明: ⟨hf.1.const_smul s, hf.2.const_smul s⟩

Depends on / 依赖: const_smul
-/
theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z f') (s : 𝕜) :
    HasMFDerivAt% (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩

/--
theorem `MDifferentiableWithinAt.const_smul` / 定理 `MDifferentiableWithinAt.const_smul`

English:
theorem MDifferentiableWithinAt.const_smul
  given: (hf : MDiffAt[s] f z) (a : 𝕜)
  statement: MDiffAt[s] (a • f) z
  proof: (hf.hasMFDerivWithinAt.const_smul a).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.const_smul
  条件: (hf : MDiffAt[s] f z) (a : 𝕜)
  结论: MDiffAt[s] (a • f) z
  证明: (hf.hasMFDerivWithinAt.const_smul a).mdifferentiableWithinAt

Depends on / 依赖: const_smul, hasMFDerivWithinAt, hf.hasMFDerivWithinAt.const_smul, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.const_smul (hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt[s] (a • f) z :=
  (hf.hasMFDerivWithinAt.const_smul a).mdifferentiableWithinAt

/--
theorem `MDifferentiableAt.const_smul` / 定理 `MDifferentiableAt.const_smul`

English:
theorem MDifferentiableAt.const_smul
  given: (hf : MDiffAt f z) (s : 𝕜)
  statement: MDiffAt (s • f) z
  proof: (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

中文:
定理 MDifferentiableAt.const_smul
  条件: (hf : MDiffAt f z) (s : 𝕜)
  结论: MDiffAt (s • f) z
  证明: (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

Depends on / 依赖: const_smul, hasMFDerivAt, hf.hasMFDerivAt.const_smul, mdifferentiableAt
-/
theorem MDifferentiableAt.const_smul (hf : MDiffAt f z) (s : 𝕜) : MDiffAt (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

/--
theorem `MDifferentiableOn.const_smul` / 定理 `MDifferentiableOn.const_smul`

English:
theorem MDifferentiableOn.const_smul
  given: (a : 𝕜) (hf : MDiff[s] f)
  statement: MDiff[s] (a • f)
  proof: fun x hx => (hf x hx).const_smul a

中文:
定理 MDifferentiableOn.const_smul
  条件: (a : 𝕜) (hf : MDiff[s] f)
  结论: MDiff[s] (a • f)
  证明: fun x hx => (hf x hx).const_smul a

Depends on / 依赖: Module, Module.Free, Subsingleton, const_smul, of_subsingleton
-/
theorem MDifferentiableOn.const_smul (a : 𝕜) (hf : MDiff[s] f) : MDiff[s] (a • f) :=
  fun x hx => (hf x hx).const_smul a

/--
theorem `MDifferentiable.const_smul` / 定理 `MDifferentiable.const_smul`

English:
theorem MDifferentiable.const_smul
  given: (s : 𝕜) (hf : MDiff f)
  statement: MDiff (s • f)
  proof: fun x => (hf x).const_smul s

中文:
定理 MDifferentiable.const_smul
  条件: (s : 𝕜) (hf : MDiff f)
  结论: MDiff (s • f)
  证明: fun x => (hf x).const_smul s

Depends on / 依赖: const_smul
-/
theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDiff f) : MDiff (s • f) :=
  fun x => (hf x).const_smul s

/--
theorem `const_smul_mfderiv` / 定理 `const_smul_mfderiv`

English:
theorem const_smul_mfderiv
  given: (hf : MDiffAt f z) (s : 𝕜)
  statement: mfderiv% (s • f) z = s • mfderiv% f z
  proof: (hf.hasMFDerivAt.const_smul s).mfderiv

中文:
定理 const_smul_mfderiv
  条件: (hf : MDiffAt f z) (s : 𝕜)
  结论: mfderiv% (s • f) z = s • mfderiv% f z
  证明: (hf.hasMFDerivAt.const_smul s).mfderiv

Depends on / 依赖: const_smul, hasMFDerivAt, hf.hasMFDerivAt.const_smul, mfderiv
-/
theorem const_smul_mfderiv (hf : MDiffAt f z) (s : 𝕜) : mfderiv% (s • f) z = s • mfderiv% f z :=
  (hf.hasMFDerivAt.const_smul s).mfderiv

/--
theorem `HasMFDerivWithinAt.neg` / 定理 `HasMFDerivWithinAt.neg`

English:
theorem HasMFDerivWithinAt.neg
  given: {s : Set M} (hf : HasMFDerivAt[s] f z f')
  proof: ⟨hf.1.neg, hf.2.neg⟩

中文:
定理 HasMFDerivWithinAt.neg
  条件: {s : Set M} (hf : HasMFDerivAt[s] f z f')
  证明: ⟨hf.1.neg, hf.2.neg⟩
-/
theorem HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivAt[s] f z f') :
    HasMFDerivAt[s] (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

/--
theorem `HasMFDerivAt.neg` / 定理 `HasMFDerivAt.neg`

English:
theorem HasMFDerivAt.neg
  given: (hf : HasMFDerivAt% f z f')
  statement: HasMFDerivAt% (-f) z (-f')
  proof: ⟨hf.1.neg, hf.2.neg⟩

中文:
定理 HasMFDerivAt.neg
  条件: (hf : HasMFDerivAt% f z f')
  结论: HasMFDerivAt% (-f) z (-f')
  证明: ⟨hf.1.neg, hf.2.neg⟩
-/
theorem HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDerivAt% (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivAt_neg` / 定理 `hasMFDerivAt_neg`

English:
theorem hasMFDerivAt_neg
  statement: HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f'
  proof: ⟨fun hf => by convert! hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩

中文:
定理 hasMFDerivAt_neg
  结论: HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f'
  证明: ⟨fun hf => by convert! hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩

Depends on / 依赖: convert, hf.neg, neg_neg
-/
theorem hasMFDerivAt_neg : HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f' :=
  ⟨fun hf => by convert! hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩

/--
theorem `MDifferentiableWithinAt.neg` / 定理 `MDifferentiableWithinAt.neg`

English:
theorem MDifferentiableWithinAt.neg
  given: {s : Set M} (hf : MDiffAt[s] f z)
  statement: MDiffAt[s] (-f) z
  proof: (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.neg
  条件: {s : Set M} (hf : MDiffAt[s] f z)
  结论: MDiffAt[s] (-f) z
  证明: (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.neg, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.neg {s : Set M} (hf : MDiffAt[s] f z) : MDiffAt[s] (-f) z :=
  (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt

/--
theorem `MDifferentiableAt.neg` / 定理 `MDifferentiableAt.neg`

English:
theorem MDifferentiableAt.neg
  given: (hf : MDiffAt f z)
  statement: MDiffAt (-f) z
  proof: hf.hasMFDerivAt.neg.mdifferentiableAt

中文:
定理 MDifferentiableAt.neg
  条件: (hf : MDiffAt f z)
  结论: MDiffAt (-f) z
  证明: hf.hasMFDerivAt.neg.mdifferentiableAt

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt.neg.mdifferentiableAt, mdifferentiableAt
-/
theorem MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffAt (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt

/--
theorem `MDifferentiableOn.neg` / 定理 `MDifferentiableOn.neg`

English:
theorem MDifferentiableOn.neg
  given: {s : Set M} (hf : MDiff[s] f)
  statement: MDiff[s] (-f)
  proof: fun x hx => (hf x hx).neg

中文:
定理 MDifferentiableOn.neg
  条件: {s : Set M} (hf : MDiff[s] f)
  结论: MDiff[s] (-f)
  证明: fun x hx => (hf x hx).neg
-/
theorem MDifferentiableOn.neg {s : Set M} (hf : MDiff[s] f) : MDiff[s] (-f) :=
  fun x hx => (hf x hx).neg

/--
theorem `mdifferentiableWithinAt_neg` / 定理 `mdifferentiableWithinAt_neg`

English:
theorem mdifferentiableWithinAt_neg
  statement: MDiffAt[s] (-f) z ↔ MDiffAt[s] f z
  proof: ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩

中文:
定理 mdifferentiableWithinAt_neg
  结论: MDiffAt[s] (-f) z ↔ MDiffAt[s] f z
  证明: ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩

Depends on / 依赖: convert, hf.neg, neg_neg
-/
theorem mdifferentiableWithinAt_neg : MDiffAt[s] (-f) z ↔ MDiffAt[s] f z :=
  ⟨fun hf => by convert hf.neg; rw [neg_neg], fun hf => hf.neg⟩

/--
theorem `mdifferentiableAt_neg` / 定理 `mdifferentiableAt_neg`

English:
theorem mdifferentiableAt_neg
  statement: MDiffAt (-f) z ↔ MDiffAt f z
  proof: ⟨fun hf => by convert! hf.neg; rw [neg_neg], fun hf => hf.neg⟩

中文:
定理 mdifferentiableAt_neg
  结论: MDiffAt (-f) z ↔ MDiffAt f z
  证明: ⟨fun hf => by convert! hf.neg; rw [neg_neg], fun hf => hf.neg⟩

Depends on / 依赖: convert, hf.neg, neg_neg
-/
theorem mdifferentiableAt_neg : MDiffAt (-f) z ↔ MDiffAt f z :=
  ⟨fun hf => by convert! hf.neg; rw [neg_neg], fun hf => hf.neg⟩

/--
theorem `MDifferentiable.neg` / 定理 `MDifferentiable.neg`

English:
theorem MDifferentiable.neg
  given: (hf : MDiff f)
  statement: MDiff (-f)
  proof: fun x => (hf x).neg

中文:
定理 MDifferentiable.neg
  条件: (hf : MDiff f)
  结论: MDiff (-f)
  证明: fun x => (hf x).neg
-/
theorem MDifferentiable.neg (hf : MDiff f) : MDiff (-f) := fun x => (hf x).neg

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mfderivWithin_neg` / 定理 `mfderivWithin_neg`

English:
theorem mfderivWithin_neg
  given: (hs : UniqueMDiffAt[s] x)
  proof: by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [if_neg hf, neg_zero]

中文:
定理 mfderivWithin_neg
  条件: (hs : UniqueMDiffAt[s] x)
  证明: by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [if_neg hf, neg_zero]

Depends on / 依赖: MDiffAt, hasMFDerivWithinAt, hf.hasMFDerivWithinAt.neg.mfderivWithin, if_neg, mdifferentiableWithinAt_neg, mfderivWithin, neg_zero, simp_rw
-/
theorem mfderivWithin_neg (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (-f) x = -mfderiv[s] f x := by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [if_neg hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [if_neg hf, neg_zero]

/--
theorem `mfderiv_neg` / 定理 `mfderiv_neg`

English:
theorem mfderiv_neg
  statement: mfderiv% (-f) x = -mfderiv% f x
  proof: by
  rw [← mfderivWithin_univ]; rw [mfderivWithin_neg (uniqueMDiffWithinAt_univ I)]; rw [mfderivWithin_univ]

中文:
定理 mfderiv_neg
  结论: mfderiv% (-f) x = -mfderiv% f x
  证明: by
  rw [← mfderivWithin_univ]; rw [mfderivWithin_neg (uniqueMDiffWithinAt_univ I)]; rw [mfderivWithin_univ]

Depends on / 依赖: mfderivWithin_neg, mfderivWithin_univ, uniqueMDiffWithinAt_univ
-/
theorem mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x := by
  rw [← mfderivWithin_univ]; rw [mfderivWithin_neg (uniqueMDiffWithinAt_univ I)]; rw [mfderivWithin_univ]

/--
theorem `HasMFDerivWithinAt.sub` / 定理 `HasMFDerivWithinAt.sub`

English:
theorem HasMFDerivWithinAt.sub
  given: (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g')
  proof: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

中文:
定理 HasMFDerivWithinAt.sub
  条件: (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g')
  证明: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
-/
theorem HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

/--
theorem `HasMFDerivAt.sub` / 定理 `HasMFDerivAt.sub`

English:
theorem HasMFDerivAt.sub
  given: (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g')
  proof: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

中文:
定理 HasMFDerivAt.sub
  条件: (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g')
  证明: ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
-/
theorem HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

/--
theorem `MDifferentiableWithinAt.sub` / 定理 `MDifferentiableWithinAt.sub`

English:
theorem MDifferentiableWithinAt.sub
  given: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  proof: (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.sub
  条件: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  证明: (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mdifferentiableWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.sub, hg.hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f - g) z :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mdifferentiableWithinAt

/--
theorem `MDifferentiableAt.sub` / 定理 `MDifferentiableAt.sub`

English:
theorem MDifferentiableAt.sub
  given: (hf : MDiffAt f z) (hg : MDiffAt g z)
  statement: MDiffAt (f - g) z
  proof: (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

中文:
定理 MDifferentiableAt.sub
  条件: (hf : MDiffAt f z) (hg : MDiffAt g z)
  结论: MDiffAt (f - g) z
  证明: (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt.sub, hg.hasMFDerivAt, mdifferentiableAt
-/
theorem MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

/--
theorem `MDifferentiableOn.sub` / 定理 `MDifferentiableOn.sub`

English:
theorem MDifferentiableOn.sub
  given: (hf : MDiff[s] f) (hg : MDiff[s] g)
  proof: fun x hx => (hf x hx).sub (hg x hx)

中文:
定理 MDifferentiableOn.sub
  条件: (hf : MDiff[s] f) (hg : MDiff[s] g)
  证明: fun x hx => (hf x hx).sub (hg x hx)
-/
theorem MDifferentiableOn.sub (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (f - g) :=
  fun x hx => (hf x hx).sub (hg x hx)

/--
theorem `MDifferentiable.sub` / 定理 `MDifferentiable.sub`

English:
theorem MDifferentiable.sub
  given: (hf : MDiff f) (hg : MDiff g)
  statement: MDiff (f - g)
  proof: fun x => (hf x).sub (hg x)

中文:
定理 MDifferentiable.sub
  条件: (hf : MDiff f) (hg : MDiff g)
  结论: MDiff (f - g)
  证明: fun x => (hf x).sub (hg x)
-/
theorem MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
  fun x => (hf x).sub (hg x)

/--
theorem `mfderivWithin_sub` / 定理 `mfderivWithin_sub`

English:
theorem mfderivWithin_sub
  statement: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  proof: (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs

中文:
定理 mfderivWithin_sub
  结论: (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
  证明: (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs

Depends on / 依赖: hasMFDerivWithinAt, hf.hasMFDerivWithinAt.sub, hg.hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f - g) z : TangentSpace% z ->L[𝕜] E') =
      (by exact mfderiv[s] f z) - (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs

/--
theorem `mfderiv_sub` / 定理 `mfderiv_sub`

English:
theorem mfderiv_sub
  given: (hf : MDiffAt f z) (hg : MDiffAt g z)
  proof: (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

中文:
定理 mfderiv_sub
  条件: (hf : MDiffAt f z) (hg : MDiffAt g z)
  证明: (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt.sub, hg.hasMFDerivAt, mfderiv
-/
theorem mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f - g) z : TangentSpace% z ->L[𝕜] E') =
      (by exact mfderiv% f z) - (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M -> F'}
  {p' q' : TangentSpace% z ->L[𝕜] F'}

/--
theorem `HasMFDerivWithinAt.mul'` / 定理 `HasMFDerivWithinAt.mul'`

English:
theorem HasMFDerivWithinAt.mul'
  statement: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  proof: ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩

中文:
定理 HasMFDerivWithinAt.mul'
  结论: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  证明: ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩

Depends on / 依赖: mfld_simps
-/
theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p' <• q z : E ->L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩

/--
theorem `HasMFDerivAt.mul'` / 定理 `HasMFDerivAt.mul'`

English:
theorem HasMFDerivAt.mul'
  statement: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  proof: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

中文:
定理 HasMFDerivAt.mul'
  结论: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  证明: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hasMFDerivWithinAt_univ.mp, hp.hasMFDerivWithinAt.mul, hq.hasMFDerivWithinAt
-/
theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p' <• q z : E ->L[𝕜] F') :=
hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

/--
theorem `MDifferentiableWithinAt.mul` / 定理 `MDifferentiableWithinAt.mul`

English:
theorem MDifferentiableWithinAt.mul
  statement: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  proof: (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.mul
  结论: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  证明: (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hp.hasMFDerivWithinAt.mul, hq.hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

/--
theorem `MDifferentiableAt.mul` / 定理 `MDifferentiableAt.mul`

English:
theorem MDifferentiableAt.mul
  statement: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
  proof: (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

中文:
定理 MDifferentiableAt.mul
  结论: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
  证明: (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt, hp.hasMFDerivAt.mul, hq.hasMFDerivAt, mdifferentiableAt
-/
theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

/--
theorem `MDifferentiableOn.mul` / 定理 `MDifferentiableOn.mul`

English:
theorem MDifferentiableOn.mul
  statement: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
  proof: fun x hx => (hp x hx).mul hq x hx

中文:
定理 MDifferentiableOn.mul
  结论: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
  证明: fun x hx => (hp x hx).mul hq x hx

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, I.smithCoeffs_ne_zero, PowerBasis, PowerBasis.finite, finite, powerBasis, smithCoeffs_ne_zero
-/
theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s :=
fun x hx => (hp x hx).mul hq x hx

/--
theorem `MDifferentiable.mul` / 定理 `MDifferentiable.mul`

English:
theorem MDifferentiable.mul
  statement: (hp : MDifferentiable I 𝓘(𝕜, F') p)
  proof: fun x => (hp x).mul (hq x)

中文:
定理 MDifferentiable.mul
  结论: (hp : MDifferentiable I 𝓘(𝕜, F') p)
  证明: fun x => (hp x).mul (hq x)
-/
theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) :=
  fun x => (hp x).mul (hq x)

/--
theorem `MDifferentiableWithinAt.pow` / 定理 `MDifferentiableWithinAt.pow`

English:
theorem MDifferentiableWithinAt.pow
  statement: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  proof: by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp

中文:
定理 MDifferentiableWithinAt.pow
  结论: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  证明: by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp

Depends on / 依赖: hn.mul, mdifferentiableWithinAt_const, pow_succ, pow_zero
-/
theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (n : Nat) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z := by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp

/--
theorem `MDifferentiableAt.pow` / 定理 `MDifferentiableAt.pow`

English:
theorem MDifferentiableAt.pow
  given: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : Nat)
  proof: mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

中文:
定理 MDifferentiableAt.pow
  条件: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : 自然数)
  证明: mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

Depends on / 依赖: hp.mdifferentiableWithinAt.pow, mdifferentiableWithinAt, mdifferentiableWithinAt_univ, mdifferentiableWithinAt_univ.mp
-/
theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : Nat) :
    MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z :=
  mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

/--
theorem `MDifferentiableOn.pow` / 定理 `MDifferentiableOn.pow`

English:
theorem MDifferentiableOn.pow
  given: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : Nat)
  proof: fun x hx => (hp x hx).pow n

中文:
定理 MDifferentiableOn.pow
  条件: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : 自然数)
  证明: fun x hx => (hp x hx).pow n
-/
theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : Nat) :
    MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s := fun x hx => (hp x hx).pow n

/--
theorem `MDifferentiable.pow` / 定理 `MDifferentiable.pow`

English:
theorem MDifferentiable.pow
  given: (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : Nat)
  proof: fun x => (hp x).pow n

中文:
定理 MDifferentiable.pow
  条件: (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : 自然数)
  证明: fun x => (hp x).pow n
-/
theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : Nat) :
    MDifferentiable I 𝓘(𝕜, F') (p ^ n) := fun x => (hp x).pow n

end AlgebraOverRing

section AlgebraOverCommRing

variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M -> F'}
  {p' q' : TangentSpace% z ->L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasMFDerivWithinAt.mul` / 定理 `HasMFDerivWithinAt.mul`

English:
theorem HasMFDerivWithinAt.mul
  statement: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  proof: by
  convert! hp.mul' hq; ext _; apply mul_comm

中文:
定理 HasMFDerivWithinAt.mul
  结论: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  证明: by
  convert! hp.mul' hq; ext _; apply mul_comm

Depends on / 依赖: convert, hp.mul, mul_comm
-/
theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E ->L[𝕜] F') := by
  convert! hp.mul' hq; ext _; apply mul_comm

/--
theorem `HasMFDerivAt.mul` / 定理 `HasMFDerivAt.mul`

English:
theorem HasMFDerivAt.mul
  statement: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  proof: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

中文:
定理 HasMFDerivAt.mul
  结论: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  证明: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hasMFDerivWithinAt_univ.mp, hp.hasMFDerivWithinAt.mul, hq.hasMFDerivWithinAt
-/
theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E ->L[𝕜] F') :=
hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

section prod
variable {ι : Type} {t : Finset ι} {f : ι -> M -> F'} {f' : ι -> TangentSpace% z ->L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasMFDerivWithinAt.prod` / 引理 `HasMFDerivWithinAt.prod`

English:
lemma HasMFDerivWithinAt.prod
  statement: [DecidableEq ι]
  proof: by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi]; rw [t.erase_insert hi]; rw [t.prod_insert hi]; rw [add_comm]
    rw [t.forall_mem_insert] at hf
    convert! hf.1.mul (IH hf.2) using 2
    · simp o

中文:
引理 HasMFDerivWithinAt.prod
  结论: [DecidableEq ι]
  证明: by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi]; rw [t.erase_insert hi]; rw [t.prod_insert hi]; rw [add_comm]
    rw [t.forall_mem_insert] at hf
    convert! hf.1.mul (IH hf.2) using 2
    · simp o

Depends on / 依赖: Finset, Finset.induction_on, Finset.prod_insert, add_comm, convert, erase_insert, erase_insert_of_ne, forall_mem_insert, hasMFDerivWithinAt_const, induction_on, insert, mul_smul, prod_insert, smul_sum, sum_congr, sum_insert, t.erase_insert, t.erase_insert_of_ne, t.forall_mem_insert, t.prod_insert
-/
lemma HasMFDerivWithinAt.prod [DecidableEq ι]
    (hf : forall i in t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i in t, f i) s z
      (∑ i in t, (∏ j in t.erase i, f j z) • (f' i)) := by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi]; rw [t.erase_insert hi]; rw [t.prod_insert hi]; rw [add_comm]
    rw [t.forall_mem_insert] at hf
    convert! hf.1.mul (IH hf.2) using 2
    · simp only [t.smul_sum, ← mul_smul]
      refine t.sum_congr rfl (fun j hj => ?_)
      rw [t.erase_insert_of_ne (by grind)]; rw [Finset.prod_insert (by grind)]
    · simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `HasMFDerivAt.prod` / 引理 `HasMFDerivAt.prod`

English:
lemma HasMFDerivAt.prod
  statement: [DecidableEq ι]
  proof: by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

中文:
引理 HasMFDerivAt.prod
  结论: [DecidableEq ι]
  证明: by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.prod, hasMFDerivWithinAt_univ
-/
lemma HasMFDerivAt.prod [DecidableEq ι]
    (hf : forall i in t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z (f' i)) :
    HasMFDerivAt I 𝓘(𝕜, F') (∏ i in t, f i) z (∑ i in t, (∏ j in t.erase i, f j z) • (f' i)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

/--
lemma `MDifferentiableWithinAt.prod` / 引理 `MDifferentiableWithinAt.prod`

English:
lemma MDifferentiableWithinAt.prod
  proof: by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

中文:
引理 MDifferentiableWithinAt.prod
  证明: by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt
-/
lemma MDifferentiableWithinAt.prod
    (hf : forall i in t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i in t, f i) s z := by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi => (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

/--
lemma `MDifferentiableAt.prod` / 引理 `MDifferentiableAt.prod`

English:
lemma MDifferentiableAt.prod
  given: (hf : forall i in t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z)
  proof: by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

中文:
引理 MDifferentiableAt.prod
  条件: (hf : 对任意 i in t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z)
  证明: by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.prod, mdifferentiableWithinAt_univ
-/
lemma MDifferentiableAt.prod (hf : forall i in t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, F') (∏ i in t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

/--
lemma `MDifferentiableOn.prod` / 引理 `MDifferentiableOn.prod`

English:
lemma MDifferentiableOn.prod
  given: (hf : forall i in t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s)
  proof: fun z hz => .prod fun i hi => hf i hi z hz

中文:
引理 MDifferentiableOn.prod
  条件: (hf : 对任意 i in t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s)
  证明: fun z hz => .prod fun i hi => hf i hi z hz
-/
lemma MDifferentiableOn.prod (hf : forall i in t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, F') (∏ i in t, f i) s :=
  fun z hz => .prod fun i hi => hf i hi z hz

/--
lemma `MDifferentiable.prod` / 引理 `MDifferentiable.prod`

English:
lemma MDifferentiable.prod
  given: (hf : forall i in t, MDifferentiable I 𝓘(𝕜, F') (f i))
  proof: fun z => .prod fun i hi => hf i hi z

中文:
引理 MDifferentiable.prod
  条件: (hf : 对任意 i in t, MDifferentiable I 𝓘(𝕜, F') (f i))
  证明: fun z => .prod fun i hi => hf i hi z
-/
lemma MDifferentiable.prod (hf : forall i in t, MDifferentiable I 𝓘(𝕜, F') (f i)) :
    MDifferentiable I 𝓘(𝕜, F') (∏ i in t, f i) :=
  fun z => .prod fun i hi => hf i hi z

end prod

end AlgebraOverCommRing

section DivisionRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedDivisionRing F'] [NormedAlgebra 𝕜 F'] {p q : M -> F'}
  {p' q' : TangentSpace% z ->L[𝕜] F'}

/--
lemma `HasMFDerivWithinAt.inv'` / 引理 `HasMFDerivWithinAt.inv'`

English:
lemma HasMFDerivWithinAt.inv'
  given: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0)
  proof: (hasFDerivAt_inv' hp_ne).hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hp)

中文:
引理 HasMFDerivWithinAt.inv'
  条件: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0)
  证明: (hasFDerivAt_inv' hp_ne).hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hp)

Depends on / 依赖: comp_hasMFDerivWithinAt, hasFDerivAt_inv, hasMFDerivAt, hasMFDerivAt.comp_hasMFDerivWithinAt, hp_ne
-/
lemma HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-((p z)⁻¹ •> p' <• (p z)⁻¹) : E ->L[𝕜] F') :=
  (hasFDerivAt_inv' hp_ne).hasMFDerivAt.comp_hasMFDerivWithinAt (hf := hp)

/--
lemma `HasMFDerivAt.inv'` / 引理 `HasMFDerivAt.inv'`

English:
lemma HasMFDerivAt.inv'
  given: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0)
  proof: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv' hp_ne

中文:
引理 HasMFDerivAt.inv'
  条件: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0)
  证明: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv' hp_ne

Depends on / 依赖: hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hasMFDerivWithinAt_univ.mp, hp.hasMFDerivWithinAt.inv, hp_ne
-/
lemma HasMFDerivAt.inv' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-((p z)⁻¹ •> p' <• (p z)⁻¹) : E ->L[𝕜] F') :=
hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv' hp_ne

/--
lemma `MDifferentiableWithinAt.inv` / 引理 `MDifferentiableWithinAt.inv`

English:
lemma MDifferentiableWithinAt.inv
  statement: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  proof: (hp.hasMFDerivWithinAt.inv' hp_ne).mdifferentiableWithinAt

中文:
引理 MDifferentiableWithinAt.inv
  结论: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  证明: (hp.hasMFDerivWithinAt.inv' hp_ne).mdifferentiableWithinAt

Depends on / 依赖: Finite, IsTorsionFree, Module, Module.Finite, Module.Free, Module.free_of_finite_type_torsion_free, free_of_finite_type_torsion_free, hasMFDerivWithinAt, hp.hasMFDerivWithinAt.inv, hp_ne, mdifferentiableWithinAt, restrictScalars
-/
lemma MDifferentiableWithinAt.inv (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hp_ne : p z != 0) : MDifferentiableWithinAt I 𝓘(𝕜, F') p⁻¹ s z :=
  (hp.hasMFDerivWithinAt.inv' hp_ne).mdifferentiableWithinAt

/--
lemma `MDifferentiableAt.inv` / 引理 `MDifferentiableAt.inv`

English:
lemma MDifferentiableAt.inv
  given: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z != 0)
  proof: mdifferentiableWithinAt_univ.mp hp.mdifferentiableWithinAt.inv hp_ne

中文:
引理 MDifferentiableAt.inv
  条件: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z != 0)
  证明: mdifferentiableWithinAt_univ.mp hp.mdifferentiableWithinAt.inv hp_ne

Depends on / 依赖: hp.mdifferentiableWithinAt.inv, hp_ne, mdifferentiableWithinAt, mdifferentiableWithinAt_univ, mdifferentiableWithinAt_univ.mp
-/
lemma MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (hp_ne : p z != 0) :
    MDifferentiableAt I 𝓘(𝕜, F') p⁻¹ z :=
mdifferentiableWithinAt_univ.mp hp.mdifferentiableWithinAt.inv hp_ne

/--
theorem `MDifferentiableOn.inv` / 定理 `MDifferentiableOn.inv`

English:
theorem MDifferentiableOn.inv
  given: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : forall z in s, p z != 0)
  proof: fun x hx => (hp x hx).inv (hp_ne x hx)

中文:
定理 MDifferentiableOn.inv
  条件: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : 对任意 z in s, p z != 0)
  证明: fun x hx => (hp x hx).inv (hp_ne x hx)

Depends on / 依赖: hp_ne
-/
theorem MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (hp_ne : forall z in s, p z != 0) :
    MDifferentiableOn I 𝓘(𝕜, F') p⁻¹ s :=
  fun x hx => (hp x hx).inv (hp_ne x hx)

/--
theorem `MDifferentiable.inv` / 定理 `MDifferentiable.inv`

English:
theorem MDifferentiable.inv
  given: (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : forall z, p z != 0)
  proof: fun x => (hp x).inv (hp_ne x)

中文:
定理 MDifferentiable.inv
  条件: (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : 对任意 z, p z != 0)
  证明: fun x => (hp x).inv (hp_ne x)

Depends on / 依赖: hp_ne
-/
theorem MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F') p) (hp_ne : forall z, p z != 0) :
    MDifferentiable I 𝓘(𝕜, F') p⁻¹ :=
  fun x => (hp x).inv (hp_ne x)

/--
lemma `MDifferentiableWithinAt.div` / 引理 `MDifferentiableWithinAt.div`

English:
lemma MDifferentiableWithinAt.div
  statement: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  proof: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

中文:
引理 MDifferentiableWithinAt.div
  结论: (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
  证明: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

Depends on / 依赖: div_eq_mul_inv, hp.mul, hq.inv, hq_ne
-/
lemma MDifferentiableWithinAt.div (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) (hq_ne : q z != 0) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p / q) s z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

/--
lemma `MDifferentiableAt.div` / 引理 `MDifferentiableAt.div`

English:
lemma MDifferentiableAt.div
  statement: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
  proof: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

中文:
引理 MDifferentiableAt.div
  结论: (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
  证明: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

Depends on / 依赖: div_eq_mul_inv, hp.mul, hq.inv, hq_ne
-/
lemma MDifferentiableAt.div (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) (hq_ne : q z != 0) :
    MDifferentiableAt I 𝓘(𝕜, F') (p / q) z := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

/--
lemma `MDifferentiableOn.div` / 引理 `MDifferentiableOn.div`

English:
lemma MDifferentiableOn.div
  statement: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
  proof: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

中文:
引理 MDifferentiableOn.div
  结论: (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
  证明: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

Depends on / 依赖: div_eq_mul_inv, hp.mul, hq.inv, hq_ne
-/
lemma MDifferentiableOn.div (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) (hq_ne : forall z in s, q z != 0) :
    MDifferentiableOn I 𝓘(𝕜, F') (p / q) s := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

/--
lemma `MDifferentiable.div` / 引理 `MDifferentiable.div`

English:
lemma MDifferentiable.div
  statement: (hp : MDifferentiable I 𝓘(𝕜, F') p)
  proof: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

中文:
引理 MDifferentiable.div
  结论: (hp : MDifferentiable I 𝓘(𝕜, F') p)
  证明: by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

Depends on / 依赖: div_eq_mul_inv, hp.mul, hq.inv, hq_ne
-/
lemma MDifferentiable.div (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) (hq_ne : forall z, q z != 0) :
    MDifferentiable I 𝓘(𝕜, F') (p / q) := by
  simpa [div_eq_mul_inv] using hp.mul (hq.inv hq_ne)

end DivisionRing

section Field

variable {z : M} {F' : Type*} [NormedField F'] [NormedAlgebra 𝕜 F'] {p q : M -> F'}
  {p' q' : TangentSpace% z ->L[𝕜] F'}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `HasMFDerivWithinAt.inv` / 引理 `HasMFDerivWithinAt.inv`

English:
lemma HasMFDerivWithinAt.inv
  given: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0)
  proof: by
  convert! hp.inv' hp_ne
  ext
  simp
  ring_nf

中文:
引理 HasMFDerivWithinAt.inv
  条件: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0)
  证明: by
  convert! hp.inv' hp_ne
  ext
  simp
  ring_nf

Depends on / 依赖: convert, hp.inv, hp_ne, ring_nf
-/
lemma HasMFDerivWithinAt.inv (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p') (hp_ne : p z != 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p⁻¹) s z (-(p z ^ 2)⁻¹ • p' : E ->L[𝕜] F') := by
  convert! hp.inv' hp_ne
  ext
  simp
  ring_nf

/--
lemma `HasMFDerivAt.inv` / 引理 `HasMFDerivAt.inv`

English:
lemma HasMFDerivAt.inv
  given: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0)
  proof: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv hp_ne

中文:
引理 HasMFDerivAt.inv
  条件: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0)
  证明: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv hp_ne

Depends on / 依赖: hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hasMFDerivWithinAt_univ.mp, hp.hasMFDerivWithinAt.inv, hp_ne
-/
lemma HasMFDerivAt.inv (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p') (hp_ne : p z != 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p⁻¹) z (-(p z ^ 2)⁻¹ • p' : E ->L[𝕜] F') :=
hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.inv hp_ne

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `HasMFDerivWithinAt.div` / 引理 `HasMFDerivWithinAt.div`

English:
lemma HasMFDerivWithinAt.div
  statement: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  proof: by
  convert! hp.mul (hq.inv hq_ne) using 1
  · simp [div_eq_mul_inv]
  · ext
    simp [div_eq_mul_inv]
    ring

中文:
引理 HasMFDerivWithinAt.div
  结论: (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
  证明: by
  convert! hp.mul (hq.inv hq_ne) using 1
  · simp [div_eq_mul_inv]
  · ext
    simp [div_eq_mul_inv]
    ring

Depends on / 依赖: convert, div_eq_mul_inv, hp.mul, hq.inv, hq_ne
-/
lemma HasMFDerivWithinAt.div (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') (hq_ne : q z != 0) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p / q) s z
      ((1 / q z) • p' - (p z / q z ^ 2) • q' : E ->L[𝕜] F') := by
  convert! hp.mul (hq.inv hq_ne) using 1
  · simp [div_eq_mul_inv]
  · ext
    simp [div_eq_mul_inv]
    ring

/--
lemma `HasMFDerivAt.div` / 引理 `HasMFDerivAt.div`

English:
lemma HasMFDerivAt.div
  statement: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  proof: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt hq_ne

中文:
引理 HasMFDerivAt.div
  结论: (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
  证明: hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt hq_ne

Depends on / 依赖: hasMFDerivWithinAt, hasMFDerivWithinAt_univ, hasMFDerivWithinAt_univ.mp, hp.hasMFDerivWithinAt.div, hq.hasMFDerivWithinAt, hq_ne
-/
lemma HasMFDerivAt.div (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') (hq_ne : q z != 0) :
    HasMFDerivAt I 𝓘(𝕜, F') (p / q) z
      ((1 / q z) • p' - (p z / q z ^ 2) • q' : E ->L[𝕜] F') :=
hasMFDerivWithinAt_univ.mp hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt hq_ne

end Field

end Arithmetic

end SpecificFunctions
