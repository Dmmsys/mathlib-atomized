/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Complement

/-! # Continuous linear maps with a continuous left/right inverse

This file defines continuous linear maps which admit a continuous left/right inverse.

We prove that both of these classes of maps are closed under products, composition and contain
linear equivalences, and a sufficient criterion in finite dimension: a surjective linear map on a
finite-dimensional space always admits a continuous right inverse; an injective linear map on a
finite-dimensional space always admits a continuous left inverse.

We also prove an equivalent characterisation of admitting a continuous left inverse: `f` admits a
continuous left inverse if and only if it is injective, has closed range and its range admits a
closed complement. This characterisation is used to extract a complement from immersions, for use
in the regular value theorem. (For submersions, there is a natural choice of complement, and an
analogous statement is not necessary.)

This concept is used to give an equivalent definition of immersions and submersions of manifolds.

## Main definitions and results

* `ContinuousLinearMap.HasLeftInverse`: a continuous linear map admits a left inverse
  which is a continuous linear map itself
* `ContinuousLinearMap.HasRightInverse`: a continuous linear map admits a right inverse
  which is a continuous linear map itself

* `ContinuousLinearMap.HasLeftInverse.isClosed_range`: if `f` has a continuous left inverse,
  its range is closed
* `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`: if `f` has a continuous left
  inverse, its range admits a closed complement
* `ContinuousLinearMap.HasLeftInverse.complement`: a choice of closed complement for `range f`
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`:
  if `f` is injective and has closed range with a closed complement, it admits a continuous left
  inverse

* `ContinuousLinearEquiv.hasLeftInverse` and `ContinuousLinearEquiv.hasRightInverse`:
  a continuous linear equivalence admits a continuous left (resp. right) inverse
* `ContinuousLinearMap.HasLeftInverse.comp`, `ContinuousLinearMap.HasRightInverse.comp`:
  if `f : E → F` and `g : F → G` both admit a continuous left (resp. right) inverse,
  so does `g.comp f`.
* `ContinuousLinearMap.HasLeftInverse.of_comp`, `ContinuousLinearMap.HasRightInverse.of_comp`:
  suppose `f : E → F` and `g : F → G` are continuous linear maps.
  If `g.comp f : E → G` admits a continuous left inverse, then so does `f`.
  If `g.comp f : E → G` admits a continuous right inverse, then so does `g`.
* `ContinuousLinearMap.HasLeftInverse.prodMap`, `ContinuousLinearMap.HasRightInverse.prodMap`:
  having a continuous left/right inverse is closed under taking products
* `ContinuousLinearMap.HasLeftInverse.inl`, `ContinuousLinearMap.HasLeftInverse.inr`:
  `ContinuousLinearMap.inl` and `.inr` have a continuous left inverse
* `ContinuousLinearMap.HasRightInverse.fst`, `ContinuousLinearMap.HasRightInverse.snd`:
  `ContinuousLinearMap.fst` and `.snd` have a continuous right inverse
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`:
  if `f : E → F` is injective and `F` is finite-dimensional, `f` has a continuous left inverse.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional`:
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO

* Suppose `E` and `F` are Banach and `f : E → F` is Fredholm.
  If `f` is surjective, it has a continuous right inverse.
  If `f` is injective, it has a continuous left inverse.

-/

public section

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

/--
Definition of `ContinuousLinearMap.HasLeftInverse` / `ContinuousLinearMap.HasLeftInverse` 的定义

English:
definition ContinuousLinearMap.HasLeftInverse
  signature: (f : E ->L[R] F)
  body: exists g : F ->L[R] E, LeftInverse g f

中文:
定义 ContinuousLinearMap.HasLeftInverse
  签名: (f : E ->L[R] F)
  定义体: exists g : F ->L[R] E, LeftInverse g f
-/
@[expose] protected def ContinuousLinearMap.HasLeftInverse (f : E ->L[R] F) : Prop :=
  exists g : F ->L[R] E, LeftInverse g f

/--
Definition of `ContinuousLinearMap.HasRightInverse` / `ContinuousLinearMap.HasRightInverse` 的定义

English:
definition ContinuousLinearMap.HasRightInverse
  signature: (f : E ->L[R] F)
  body: exists g : F ->L[R] E, RightInverse g f

中文:
定义 ContinuousLinearMap.HasRightInverse
  签名: (f : E ->L[R] F)
  定义体: exists g : F ->L[R] E, RightInverse g f
-/
@[expose] protected def ContinuousLinearMap.HasRightInverse (f : E ->L[R] F) : Prop :=
  exists g : F ->L[R] E, RightInverse g f

namespace ContinuousLinearMap

namespace HasLeftInverse

variable {f : E ->L[R] F}

/--
Definition of `leftInverse` / `leftInverse` 的定义

English:
definition leftInverse
  signature: (h : f.HasLeftInverse)
  body: Classical.choose h

中文:
定义 leftInverse
  签名: (h : f.HasLeftInverse)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def leftInverse (h : f.HasLeftInverse) : F ->L[R] E := Classical.choose h

/--
lemma `leftInverse_leftInverse` / 引理 `leftInverse_leftInverse`

English:
lemma leftInverse_leftInverse
  given: (h : f.HasLeftInverse)
  statement: LeftInverse h.leftInverse f
  proof: Classical.choose_spec h

中文:
引理 leftInverse_leftInverse
  条件: (h : f.HasLeftInverse)
  结论: LeftInverse h.leftInverse f
  证明: Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma leftInverse_leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h

/--
lemma `injective` / 引理 `injective`

English:
lemma injective
  given: (h : f.HasLeftInverse)
  statement: Injective f
  proof: h.leftInverse_leftInverse.injective

example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

中文:
引理 injective
  条件: (h : f.HasLeftInverse)
  结论: Injective f
  证明: h.leftInverse_leftInverse.injective

example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

Depends on / 依赖: h.leftInverse_leftInverse.injective, injective, leftInverse_leftInverse
-/
lemma injective (h : f.HasLeftInverse) : Injective f :=
  h.leftInverse_leftInverse.injective

example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=
  h.leftInverse_leftInverse x

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {g : E ->L[R] F} (hf : f.HasLeftInverse) (hfg : g = f)
  proof: hfg ▸ hf

中文:
引理 congr
  条件: {g : E ->L[R] F} (hf : f.HasLeftInverse) (hfg : g = f)
  证明: hfg ▸ hf
-/
lemma congr {g : E ->L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) :
    g.HasLeftInverse :=
  hfg ▸ hf

/--
lemma `_root_.ContinuousLinearEquiv.hasLeftInverse` / 引理 `_root_.ContinuousLinearEquiv.hasLeftInverse`

English:
lemma _root_.ContinuousLinearEquiv.hasLeftInverse
  given: (f : E ≃L[R] F)
  proof: ⟨f.symm, rightInverse_of_comp (by simp)⟩

中文:
引理 _root_.ContinuousLinearEquiv.hasLeftInverse
  条件: (f : E ≃L[R] F)
  证明: ⟨f.symm, rightInverse_of_comp (by simp)⟩

Depends on / 依赖: f.symm, rightInverse_of_comp
-/
lemma _root_.ContinuousLinearEquiv.hasLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/--
lemma `_root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse` / 引理 `_root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse`

English:
lemma _root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse
  given: (f : E ≃L[R] F)
  proof: by
  ext y
  calc f.hasLeftInverse.leftInverse y
    _ = f.hasLeftInverse.leftInverse (f (f.symm y)) := by simp
    _ = f.symm y := f.hasLeftInverse.leftInverse_leftInverse (f.symm y)

中文:
引理 _root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse
  条件: (f : E ≃L[R] F)
  证明: by
  ext y
  calc f.hasLeftInverse.leftInverse y
    _ = f.hasLeftInverse.leftInverse (f (f.symm y)) := by simp
    _ = f.symm y := f.hasLeftInverse.leftInverse_leftInverse (f.symm y)
-/
@[simp] lemma _root_.ContinuousLinearEquiv.leftInverse_hasLeftInverse (f : E ≃L[R] F) :
    f.hasLeftInverse.leftInverse = f.symm := by
  ext y
  calc f.hasLeftInverse.leftInverse y
    _ = f.hasLeftInverse.leftInverse (f (f.symm y)) := by simp
    _ = f.symm y := f.hasLeftInverse.leftInverse_leftInverse (f.symm y)

/--
lemma `of_isInvertible` / 引理 `of_isInvertible`

English:
lemma of_isInvertible
  given: (hf : IsInvertible f)
  statement: f.HasLeftInverse
  proof: by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasLeftInverse

中文:
引理 of_isInvertible
  条件: (hf : IsInvertible f)
  结论: f.HasLeftInverse
  证明: by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasLeftInverse

Depends on / 依赖: e.hasLeftInverse, hasLeftInverse
-/
lemma of_isInvertible (hf : IsInvertible f) : f.HasLeftInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasLeftInverse

/--
lemma `prodMap` / 引理 `prodMap`

English:
lemma prodMap
  given: {g : E' ->L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse)
  proof: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

中文:
引理 prodMap
  条件: {g : E' ->L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse)
  证明: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

Depends on / 依赖: finv.prodMap, prodMap
-/
lemma prodMap {g : E' ->L[R] F'} (hf : f.HasLeftInverse) (hg : g.HasLeftInverse) :
    (f.prodMap g).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {g : F ->L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse)
  proof: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hginv]; rw [hfinv]

中文:
引理 comp
  条件: {g : F ->L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse)
  证明: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hginv]; rw [hfinv]

Depends on / 依赖: comp_apply, finv.comp
-/
lemma comp {g : F ->L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) :
    (g.comp f).HasLeftInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hginv]; rw [hfinv]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: {g : F ->L[R] G} (hfg : (g.comp f).HasLeftInverse)
  proof: by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y => ?_⟩
  simp only [comp_apply]
  exact hfginv y

中文:
引理 of_comp
  条件: {g : F ->L[R] G} (hfg : (g.comp f).HasLeftInverse)
  证明: by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y => ?_⟩
  simp only [comp_apply]
  exact hfginv y

Depends on / 依赖: comp_apply, fginv.comp, hfginv
-/
lemma of_comp {g : F ->L[R] G} (hfg : (g.comp f).HasLeftInverse) :
    f.HasLeftInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  refine ⟨fginv.comp g, fun y => ?_⟩
  simp only [comp_apply]
  exact hfginv y

/--
lemma `comp_continuousLinearEquivalence` / 引理 `comp_continuousLinearEquivalence`

English:
lemma comp_continuousLinearEquivalence
  given: {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse)
  proof: hf.comp f₀.hasLeftInverse

中文:
引理 comp_continuousLinearEquivalence
  条件: {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse)
  证明: hf.comp f₀.hasLeftInverse

Depends on / 依赖: hasLeftInverse, hf.comp
-/
lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasLeftInverse) :
    (f.comp f₀.toContinuousLinearMap).HasLeftInverse :=
  hf.comp f₀.hasLeftInverse

/--
lemma `continuousLinearEquivalence_comp` / 引理 `continuousLinearEquivalence_comp`

English:
lemma continuousLinearEquivalence_comp
  given: {g : F ≃L[R] F'} (hf : f.HasLeftInverse)
  proof: g.hasLeftInverse.comp hf

中文:
引理 continuousLinearEquivalence_comp
  条件: {g : F ≃L[R] F'} (hf : f.HasLeftInverse)
  证明: g.hasLeftInverse.comp hf

Depends on / 依赖: g.hasLeftInverse.comp, hasLeftInverse
-/
lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasLeftInverse) :
    (g.toContinuousLinearMap.comp f).HasLeftInverse :=
  g.hasLeftInverse.comp hf

/--
lemma `inl` / 引理 `inl`

English:
lemma inl
  statement: (ContinuousLinearMap.inl R F G).HasLeftInverse
  proof: by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp

中文:
引理 inl
  结论: (ContinuousLinearMap.inl R F G).HasLeftInverse
  证明: by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp
-/
protected lemma inl : (ContinuousLinearMap.inl R F G).HasLeftInverse := by
  use ContinuousLinearMap.fst _ _ _
  intro x
  simp

/--
lemma `inr` / 引理 `inr`

English:
lemma inr
  statement: (ContinuousLinearMap.inr R F G).HasLeftInverse
  proof: by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp

中文:
引理 inr
  结论: (ContinuousLinearMap.inr R F G).HasLeftInverse
  证明: by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp
-/
protected lemma inr : (ContinuousLinearMap.inr R F G).HasLeftInverse := by
  use ContinuousLinearMap.snd _ _ _
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E ->L[𝕜] F}

/--
lemma `of_injective_of_finiteDimensional` / 引理 `of_injective_of_finiteDimensional`

English:
lemma of_injective_of_finiteDimensional
  statement: [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  proof: by
  -- An injective linear map has a linear inverse; this inverse is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩

中文:
引理 of_injective_of_finiteDimensional
  结论: [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  证明: by
  -- An injective linear map has a linear inverse; this inverse is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩
-/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Injective f) :
    f.HasLeftInverse := by
  -- An injective linear map has a linear inverse; this inverse is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩, fun x => congr($hg x)⟩

end NontriviallyNormedField

/-! An equivalent characterisation of maps with a continuous left inverse -/
section Ring

-- The next lemmas assume we are working over a ring.
variable {R E E' F F' G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] {f : E ->L[R] F}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `closedComplemented_range` / 引理 `closedComplemented_range`

English:
lemma closedComplemented_range
  given: (hf : f.HasLeftInverse)
  statement: Submodule.ClosedComplemented f.range
  proof: by
  -- Idea of proof: let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f.
  -- Mathlib's definition of closed complement takes a continuous projection to f.range instead
  -- of a complementary subspace: consider `f.comp g` instead, which is contin

中文:
引理 closedComplemented_range
  条件: (hf : f.HasLeftInverse)
  结论: Submodule.ClosedComplemented f.range
  证明: by
  -- Idea of proof: let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f.
  -- Mathlib's definition of closed complement takes a continuous projection to f.range instead
  -- of a complementary subspace: consider `f.comp g` instead, which is contin
-/
lemma closedComplemented_range (hf : f.HasLeftInverse) : Submodule.ClosedComplemented f.range := by
  -- Idea of proof: let g be a left inverse for f. Then ker g is a closed subspace of F,
  -- and a complement to range f.
  -- Mathlib's definition of closed complement takes a continuous projection to f.range instead
  -- of a complementary subspace: consider `f.comp g` instead, which is continuous as both maps are,
  -- and idempotent as a continuous left inverse.
  use (f.comp hf.leftInverse).codRestrict f.range (by intro y; simp)
  rintro ⟨y, x, rfl⟩
  ext
  simp only [coe_coe, coe_codRestrict_apply, comp_apply]
  rw [hf.leftInverse_leftInverse]

section

variable [T1Space F]

/--
lemma `isClosed_range` / 引理 `isClosed_range`

English:
lemma isClosed_range
  given: (hf : f.HasLeftInverse) [IsTopologicalAddGroup F]
  proof: by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  rw [← f.range_toLinearMap]; rw [← f.coe_range]; rw [f.range_eq_ker_of_leftInverse (hf.leftInverse_leftInverse)]
  exact ((f.comp hf.leftInverse) - (ContinuousLinearMap.id R F)).isClosed_ker

中文:
引理 isClosed_range
  条件: (hf : f.HasLeftInverse) [IsTopologicalAddGroup F]
  证明: by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  rw [← f.range_toLinearMap]; rw [← f.coe_range]; rw [f.range_eq_ker_of_leftInverse (hf.leftInverse_leftInverse)]
  exact ((f.comp hf.leftInverse) - (ContinuousLinearMap.id R F)).isClosed_ker
-/
lemma isClosed_range (hf : f.HasLeftInverse) [IsTopologicalAddGroup F] :
    IsClosed (range f) := by
  -- `range f = ker (f ∘ g - id)` is closed since `f ∘ g - id` is continuous.
  rw [← f.range_toLinearMap]; rw [← f.coe_range]; rw [f.range_eq_ker_of_leftInverse (hf.leftInverse_leftInverse)]
  exact ((f.comp hf.leftInverse) - (ContinuousLinearMap.id R F)).isClosed_ker

/--
Definition of `complement` / `complement` 的定义

English:
definition complement
  signature: (h : f.HasLeftInverse)
  body: h.closedComplemented_range.complement

中文:
定义 complement
  签名: (h : f.HasLeftInverse)
  定义体: h.closedComplemented_range.complement

Depends on / 依赖: closedComplemented_range, complement, h.closedComplemented_range.complement
-/
def complement (h : f.HasLeftInverse) : Submodule R F :=
  h.closedComplemented_range.complement

/--
lemma `isClosed_complement` / 引理 `isClosed_complement`

English:
lemma isClosed_complement
  given: (h : f.HasLeftInverse)
  statement: IsClosed (X := F) h.complement
  proof: h.closedComplemented_range.isClosed_complement

omit [T1Space F] in

中文:
引理 isClosed_complement
  条件: (h : f.HasLeftInverse)
  结论: IsClosed (X := F) h.complement
  证明: h.closedComplemented_range.isClosed_complement

omit [T1Space F] in

Depends on / 依赖: complement, h.complement
-/
lemma isClosed_complement (h : f.HasLeftInverse) : IsClosed (X := F) h.complement :=
  h.closedComplemented_range.isClosed_complement

omit [T1Space F] in
/--
lemma `isCompl_complement` / 引理 `isCompl_complement`

English:
lemma isCompl_complement
  given: (h : f.HasLeftInverse)
  statement: IsCompl f.range h.complement
  proof: h.closedComplemented_range.isCompl_complement

中文:
引理 isCompl_complement
  条件: (h : f.HasLeftInverse)
  结论: IsCompl f.range h.complement
  证明: h.closedComplemented_range.isCompl_complement

Depends on / 依赖: closedComplemented_range, h.closedComplemented_range.isCompl_complement, isCompl_complement
-/
lemma isCompl_complement (h : f.HasLeftInverse) : IsCompl f.range h.complement :=
  h.closedComplemented_range.isCompl_complement

end

end Ring

section

variable {R E F : Type*} [NontriviallyNormedField R]
  [NormedAddCommGroup E] [NormedSpace R E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace R F] [CompleteSpace F]

/--
lemma `of_injective_of_isClosed_range_of_closedComplement_range` / 引理 `of_injective_of_isClosed_range_of_closedComplement_range`

English:
lemma of_injective_of_isClosed_range_of_closedComplement_range
  statement: {f : E ->L[R] F}
  proof: by
  have : (f.rangeRestrict).ker = ⊥ := by
    rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf''
  refine ⟨(f.leftInverse_of_injective_of_isClosed_range hf hf').comp p, 

中文:
引理 of_injective_of_isClosed_range_of_closedComplement_range
  结论: {f : E ->L[R] F}
  证明: by
  have : (f.rangeRestrict).ker = ⊥ := by
    rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf''
  refine ⟨(f.leftInverse_of_injective_of_isClosed_range hf hf').comp p, 

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mpr, f.rangeRestrict, ker_codRestrict, ker_eq_bot, rangeRestrict
-/
lemma of_injective_of_isClosed_range_of_closedComplement_range {f : E ->L[R] F}
    (hf : Injective f) (hf' : IsClosed (range f)) (hf'' : Submodule.ClosedComplemented f.range) :
    f.HasLeftInverse := by
  have : (f.rangeRestrict).ker = ⊥ := by
    rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf''
  refine ⟨(f.leftInverse_of_injective_of_isClosed_range hf hf').comp p, fun x => ?_⟩
  simpa [hp ⟨f x, by simp⟩] using! f.rangeRestrict.leftInverse_apply_of_inj this x

end

end HasLeftInverse

namespace HasRightInverse

variable {f : E ->L[R] F}

/--
Definition of `rightInverse` / `rightInverse` 的定义

English:
definition rightInverse
  signature: (h : f.HasRightInverse)
  body: Classical.choose h

中文:
定义 rightInverse
  签名: (h : f.HasRightInverse)
  定义体: Classical.choose h

Depends on / 依赖: Classical, Classical.choose
-/
def rightInverse (h : f.HasRightInverse) : F ->L[R] E := Classical.choose h

/--
lemma `rightInverse_rightInverse` / 引理 `rightInverse_rightInverse`

English:
lemma rightInverse_rightInverse
  given: (h : f.HasRightInverse)
  statement: RightInverse h.rightInverse f
  proof: Classical.choose_spec h

中文:
引理 rightInverse_rightInverse
  条件: (h : f.HasRightInverse)
  结论: RightInverse h.rightInverse f
  证明: Classical.choose_spec h

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma rightInverse_rightInverse (h : f.HasRightInverse) : RightInverse h.rightInverse f :=
  Classical.choose_spec h

/--
lemma `surjective` / 引理 `surjective`

English:
lemma surjective
  given: (h : f.HasRightInverse)
  statement: Surjective f
  proof: h.rightInverse_rightInverse.surjective

中文:
引理 surjective
  条件: (h : f.HasRightInverse)
  结论: Surjective f
  证明: h.rightInverse_rightInverse.surjective

Depends on / 依赖: h.rightInverse_rightInverse.surjective, rightInverse_rightInverse, surjective
-/
lemma surjective (h : f.HasRightInverse) : Surjective f :=
  h.rightInverse_rightInverse.surjective

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {g : E ->L[R] F} (hf : f.HasRightInverse) (hfg : g = f)
  proof: hfg ▸ hf

中文:
引理 congr
  条件: {g : E ->L[R] F} (hf : f.HasRightInverse) (hfg : g = f)
  证明: hfg ▸ hf
-/
lemma congr {g : E ->L[R] F} (hf : f.HasRightInverse) (hfg : g = f) :
    g.HasRightInverse :=
  hfg ▸ hf

/--
lemma `_root_.ContinuousLinearEquiv.hasRightInverse` / 引理 `_root_.ContinuousLinearEquiv.hasRightInverse`

English:
lemma _root_.ContinuousLinearEquiv.hasRightInverse
  given: (f : E ≃L[R] F)
  proof: ⟨f.symm, rightInverse_of_comp (by simp)⟩

中文:
引理 _root_.ContinuousLinearEquiv.hasRightInverse
  条件: (f : E ≃L[R] F)
  证明: ⟨f.symm, rightInverse_of_comp (by simp)⟩

Depends on / 依赖: f.symm, rightInverse_of_comp
-/
lemma _root_.ContinuousLinearEquiv.hasRightInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasRightInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩

/--
lemma `_root_.ContinuousLinearEquiv.rightInverse_hasRightInverse` / 引理 `_root_.ContinuousLinearEquiv.rightInverse_hasRightInverse`

English:
lemma _root_.ContinuousLinearEquiv.rightInverse_hasRightInverse
  given: (f : E ≃L[R] F)
  proof: by
  ext y
exact f.injective by simpa using f.hasRightInverse.rightInverse_rightInverse y

中文:
引理 _root_.ContinuousLinearEquiv.rightInverse_hasRightInverse
  条件: (f : E ≃L[R] F)
  证明: by
  ext y
exact f.injective by simpa using f.hasRightInverse.rightInverse_rightInverse y
-/
@[simp] lemma _root_.ContinuousLinearEquiv.rightInverse_hasRightInverse (f : E ≃L[R] F) :
    f.hasRightInverse.rightInverse = f.symm := by
  ext y
exact f.injective by simpa using f.hasRightInverse.rightInverse_rightInverse y

/--
lemma `of_isInvertible` / 引理 `of_isInvertible`

English:
lemma of_isInvertible
  given: (hf : IsInvertible f)
  statement: f.HasRightInverse
  proof: by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasRightInverse

中文:
引理 of_isInvertible
  条件: (hf : IsInvertible f)
  结论: f.HasRightInverse
  证明: by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasRightInverse

Depends on / 依赖: e.hasRightInverse, hasRightInverse
-/
lemma of_isInvertible (hf : IsInvertible f) : f.HasRightInverse := by
  obtain ⟨e, rfl⟩ := hf
  exact e.hasRightInverse

/--
lemma `prodMap` / 引理 `prodMap`

English:
lemma prodMap
  given: {g : E' ->L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInverse)
  proof: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

中文:
引理 prodMap
  条件: {g : E' ->L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInverse)
  证明: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

Depends on / 依赖: finv.prodMap, prodMap
-/
lemma prodMap {g : E' ->L[R] F'} (hf : f.HasRightInverse) (hg : g.HasRightInverse) :
    (f.prodMap g).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  use finv.prodMap ginv
  simp [hfinv, hginv]

variable [TopologicalSpace G] [AddCommMonoid G] [Module R G]

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {g : F ->L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse)
  proof: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hfinv]; rw [hginv]

中文:
引理 comp
  条件: {g : F ->L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse)
  证明: by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hfinv]; rw [hginv]

Depends on / 依赖: comp_apply, finv.comp
-/
lemma comp {g : F ->L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) :
    (g.comp f).HasRightInverse := by
  obtain ⟨finv, hfinv⟩ := hf
  obtain ⟨ginv, hginv⟩ := hg
  refine ⟨finv.comp ginv, fun x => ?_⟩
  simp only [comp_apply]
  rw [hfinv]; rw [hginv]

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: {g : F ->L[R] G} (hfg : (g.comp f).HasRightInverse)
  proof: by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y => by simpa using hfginv y⟩

中文:
引理 of_comp
  条件: {g : F ->L[R] G} (hfg : (g.comp f).HasRightInverse)
  证明: by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y => by simpa using hfginv y⟩

Depends on / 依赖: f.comp, hfginv
-/
lemma of_comp {g : F ->L[R] G} (hfg : (g.comp f).HasRightInverse) :
    g.HasRightInverse := by
  obtain ⟨fginv, hfginv⟩ := hfg
  exact ⟨f.comp fginv, fun y => by simpa using hfginv y⟩

/--
lemma `comp_continuousLinearEquivalence` / 引理 `comp_continuousLinearEquivalence`

English:
lemma comp_continuousLinearEquivalence
  given: {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse)
  proof: hf.comp f₀.hasRightInverse

中文:
引理 comp_continuousLinearEquivalence
  条件: {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse)
  证明: hf.comp f₀.hasRightInverse

Depends on / 依赖: hasRightInverse, hf.comp
-/
lemma comp_continuousLinearEquivalence {f₀ : F' ≃L[R] E} (hf : f.HasRightInverse) :
    (f.comp f₀.toContinuousLinearMap).HasRightInverse :=
  hf.comp f₀.hasRightInverse

/--
lemma `continuousLinearEquivalence_comp` / 引理 `continuousLinearEquivalence_comp`

English:
lemma continuousLinearEquivalence_comp
  given: {g : F ≃L[R] F'} (hf : f.HasRightInverse)
  proof: g.hasRightInverse.comp hf

中文:
引理 continuousLinearEquivalence_comp
  条件: {g : F ≃L[R] F'} (hf : f.HasRightInverse)
  证明: g.hasRightInverse.comp hf

Depends on / 依赖: g.hasRightInverse.comp, hasRightInverse
-/
lemma continuousLinearEquivalence_comp {g : F ≃L[R] F'} (hf : f.HasRightInverse) :
    (g.toContinuousLinearMap.comp f).HasRightInverse :=
  g.hasRightInverse.comp hf

/--
lemma `fst` / 引理 `fst`

English:
lemma fst
  statement: (ContinuousLinearMap.fst R F G).HasRightInverse
  proof: by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp

中文:
引理 fst
  结论: (ContinuousLinearMap.fst R F G).HasRightInverse
  证明: by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp
-/
protected lemma fst : (ContinuousLinearMap.fst R F G).HasRightInverse := by
  use (ContinuousLinearMap.id _ _).prod 0
  intro x
  simp

/--
lemma `snd` / 引理 `snd`

English:
lemma snd
  statement: (ContinuousLinearMap.snd R F G).HasRightInverse
  proof: by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp

中文:
引理 snd
  结论: (ContinuousLinearMap.snd R F G).HasRightInverse
  证明: by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp
-/
protected lemma snd : (ContinuousLinearMap.snd R F G).HasRightInverse := by
  use ContinuousLinearMap.prod 0 (.id R G)
  intro x
  simp

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E ->L[𝕜] F}

/--
lemma `of_surjective_of_finiteDimensional` / 引理 `of_surjective_of_finiteDimensional`

English:
lemma of_surjective_of_finiteDimensional
  statement: [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  proof: by
  -- A surjective linear map has a linear inverse, which is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x => c

中文:
引理 of_surjective_of_finiteDimensional
  结论: [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
  证明: by
  -- A surjective linear map has a linear inverse, which is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x => c
-/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Surjective f) :
    f.HasRightInverse := by
  -- A surjective linear map has a linear inverse, which is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x => congr($hg x)⟩

end NontriviallyNormedField

end HasRightInverse

end ContinuousLinearMap

end
