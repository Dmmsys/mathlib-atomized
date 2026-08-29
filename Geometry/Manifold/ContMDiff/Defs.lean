/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# `C^n` functions between manifolds

We define `Cⁿ` functions between manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions. Here, `n` can be finite, or `∞`, or `ω`.

## Main definitions and statements

Let `M` and `M'` be two manifolds, with respect to models with corners `I` and `I'`. Let
`f : M → M'`.

* `ContMDiffWithinAt I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `ContMDiffAt I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `ContMDiffOn I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `ContMDiff I I' n f` states that the function `f` is `Cⁿ`.

We also give some basic properties of `Cⁿ` functions between manifolds, following the API of
`C^n` functions between vector spaces.
See `Basic.lean` for further basic properties of `Cⁿ` functions between manifolds,
`NormedSpace.lean` for the equivalence of manifold-smoothness to usual smoothness,
`Product.lean` for smoothness results related to the product of manifolds and
`Atlas.lean` for smoothness of atlas members and local structomorphisms.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the `Cⁿ` groupoid. We take advantage of the
general machinery developed in `LocalInvariantProperties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `liftPropWithinAt_indep_chart`.

For this to work, the definition of `ContMDiffWithinAt` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `contMDiffOn_iff` and `contMDiff_iff`.
-/

@[expose] public section


open Set Function Filter ChartedSpace IsManifold

open scoped Topology Manifold ContDiff

/-! ### Definition of `Cⁿ` functions between manifolds -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- Prerequisite typeclasses to say that `M` is a manifold over the pair `(E, H)`
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Prerequisite typeclasses to say that `M'` is a manifold over the pair `(E', H')`
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- Prerequisite typeclasses to say that `M''` is a manifold over the pair `(E'', H'')`
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H} {e' : OpenPartialHomeomorph M' H'}
  {f f₁ : M -> M'} {s s₁ t : Set M} {x x' : M} {y : M'} {m n : Nat∞ω}

variable (I I') in
/--
Definition of `ContDiffWithinAtProp` / `ContDiffWithinAtProp` 的定义

English:
definition ContDiffWithinAtProp
  signature: (n : Nat∞ω) (f : H -> H') (s : Set H) (x : H)
  body: ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x)

中文:
定义 ContDiffWithinAtProp
  签名: (n : 自然数∞ω) (f : H -> H') (s : 集合 H) (x : H)
  定义体: ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x)

Depends on / 依赖: AddCommGroup, ContDiffWithinAt, I.symm, Module, Module.complexToReal, complexToReal
-/
def ContDiffWithinAtProp (n : Nat∞ω) (f : H -> H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x)

/--
theorem `contDiffWithinAtProp_self_source` / 定理 `contDiffWithinAtProp_self_source`

English:
theorem contDiffWithinAtProp_self_source
  given: {f : E -> H'} {s : Set E} {x : E}
  proof: by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

中文:
定理 contDiffWithinAtProp_self_source
  条件: {f : E -> H'} {s : 集合 E} {x : E}
  证明: by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

Depends on / 依赖: Algebra, Algebra.complexToReal, CompTriple, CompTriple.comp_eq, ContDiffWithinAtProp, Semiring, comp_eq, complexToReal, id_eq, inter_univ, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, preimage_id_eq, range_id, simp_rw
-/
theorem contDiffWithinAtProp_self_source {f : E -> H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

/--
theorem `contDiffWithinAtProp_self` / 定理 `contDiffWithinAtProp_self`

English:
theorem contDiffWithinAtProp_self
  given: {f : E -> E'} {s : Set E} {x : E}
  proof: contDiffWithinAtProp_self_source

中文:
定理 contDiffWithinAtProp_self
  条件: {f : E -> E'} {s : 集合 E} {x : E}
  证明: contDiffWithinAtProp_self_source

Depends on / 依赖: contDiffWithinAtProp_self_source
-/
theorem contDiffWithinAtProp_self {f : E -> E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source

/--
theorem `contDiffWithinAtProp_self_target` / 定理 `contDiffWithinAtProp_self_target`

English:
theorem contDiffWithinAtProp_self_target
  given: {f : H -> E'} {s : Set H} {x : H}
  proof: Iff.rfl

中文:
定理 contDiffWithinAtProp_self_target
  条件: {f : H -> E'} {s : 集合 H} {x : H}
  证明: Iff.rfl

Depends on / 依赖: AddCommGroup, Iff.rfl, Module, SMulCommClass, SMulCommClass.complexToReal, complexToReal
-/
theorem contDiffWithinAtProp_self_target {f : H -> E'} {s : Set H} {x : H} :
    ContDiffWithinAtProp I 𝓘(𝕜, E') n f s x ↔
      ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s inter range I) (I x) :=
  Iff.rfl

/--
theorem `contDiffWithinAt_localInvariantProp_of_le` / 定理 `contDiffWithinAt_localInvariantProp_of_le`

English:
theorem contDiffWithinAt_localInvariantProp_of_le
  given: (n m : Nat∞ω) (hmn : m <= n)
  proof: by
    have : I.symm ⁻¹' (s inter u) inter range I = I.symm ⁻¹' s inter range I inter I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp]; rw [ContDiffWithinAtProp]; rw [this]
    symm
    apply contDiffWithinAt_inter
    have : u in 𝓝 (I.symm (I x)) :

中文:
定理 contDiffWithinAt_localInvariantProp_of_le
  条件: (n m : 自然数∞ω) (hmn : m <= n)
  证明: by
    have : I.symm ⁻¹' (s inter u) inter range I = I.symm ⁻¹' s inter range I inter I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp]; rw [ContDiffWithinAtProp]; rw [this]
    symm
    apply contDiffWithinAt_inter
    have : u in 𝓝 (I.symm (I x)) :

Depends on / 依赖: ContDiffWithinAtProp, ContinuousAt, ContinuousAt.preimage_mem_nhds, I.continuous_symm.continuousAt, I.symm, ModelWithCorners, ModelWithCorners.left_inv, contDiffWithinAt_inter, continuousAt, continuous_symm, inter_right_comm, left_inv, mem_nhds, preimage_inter, preimage_mem_nhds, right_invariance, u_open, u_open.mem_nhds
-/
theorem contDiffWithinAt_localInvariantProp_of_le (n m : Nat∞ω) (hmn : m <= n) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' m) where
  is_local {s x u f} u_open xu := by
    have : I.symm ⁻¹' (s inter u) inter range I = I.symm ⁻¹' s inter range I inter I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp]; rw [ContDiffWithinAtProp]; rw [this]
    symm
    apply contDiffWithinAt_inter
    have : u in 𝓝 (I.symm (I x)) := by
      rw [ModelWithCorners.left_inv]
      exact u_open.mem_nhds xu
    apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuousAt this
  right_invariance' {s x f e} he hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
    rw [this] at h
    have : I (e x) in I.symm ⁻¹' e.target inter range I := by simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
    convert! (h.comp_inter _ (this.of_le hmn)).mono_of_mem_nhdsWithin _ using 1
    · ext y; simp only [mfld_simps]
    refine mem_nhdsWithin.mpr
      ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
    mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [h, hy, mfld_simps]
    · simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have A : (I' ∘ f ∘ I.symm) (I x) in I'.symm ⁻¹' e'.source inter range I' := by
      simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
    convert! (this.of_le hmn).comp _ h _
    · ext y; simp only [mfld_simps]
    · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1

/--
theorem `contDiffWithinAt_localInvariantProp` / 定理 `contDiffWithinAt_localInvariantProp`

English:
theorem contDiffWithinAt_localInvariantProp
  given: (n : Nat∞ω)
  proof: contDiffWithinAt_localInvariantProp_of_le n n le_rfl

中文:
定理 contDiffWithinAt_localInvariantProp
  条件: (n : 自然数∞ω)
  证明: contDiffWithinAt_localInvariantProp_of_le n n le_rfl

Depends on / 依赖: AddCommGroup, StarModule, StarModule.complexToReal, complexToReal, contDiffWithinAt_localInvariantProp_of_le, le_rfl
-/
theorem contDiffWithinAt_localInvariantProp (n : Nat∞ω) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' n) :=
  contDiffWithinAt_localInvariantProp_of_le n n le_rfl

/--
theorem `contDiffWithinAtProp_mono_of_mem_nhdsWithin` / 定理 `contDiffWithinAtProp_mono_of_mem_nhdsWithin`

English:
theorem contDiffWithinAtProp_mono_of_mem_nhdsWithin
  proof: by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]

中文:
定理 contDiffWithinAtProp_mono_of_mem_nhdsWithin
  证明: by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]

Depends on / 依赖: Filter, Filter.mem_map, I.image_eq, I.symm_map_nhdsWithin_image, h.mono_of_mem_nhdsWithin, image_eq, inter_mem, inter_subset_right, mem_map, mem_of_superset, mono_of_mem_nhdsWithin, self_mem_nhdsWithin, symm_map_nhdsWithin_image
-/
theorem contDiffWithinAtProp_mono_of_mem_nhdsWithin
    (n : Nat∞ω) ⦃s x t⦄ ⦃f : H -> H'⦄ (hts : s in 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]

/--
theorem `contDiffWithinAtProp_id` / 定理 `contDiffWithinAtProp_id`

English:
theorem contDiffWithinAtProp_id
  given: (x : H)
  statement: ContDiffWithinAtProp I I n id univ x
  proof: by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]

中文:
定理 contDiffWithinAtProp_id
  条件: (x : H)
  结论: ContDiffWithinAtProp I I n id univ x
  证明: by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAtProp, ModelWithCorners, ModelWithCorners.right_inv, contDiffAt, contDiffWithinAt, contDiff_id, contDiff_id.contDiffAt.contDiffWithinAt, id_comp, mfld_simps, preimage_univ, right_inv, this.congr, univ_inter
-/
theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]

variable (I I') in
/--
Definition of `ContMDiffWithinAt` / `ContMDiffWithinAt` 的定义

English:
definition ContMDiffWithinAt
  signature: (n : Nat∞ω) (f : M -> M') (s : Set M) (x : M)
  body: LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

中文:
定义 ContMDiffWithinAt
  签名: (n : 自然数∞ω) (f : M -> M') (s : 集合 M) (x : M)
  定义体: LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

Depends on / 依赖: ContDiffWithinAtProp, LiftPropWithinAt
-/
def ContMDiffWithinAt (n : Nat∞ω) (f : M -> M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

variable (I I') in
/--
Definition of `ContMDiffAt` / `ContMDiffAt` 的定义

English:
definition ContMDiffAt
  signature: (n : Nat∞ω) (f : M -> M') (x : M)
  body: ContMDiffWithinAt I I' n f univ x

中文:
定义 ContMDiffAt
  签名: (n : 自然数∞ω) (f : M -> M') (x : M)
  定义体: ContMDiffWithinAt I I' n f univ x

Depends on / 依赖: ContMDiffWithinAt
-/
def ContMDiffAt (n : Nat∞ω) (f : M -> M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x

/--
theorem `contMDiffAt_iff` / 定理 `contMDiffAt_iff`

English:
theorem contMDiffAt_iff
  given: {n : Nat∞ω} {f : M -> M'} {x : M}
  proof: liftPropAt_iff.trans by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

中文:
定理 contMDiffAt_iff
  条件: {n : 自然数∞ω} {f : M -> M'} {x : M}
  证明: liftPropAt_iff.trans by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

Depends on / 依赖: ContDiffWithinAtProp, liftPropAt_iff, liftPropAt_iff.trans, preimage_univ, univ_inter
-/
theorem contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
liftPropAt_iff.trans by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

variable (I I') in
/--
Definition of `ContMDiffOn` / `ContMDiffOn` 的定义

English:
definition ContMDiffOn
  signature: (n : Nat∞ω) (f : M -> M') (s : Set M)
  body: forall x in s, ContMDiffWithinAt I I' n f s x

中文:
定义 ContMDiffOn
  签名: (n : 自然数∞ω) (f : M -> M') (s : 集合 M)
  定义体: forall x in s, ContMDiffWithinAt I I' n f s x

Depends on / 依赖: ContMDiffWithinAt
-/
def ContMDiffOn (n : Nat∞ω) (f : M -> M') (s : Set M) :=
  forall x in s, ContMDiffWithinAt I I' n f s x

variable (I I') in
/--
Definition of `ContMDiff` / `ContMDiff` 的定义

English:
definition ContMDiff
  signature: (n : Nat∞ω) (f : M -> M')
  body: forall x, ContMDiffAt I I' n f x

中文:
定义 ContMDiff
  签名: (n : 自然数∞ω) (f : M -> M')
  定义体: forall x, ContMDiffAt I I' n f x

Depends on / 依赖: ContMDiffAt
-/
def ContMDiff (n : Nat∞ω) (f : M -> M') :=
  forall x, ContMDiffAt I I' n f x


/--
theorem `ContMDiffWithinAt.of_le` / 定理 `ContMDiffWithinAt.of_le`

English:
theorem ContMDiffWithinAt.of_le
  given: (hf : ContMDiffWithinAt I I' n f s x) (le : m <= n)
  proof: by
  simp only [ContMDiffWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩

中文:
定理 ContMDiffWithinAt.of_le
  条件: (hf : ContMDiffWithinAt I I' n f s x) (le : m <= n)
  证明: by
  simp only [ContMDiffWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩

Depends on / 依赖: ContMDiffWithinAt, mod_cast, of_le
-/
theorem ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m <= n) :
    ContMDiffWithinAt I I' m f s x := by
  simp only [ContMDiffWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩

/--
theorem `ContMDiffAt.of_le` / 定理 `ContMDiffAt.of_le`

English:
theorem ContMDiffAt.of_le
  given: (hf : ContMDiffAt I I' n f x) (le : m <= n)
  statement: ContMDiffAt I I' m f x
  proof: ContMDiffWithinAt.of_le hf le

中文:
定理 ContMDiffAt.of_le
  条件: (hf : ContMDiffAt I I' n f x) (le : m <= n)
  结论: ContMDiffAt I I' m f x
  证明: ContMDiffWithinAt.of_le hf le

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.of_le, of_le
-/
theorem ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m <= n) : ContMDiffAt I I' m f x :=
  ContMDiffWithinAt.of_le hf le

/--
theorem `ContMDiffOn.of_le` / 定理 `ContMDiffOn.of_le`

English:
theorem ContMDiffOn.of_le
  given: (hf : ContMDiffOn I I' n f s) (le : m <= n)
  statement: ContMDiffOn I I' m f s
  proof: fun x hx => (hf x hx).of_le le

中文:
定理 ContMDiffOn.of_le
  条件: (hf : ContMDiffOn I I' n f s) (le : m <= n)
  结论: ContMDiffOn I I' m f s
  证明: fun x hx => (hf x hx).of_le le

Depends on / 依赖: of_le
-/
theorem ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m <= n) : ContMDiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le

/--
theorem `ContMDiff.of_le` / 定理 `ContMDiff.of_le`

English:
theorem ContMDiff.of_le
  given: (hf : ContMDiff I I' n f) (le : m <= n)
  statement: ContMDiff I I' m f
  proof: fun x =>
  (hf x).of_le le

中文:
定理 ContMDiff.of_le
  条件: (hf : ContMDiff I I' n f) (le : m <= n)
  结论: ContMDiff I I' m f
  证明: fun x =>
  (hf x).of_le le
-/
theorem ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n) : ContMDiff I I' m f := fun x =>
  (hf x).of_le le


/--
theorem `ContMDiff.contMDiffAt` / 定理 `ContMDiff.contMDiffAt`

English:
theorem ContMDiff.contMDiffAt
  given: (h : ContMDiff I I' n f)
  statement: ContMDiffAt I I' n f x
  proof: h x

中文:
定理 ContMDiff.contMDiffAt
  条件: (h : ContMDiff I I' n f)
  结论: ContMDiffAt I I' n f x
  证明: h x
-/
theorem ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : ContMDiffAt I I' n f x :=
  h x

/--
theorem `contMDiffWithinAt_univ` / 定理 `contMDiffWithinAt_univ`

English:
theorem contMDiffWithinAt_univ
  statement: ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x
  proof: Iff.rfl

@[simp]

中文:
定理 contMDiffWithinAt_univ
  结论: ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem contMDiffWithinAt_univ : ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x :=
  Iff.rfl

@[simp]
/--
theorem `contMDiffOn_empty` / 定理 `contMDiffOn_empty`

English:
theorem contMDiffOn_empty
  statement: ContMDiffOn I I' n f ∅
  proof: fun _x hx => hx.elim

中文:
定理 contMDiffOn_empty
  结论: ContMDiffOn I I' n f ∅
  证明: fun _x hx => hx.elim

Depends on / 依赖: hx.elim
-/
theorem contMDiffOn_empty : ContMDiffOn I I' n f ∅ := fun _x hx => hx.elim

/--
theorem `contMDiffOn_univ` / 定理 `contMDiffOn_univ`

English:
theorem contMDiffOn_univ
  statement: ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f
  proof: by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]

中文:
定理 contMDiffOn_univ
  结论: ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f
  证明: by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]

Depends on / 依赖: ContMDiff, ContMDiffOn, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ
-/
theorem contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f := by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]

/--
theorem `contMDiffWithinAt_iff` / 定理 `contMDiffWithinAt_iff`

English:
theorem contMDiffWithinAt_iff
  proof: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl

中文:
定理 contMDiffWithinAt_iff
  证明: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl

Depends on / 依赖: ContMDiffWithinAt, liftPropWithinAt_iff, simp_rw
-/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl

/--
theorem `contMDiffWithinAt_iff'` / 定理 `contMDiffWithinAt_iff'`

English:
theorem contMDiffWithinAt_iff'
  proof: by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => contDiffWithinAt_congr_set
    hc.extChartAt_symm_preimage_inter_range_eventuallyEq

中文:
定理 contMDiffWithinAt_iff'
  证明: by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => contDiffWithinAt_congr_set
    hc.extChartAt_symm_preimage_inter_range_eventuallyEq

Depends on / 依赖: ContMDiffWithinAt, and_congr_right, contDiffWithinAt_congr_set, extChartAt_symm_preimage_inter_range_eventuallyEq, hc.extChartAt_symm_preimage_inter_range_eventuallyEq, liftPropWithinAt_iff
-/
theorem contMDiffWithinAt_iff' :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target inter
            (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => contDiffWithinAt_congr_set
    hc.extChartAt_symm_preimage_inter_range_eventuallyEq

/--
theorem `contMDiffWithinAt_iff_target` / 定理 `contMDiffWithinAt_iff_target`

English:
theorem contMDiffWithinAt_iff_target
  proof: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWi

中文:
定理 contMDiffWithinAt_iff_target
  证明: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWi

Depends on / 依赖: ContDiffWithinAtProp, ContMDiffWithinAt, ContinuousWithinAt, ModelWithCorners, ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomo, OpenPartialHomeomorph, OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.extend, PartialEquiv, PartialEquiv.coe_trans, and_assoc, and_iff_left_of_imp, chartAt_self_eq, coe_toPartialEquiv, coe_trans, comp_continuousWithinAt, continuousAt_extChartAt, extChartAt, extend
-/
theorem contMDiffWithinAt_iff_target :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, id_comp]
  rfl

/--
theorem `contMDiffAt_iff_target` / 定理 `contMDiffAt_iff_target`

English:
theorem contMDiffAt_iff_target
  given: {x : M}
  proof: by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target]; rw [continuousWithinAt_univ]

中文:
定理 contMDiffAt_iff_target
  条件: {x : M}
  证明: by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target]; rw [continuousWithinAt_univ]

Depends on / 依赖: ContMDiffAt, contMDiffWithinAt_iff_target, continuousWithinAt_univ
-/
theorem contMDiffAt_iff_target {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x := by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target]; rw [continuousWithinAt_univ]

/--
theorem `continuousWithinAt_iff_source` / 定理 `continuousWithinAt_iff_source`

English:
theorem continuousWithinAt_iff_source
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply h.comp_of_eq
    · exact (continuousAt_extChartAt_symm x).continuousWithinAt
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
    · exact extChartAt_to_inv x
  · rw [← continuousWithinAt_inter (extChartAt_source_mem_nhds (I := I) x)]
    

中文:
定理 continuousWithinAt_iff_source
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply h.comp_of_eq
    · exact (continuousAt_extChartAt_symm x).continuousWithinAt
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
    · exact extChartAt_to_inv x
  · rw [← continuousWithinAt_inter (extChartAt_source_mem_nhds (I := I) x)]
    

Depends on / 依赖: ContinuousWithinAt, chartAt, comp_of_eq, continuousAt_extChartAt, continuousAt_extChartAt_symm, continuousWithinAt, continuousWithinAt_inter, extChartAt, extChartAt_source_mem_nhds, extChartAt_to_inv, h.comp, h.comp_of_eq, inter_subset_left, mapsTo_preimage, mono_left, source
-/
theorem continuousWithinAt_iff_source :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply h.comp_of_eq
    · exact (continuousAt_extChartAt_symm x).continuousWithinAt
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
    · exact extChartAt_to_inv x
  · rw [← continuousWithinAt_inter (extChartAt_source_mem_nhds (I := I) x)]
    have : ContinuousWithinAt ((f ∘ ↑(extChartAt I x).symm) ∘ ↑(extChartAt I x))
        (s inter (extChartAt I x).source) x := by
      apply h.comp (continuousAt_extChartAt x).continuousWithinAt
      intro y hy
      have : (chartAt H x).symm ((chartAt H x) y) = y :=
        OpenPartialHomeomorph.left_inv _ (by simpa using hy.2)
      simpa [this] using hy.1
    apply this.congr
    · intro y hy
      have : (chartAt H x).symm ((chartAt H x) y) = y :=
        OpenPartialHomeomorph.left_inv _ (by simpa using hy.2)
      simp [this]
    · simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `contMDiffWithinAt_iff_source` / 定理 `contMDiffWithinAt_iff_source`

English:
theorem contMDiffWithinAt_iff_source
  proof: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← continuousWithinAt_iff_source]
  simp only [ContDiffWithinAtProp, mfld_simps, preimage_comp, comp_assoc]

中文:
定理 contMDiffWithinAt_iff_source
  证明: by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← continuousWithinAt_iff_source]
  simp only [ContDiffWithinAtProp, mfld_simps, preimage_comp, comp_assoc]

Depends on / 依赖: ContDiffWithinAtProp, ContMDiffWithinAt, comp_assoc, continuousWithinAt_iff_source, liftPropWithinAt_iff, mfld_simps, preimage_comp, simp_rw
-/
theorem contMDiffWithinAt_iff_source :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← continuousWithinAt_iff_source]
  simp only [ContDiffWithinAtProp, mfld_simps, preimage_comp, comp_assoc]

/--
theorem `contMDiffAt_iff_source` / 定理 `contMDiffAt_iff_source`

English:
theorem contMDiffAt_iff_source
  proof: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_source]
  simp

中文:
定理 contMDiffAt_iff_source
  证明: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_source]
  simp

Depends on / 依赖: contMDiffWithinAt_iff_source, contMDiffWithinAt_univ
-/
theorem contMDiffAt_iff_source :
    ContMDiffAt I I' n f x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_source]
  simp

section IsManifold

/--
theorem `contMDiffWithinAt_iff_source_of_mem_maximalAtlas` / 定理 `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`

English:
theorem contMDiffWithinAt_iff_source_of_mem_maximalAtlas
  proof: by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtPr

中文:
定理 contMDiffWithinAt_iff_source_of_mem_maximalAtlas
  证明: by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtPr

Depends on / 依赖: ContDiffWithinAtProp, ContMDiffWithinAt, Function, Function.comp, StructureGroupoid, StructureGroupoid.liftPropWithinAt_self_source, contDiffWithinAtProp_self_source, contDiffWithinAt_localInvariantProp, e.extend, e.extend_source, e.extend_symm_continuousWithinAt_comp_right_iff, e.left_inv, extend, extend_source, extend_symm_continuousWithinAt_comp_right_iff, left_inv, liftPropWithinAt_indep_chart_source, liftPropWithinAt_self_source, simp_rw
-/
theorem contMDiffWithinAt_iff_source_of_mem_maximalAtlas
    (he : e in maximalAtlas I n M) (hx : x in e.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s inter range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtProp_self_source,
    ContDiffWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

/--
theorem `contMDiffWithinAt_iff_source_of_mem_source` / 定理 `contMDiffWithinAt_iff_source_of_mem_source`

English:
theorem contMDiffWithinAt_iff_source_of_mem_source
  proof: contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

中文:
定理 contMDiffWithinAt_iff_source_of_mem_source
  证明: contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffWithinAt_iff_source_of_mem_maximalAtlas
-/
theorem contMDiffWithinAt_iff_source_of_mem_source
    [IsManifold I n M] (hx' : x' in (chartAt H x).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

/--
theorem `contMDiffAt_iff_source_of_mem_source` / 定理 `contMDiffAt_iff_source_of_mem_source`

English:
theorem contMDiffAt_iff_source_of_mem_source
  proof: by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]

中文:
定理 contMDiffAt_iff_source_of_mem_source
  证明: by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]

Depends on / 依赖: ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source, preimage_univ, simp_rw, univ_inter
-/
theorem contMDiffAt_iff_source_of_mem_source
    [IsManifold I n M] (hx' : x' in (chartAt H x).source) :
    ContMDiffAt I I' n f x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x') := by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]

/--
theorem `contMDiffWithinAt_iff_target_of_mem_maximalAtlas` / 定理 `contMDiffWithinAt_iff_target_of_mem_maximalAtlas`

English:
theorem contMDiffWithinAt_iff_target_of_mem_maximalAtlas
  proof: by
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_target he' hx]
  apply and_congr_right (fun h => ?_)
  have A : ContinuousWithinAt ((e'.extend I') ∘ f) s x :=
    (e'.continuousAt_extend hx).comp_continuousWithinAt h
  have A' : ContinuousWit

中文:
定理 contMDiffWithinAt_iff_target_of_mem_maximalAtlas
  证明: by
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_target he' hx]
  apply and_congr_right (fun h => ?_)
  have A : ContinuousWithinAt ((e'.extend I') ∘ f) s x :=
    (e'.continuousAt_extend hx).comp_continuousWithinAt h
  have A' : ContinuousWit

Depends on / 依赖: ContDiffWithinAtProp, ContMDiffWithinAt, ContinuousWithinAt, StructureGroupoid, StructureGroupoid.liftPropWithinAt_self_target, and_congr_right, comp_assoc, comp_continuousWithinAt, contDiffWithinAt_localInvariantProp, continuousAt, continuousAt_extend, extend, liftPropWithinAt_indep_chart_target, liftPropWithinAt_self_target, simp_rw
-/
theorem contMDiffWithinAt_iff_target_of_mem_maximalAtlas
    (he' : e' in maximalAtlas I' n M') (hx : f x in e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n ((e'.extend I') ∘ f) s x := by
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart_target he' hx]
  apply and_congr_right (fun h => ?_)
  have A : ContinuousWithinAt ((e'.extend I') ∘ f) s x :=
    (e'.continuousAt_extend hx).comp_continuousWithinAt h
  have A' : ContinuousWithinAt (e' ∘ f) s x := (e'.continuousAt hx).comp_continuousWithinAt h
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target, A, A']
  simp [ContDiffWithinAtProp, comp_assoc]

/--
theorem `contMDiffWithinAt_iff_target_of_mem_source` / 定理 `contMDiffWithinAt_iff_target_of_mem_source`

English:
theorem contMDiffWithinAt_iff_target_of_mem_source
  statement: [IsManifold I' n M']
  proof: contMDiffWithinAt_iff_target_of_mem_maximalAtlas (chart_mem_maximalAtlas _) hy

中文:
定理 contMDiffWithinAt_iff_target_of_mem_source
  结论: [是流形 I' n M']
  证明: contMDiffWithinAt_iff_target_of_mem_maximalAtlas (chart_mem_maximalAtlas _) hy

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffWithinAt_iff_target_of_mem_maximalAtlas
-/
theorem contMDiffWithinAt_iff_target_of_mem_source [IsManifold I' n M']
    (hy : f x in (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x :=
  contMDiffWithinAt_iff_target_of_mem_maximalAtlas (chart_mem_maximalAtlas _) hy

/--
theorem `contMDiffAt_iff_target_of_mem_source` / 定理 `contMDiffAt_iff_target_of_mem_source`

English:
theorem contMDiffAt_iff_target_of_mem_source
  statement: [IsManifold I' n M']
  proof: by
  rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [ContMDiffAt]

中文:
定理 contMDiffAt_iff_target_of_mem_source
  结论: [是流形 I' n M']
  证明: by
  rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [ContMDiffAt]

Depends on / 依赖: ContMDiffAt, contMDiffWithinAt_iff_target_of_mem_source, continuousWithinAt_univ
-/
theorem contMDiffAt_iff_target_of_mem_source [IsManifold I' n M']
    (hy : f x in (chartAt H' y).source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) x := by
  rw [ContMDiffAt]; rw [contMDiffWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [ContMDiffAt]

/--
theorem `contMDiffWithinAt_iff_of_mem_maximalAtlas` / 定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas`

English:
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas
  statement: (he : e in maximalAtlas I n M)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart he hx he' hy

中文:
定理 contMDiffWithinAt_iff_of_mem_maximalAtlas
  结论: (he : e in maximalAtlas I n M)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart he hx he' hy

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_indep_chart
-/
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I' n M') (hx : x in e.source) (hy : f x in e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s inter range I) (e.extend I x) :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_indep_chart he hx he' hy

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `contMDiffWithinAt_iff_of_mem_maximalAtlas'` / 定理 `contMDiffWithinAt_iff_of_mem_maximalAtlas'`

English:
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas'
  proof: by
  rw [contMDiffWithinAt_iff_source]; rw [contMDiffWithinAt_iff_target_of_mem_maximalAtlas he' (by simpa)]
  apply and_congr continuousWithinAt_iff_source.symm
  -- TODO: this is `contMDiffWithinAt_iff_contDiffWithinAt` copied,
  -- which is not put here for import reasons
  simp +contextual only 

中文:
定理 contMDiffWithinAt_iff_of_mem_maximalAtlas'
  证明: by
  rw [contMDiffWithinAt_iff_source]; rw [contMDiffWithinAt_iff_target_of_mem_maximalAtlas he' (by simpa)]
  apply and_congr continuousWithinAt_iff_source.symm
  -- TODO: this is `contMDiffWithinAt_iff_contDiffWithinAt` copied,
  -- which is not put here for import reasons
  simp +contextual only 

Depends on / 依赖: and_congr, contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_target_of_mem_maximalAtlas, continuousWithinAt_iff_source, continuousWithinAt_iff_source.symm
-/
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas'
    (he' : e' in maximalAtlas I' n M') (hy : f x in e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  rw [contMDiffWithinAt_iff_source]; rw [contMDiffWithinAt_iff_target_of_mem_maximalAtlas he' (by simpa)]
  apply and_congr continuousWithinAt_iff_source.symm
  -- TODO: this is `contMDiffWithinAt_iff_contDiffWithinAt` copied,
  -- which is not put here for import reasons
  simp +contextual only [ContMDiffWithinAt, liftPropWithinAt_iff',
    ContDiffWithinAtProp, iff_def, mfld_simps]
  exact ContDiffWithinAt.continuousWithinAt

/--
theorem `contMDiffWithinAt_iff_image` / 定理 `contMDiffWithinAt_iff_image`

English:
theorem contMDiffWithinAt_iff_image
  proof: by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_set ?_
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

中文:
定理 contMDiffWithinAt_iff_image
  证明: by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_set ?_
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

Depends on / 依赖: and_congr_right_iff, contDiffWithinAt_congr_set, contMDiffWithinAt_iff_of_mem_maximalAtlas, e.extend_symm_preimage_inter_range_eventuallyEq, extend_symm_preimage_inter_range_eventuallyEq, simp_rw
-/
theorem contMDiffWithinAt_iff_image
    (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I' n M')
    (hs : s subseteq e.source) (hx : x in e.source) (hy : f x in e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_set ?_
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

/--
theorem `contMDiffAt_iff_of_mem_maximalAtlas` / 定理 `contMDiffAt_iff_of_mem_maximalAtlas`

English:
theorem contMDiffAt_iff_of_mem_maximalAtlas
  statement: {x : M} (he : e in maximalAtlas I n M)
  proof: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

中文:
定理 contMDiffAt_iff_of_mem_maximalAtlas
  结论: {x : M} (he : e in maximalAtlas I n M)
  证明: by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

Depends on / 依赖: contMDiffWithinAt_iff_of_mem_maximalAtlas, contMDiffWithinAt_univ, continuousWithinAt_univ, preimage_univ, univ_inter
-/
theorem contMDiffAt_iff_of_mem_maximalAtlas {x : M} (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I' n M') (hx : x in e.source) (hy : f x in e'.source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (range I) (e.extend I x) := by
  rw [← contMDiffWithinAt_univ]; rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

/--
theorem `contMDiffWithinAt_iff_of_mem_source` / 定理 `contMDiffWithinAt_iff_of_mem_source`

English:
theorem contMDiffWithinAt_iff_of_mem_source
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

中文:
定理 contMDiffWithinAt_iff_of_mem_source
  结论: [是流形 I n M] [是流形 I' n M']
  证明: contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffWithinAt_iff_of_mem_maximalAtlas
-/
theorem contMDiffWithinAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M']
    (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

/--
theorem `contMDiffWithinAt_iff_of_mem_source'` / 定理 `contMDiffWithinAt_iff_of_mem_source'`

English:
theorem contMDiffWithinAt_iff_of_mem_source'
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_set ?_
  rw [← nhdsWithin_eq_iff_event

中文:
定理 contMDiffWithinAt_iff_of_mem_source'
  结论: [是流形 I n M] [是流形 I' n M']
  证明: by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_set ?_
  rw [← nhdsWithin_eq_iff_event

Depends on / 依赖: and_congr_right_iff, contDiffWithinAt_congr_set, contMDiffWithinAt_iff_of_mem_source, e.image_source_inter_eq, extChartAt, extChartAt_source, extChartAt_source_mem_nhds, image_source_inter_eq, inter_comm, map_extChartAt_nhdsWithin, map_extChartAt_nhdsWithin_eq_image, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_inter_of_mem
-/
theorem contMDiffWithinAt_iff_of_mem_source' [IsManifold I n M] [IsManifold I' n M']
    (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_set ?_
  rw [← nhdsWithin_eq_iff_eventuallyEq]; rw [← e.image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image' hx]; rw [← map_extChartAt_nhdsWithin' hx]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)

/--
theorem `contMDiffAt_iff_of_mem_source` / 定理 `contMDiffAt_iff_of_mem_source`

English:
theorem contMDiffAt_iff_of_mem_source
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: (contMDiffWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

中文:
定理 contMDiffAt_iff_of_mem_source
  结论: [是流形 I n M] [是流形 I' n M']
  证明: (contMDiffWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

Depends on / 依赖: contMDiffWithinAt_iff_of_mem_source, continuousWithinAt_univ, preimage_univ, univ_inter
-/
theorem contMDiffAt_iff_of_mem_source [IsManifold I n M] [IsManifold I' n M']
    (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    ContMDiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
(contMDiffWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

/--
theorem `contMDiffOn_iff_of_mem_maximalAtlas` / 定理 `contMDiffOn_iff_of_mem_maximalAtlas`

English:
theorem contMDiffOn_iff_of_mem_maximalAtlas
  statement: (he : e in maximalAtlas I n M)
  proof: by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)

中文:
定理 contMDiffOn_iff_of_mem_maximalAtlas
  结论: (he : e in maximalAtlas I n M)
  证明: by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)

Depends on / 依赖: ContDiffOn, ContMDiffOn, ContinuousOn, Set.forall_mem_image, contMDiffWithinAt_iff_image, forall_and, forall_mem_image, simp_rw
-/
theorem contMDiffOn_iff_of_mem_maximalAtlas (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I' n M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)

/--
theorem `contMDiffOn_iff_of_mem_maximalAtlas'` / 定理 `contMDiffOn_iff_of_mem_maximalAtlas'`

English:
theorem contMDiffOn_iff_of_mem_maximalAtlas'
  statement: (he : e in maximalAtlas I n M)
  proof: (contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

中文:
定理 contMDiffOn_iff_of_mem_maximalAtlas'
  结论: (he : e in maximalAtlas I n M)
  证明: (contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

Depends on / 依赖: and_iff_right_of_imp, contMDiffOn_iff_of_mem_maximalAtlas, continuousOn, continuousOn_writtenInExtend_iff, e.continuousOn_writtenInExtend_iff, h.continuousOn
-/
theorem contMDiffOn_iff_of_mem_maximalAtlas' (he : e in maximalAtlas I n M)
    (he' : e' in maximalAtlas I' n M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
(contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

/--
theorem `contMDiffOn_iff_of_subset_source` / 定理 `contMDiffOn_iff_of_subset_source`

English:
theorem contMDiffOn_iff_of_subset_source
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hs
    h2s

中文:
定理 contMDiffOn_iff_of_subset_source
  结论: [是流形 I n M] [是流形 I' n M']
  证明: contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hs
    h2s

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffOn_iff_of_mem_maximalAtlas
-/
theorem contMDiffOn_iff_of_subset_source [IsManifold I n M] [IsManifold I' n M']
    (hs : s subseteq (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y) hs
    h2s

/--
theorem `contMDiffOn_iff_of_subset_source'` / 定理 `contMDiffOn_iff_of_subset_source'`

English:
theorem contMDiffOn_iff_of_subset_source'
  statement: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

中文:
定理 contMDiffOn_iff_of_subset_source'
  结论: [是流形 I n M] [是流形 I' n M']
  证明: by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

Depends on / 依赖: chart_mem_maximalAtlas, contMDiffOn_iff_of_mem_maximalAtlas, extChartAt_source
-/
theorem contMDiffOn_iff_of_subset_source' [IsManifold I n M] [IsManifold I' n M']
    (hs : s subseteq (extChartAt I x).source) (h2s : MapsTo f s (extChartAt I' y).source) :
    ContMDiffOn I I' n f s ↔
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/--
theorem `contMDiffOn_iff` / 定理 `contMDiffOn_iff`

English:
theorem contMDiffOn_iff
  given: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfl

中文:
定理 contMDiffOn_iff
  条件: [是流形 I n M] [是流形 I' n M']
  证明: by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfl

Depends on / 依赖: chartAt, contMDiffWithinAt_iff_of_mem_source, convert, extChartAt, mfld_set_tac, mfld_simps, source, specialize
-/
theorem contMDiffOn_iff [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        forall (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target inter
              (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w in (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((contMDiffWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [ContDiffWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

/--
theorem `contMDiffOn_zero_iff` / 定理 `contMDiffOn_zero_iff`

English:
theorem contMDiffOn_zero_iff
  statement: ContMDiffOn I I' 0 f s ↔ ContinuousOn f s
  proof: by
  rw [contMDiffOn_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x y
  rw [contDiffOn_zero]
  apply (continuousOn_extChartAt _).comp
  · apply h.comp ((continuousOn_extChartAt_symm _).mono inter_subset_left) (fun z hz => ?_)
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at h

中文:
定理 contMDiffOn_zero_iff
  结论: ContMDiffOn I I' 0 f s ↔ ContinuousOn f s
  证明: by
  rw [contMDiffOn_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x y
  rw [contDiffOn_zero]
  apply (continuousOn_extChartAt _).comp
  · apply h.comp ((continuousOn_extChartAt_symm _).mono inter_subset_left) (fun z hz => ?_)
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at h

Depends on / 依赖: contDiffOn_zero, contMDiffOn_iff, continuousOn_extChartAt, continuousOn_extChartAt_symm, h.comp, inter_subset_left, mem_inter_iff, mem_preimage, preimage_inter
-/
theorem contMDiffOn_zero_iff : ContMDiffOn I I' 0 f s ↔ ContinuousOn f s := by
  rw [contMDiffOn_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro x y
  rw [contDiffOn_zero]
  apply (continuousOn_extChartAt _).comp
  · apply h.comp ((continuousOn_extChartAt_symm _).mono inter_subset_left) (fun z hz => ?_)
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at hz
    exact hz.2.1
  · intro z hz
    simp only [preimage_inter, mem_inter_iff, mem_preimage] at hz
    exact hz.2.2

/--
theorem `contMDiffOn_iff_target` / 定理 `contMDiffOn_iff_target`

English:
theorem contMDiffOn_iff_target
  given: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_

中文:
定理 contMDiffOn_iff_target
  条件: [是流形 I n M] [是流形 I' n M']
  证明: by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_

Depends on / 依赖: ContinuousOn, ModelWithCorners, ModelWithCorners.continuous, ModelWithCorners.source_eq, OpenPartialHomeomorph, OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv, PartialEquiv.refl_trans, Set.inter_univ, Set.preimage_univ, and_congr_right_iff, chartAt, chartAt_self_eq, comp_inter, contMDiffOn_iff, continuous, continuousOn, continuousOn_toFun, convert
-/
theorem contMDiffOn_iff_target [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        forall y : M',
          ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s inter f ⁻¹' (extChartAt I' y).source) := by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0


/--
theorem `contMDiff_iff` / 定理 `contMDiff_iff`

English:
theorem contMDiff_iff
  given: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuousOn_univ]

中文:
定理 contMDiff_iff
  条件: [是流形 I n M] [是流形 I' n M']
  证明: by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuousOn_univ]

Depends on / 依赖: contMDiffOn_iff, contMDiffOn_univ, continuousOn_univ
-/
theorem contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiff I I' n f ↔
      Continuous f ∧
        forall (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target inter
              (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' y).source) := by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuousOn_univ]

/--
theorem `contMDiff_iff_target` / 定理 `contMDiff_iff_target`

English:
theorem contMDiff_iff_target
  given: [IsManifold I n M] [IsManifold I' n M']
  proof: by
  rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_target]
  simp [continuousOn_univ]

中文:
定理 contMDiff_iff_target
  条件: [是流形 I n M] [是流形 I' n M']
  证明: by
  rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_target]
  simp [continuousOn_univ]

Depends on / 依赖: contMDiffOn_iff_target, contMDiffOn_univ, continuousOn_univ
-/
theorem contMDiff_iff_target [IsManifold I n M] [IsManifold I' n M'] :
    ContMDiff I I' n f ↔
      Continuous f ∧ forall y : M',
        ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) := by
  rw [← contMDiffOn_univ]; rw [contMDiffOn_iff_target]
  simp [continuousOn_univ]

/--
theorem `contMDiff_zero_iff` / 定理 `contMDiff_zero_iff`

English:
theorem contMDiff_zero_iff
  proof: by
  rw [← contMDiffOn_univ]; rw [← continuousOn_univ]; rw [contMDiffOn_zero_iff]

中文:
定理 contMDiff_zero_iff
  证明: by
  rw [← contMDiffOn_univ]; rw [← continuousOn_univ]; rw [contMDiffOn_zero_iff]

Depends on / 依赖: contMDiffOn_univ, contMDiffOn_zero_iff, continuousOn_univ
-/
theorem contMDiff_zero_iff :
    ContMDiff I I' 0 f ↔ Continuous f := by
  rw [← contMDiffOn_univ]; rw [← continuousOn_univ]; rw [contMDiffOn_zero_iff]

end IsManifold



/--
theorem `ContMDiffWithinAt.of_succ` / 定理 `ContMDiffWithinAt.of_succ`

English:
theorem ContMDiffWithinAt.of_succ
  given: (h : ContMDiffWithinAt I I' (n + 1) f s x)
  proof: h.of_le le_self_add

中文:
定理 ContMDiffWithinAt.of_succ
  条件: (h : ContMDiffWithinAt I I' (n + 1) f s x)
  证明: h.of_le le_self_add

Depends on / 依赖: h.of_le, le_self_add, of_le
-/
theorem ContMDiffWithinAt.of_succ (h : ContMDiffWithinAt I I' (n + 1) f s x) :
    ContMDiffWithinAt I I' n f s x :=
  h.of_le le_self_add

/--
theorem `ContMDiffAt.of_succ` / 定理 `ContMDiffAt.of_succ`

English:
theorem ContMDiffAt.of_succ
  given: (h : ContMDiffAt I I' (n + 1) f x)
  statement: ContMDiffAt I I' n f x
  proof: ContMDiffWithinAt.of_succ h

中文:
定理 ContMDiffAt.of_succ
  条件: (h : ContMDiffAt I I' (n + 1) f x)
  结论: ContMDiffAt I I' n f x
  证明: ContMDiffWithinAt.of_succ h

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.of_succ, of_succ
-/
theorem ContMDiffAt.of_succ (h : ContMDiffAt I I' (n + 1) f x) : ContMDiffAt I I' n f x :=
  ContMDiffWithinAt.of_succ h

/--
theorem `ContMDiffOn.of_succ` / 定理 `ContMDiffOn.of_succ`

English:
theorem ContMDiffOn.of_succ
  given: (h : ContMDiffOn I I' (n + 1) f s)
  statement: ContMDiffOn I I' n f s
  proof: fun x hx => (h x hx).of_succ

中文:
定理 ContMDiffOn.of_succ
  条件: (h : ContMDiffOn I I' (n + 1) f s)
  结论: ContMDiffOn I I' n f s
  证明: fun x hx => (h x hx).of_succ

Depends on / 依赖: of_succ
-/
theorem ContMDiffOn.of_succ (h : ContMDiffOn I I' (n + 1) f s) : ContMDiffOn I I' n f s :=
  fun x hx => (h x hx).of_succ

/--
theorem `ContMDiff.of_succ` / 定理 `ContMDiff.of_succ`

English:
theorem ContMDiff.of_succ
  given: (h : ContMDiff I I' (n + 1) f)
  statement: ContMDiff I I' n f
  proof: fun x =>
  (h x).of_succ

中文:
定理 ContMDiff.of_succ
  条件: (h : ContMDiff I I' (n + 1) f)
  结论: ContMDiff I I' n f
  证明: fun x =>
  (h x).of_succ
-/
theorem ContMDiff.of_succ (h : ContMDiff I I' (n + 1) f) : ContMDiff I I' n f := fun x =>
  (h x).of_succ



/--
theorem `ContMDiffWithinAt.continuousWithinAt` / 定理 `ContMDiffWithinAt.continuousWithinAt`

English:
theorem ContMDiffWithinAt.continuousWithinAt
  given: (hf : ContMDiffWithinAt I I' n f s x)
  proof: hf.1

中文:
定理 ContMDiffWithinAt.continuousWithinAt
  条件: (hf : ContMDiffWithinAt I I' n f s x)
  证明: hf.1
-/
theorem ContMDiffWithinAt.continuousWithinAt (hf : ContMDiffWithinAt I I' n f s x) :
    ContinuousWithinAt f s x :=
  hf.1

/--
theorem `ContMDiffAt.continuousAt` / 定理 `ContMDiffAt.continuousAt`

English:
theorem ContMDiffAt.continuousAt
  given: (hf : ContMDiffAt I I' n f x)
  statement: ContinuousAt f x
  proof: (continuousWithinAt_univ _ _).1 ContMDiffWithinAt.continuousWithinAt hf

中文:
定理 ContMDiffAt.continuousAt
  条件: (hf : ContMDiffAt I I' n f x)
  结论: ContinuousAt f x
  证明: (continuousWithinAt_univ _ _).1 ContMDiffWithinAt.continuousWithinAt hf

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.continuousWithinAt, continuousWithinAt, continuousWithinAt_univ
-/
theorem ContMDiffAt.continuousAt (hf : ContMDiffAt I I' n f x) : ContinuousAt f x :=
(continuousWithinAt_univ _ _).1 ContMDiffWithinAt.continuousWithinAt hf

/--
theorem `ContMDiffOn.continuousOn` / 定理 `ContMDiffOn.continuousOn`

English:
theorem ContMDiffOn.continuousOn
  given: (hf : ContMDiffOn I I' n f s)
  statement: ContinuousOn f s
  proof: fun x hx =>
  (hf x hx).continuousWithinAt

中文:
定理 ContMDiffOn.continuousOn
  条件: (hf : ContMDiffOn I I' n f s)
  结论: ContinuousOn f s
  证明: fun x hx =>
  (hf x hx).continuousWithinAt
-/
theorem ContMDiffOn.continuousOn (hf : ContMDiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).continuousWithinAt

/--
theorem `ContMDiff.continuous` / 定理 `ContMDiff.continuous`

English:
theorem ContMDiff.continuous
  given: (hf : ContMDiff I I' n f)
  statement: Continuous f
  proof: continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

中文:
定理 ContMDiff.continuous
  条件: (hf : ContMDiff I I' n f)
  结论: 连续 f
  证明: continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt
-/
theorem ContMDiff.continuous (hf : ContMDiff I I' n f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt


/--
theorem `contMDiffWithinAt_infty` / 定理 `contMDiffWithinAt_infty`

English:
theorem contMDiffWithinAt_infty
  proof: ⟨fun h n => ⟨h.1, contDiffWithinAt_infty.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_infty.2 fun n => (H n).2⟩⟩

中文:
定理 contMDiffWithinAt_infty
  证明: ⟨fun h n => ⟨h.1, contDiffWithinAt_infty.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_infty.2 fun n => (H n).2⟩⟩

Depends on / 依赖: contDiffWithinAt_infty
-/
theorem contMDiffWithinAt_infty :
    ContMDiffWithinAt I I' ∞ f s x ↔ forall n : Nat, ContMDiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, contDiffWithinAt_infty.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_infty.2 fun n => (H n).2⟩⟩

/--
theorem `contMDiffAt_infty` / 定理 `contMDiffAt_infty`

English:
theorem contMDiffAt_infty
  statement: ContMDiffAt I I' ∞ f x ↔ forall n : Nat, ContMDiffAt I I' n f x
  proof: contMDiffWithinAt_infty

中文:
定理 contMDiffAt_infty
  结论: ContMDiffAt I I' ∞ f x ↔ 对任意 n : 自然数, ContMDiffAt I I' n f x
  证明: contMDiffWithinAt_infty

Depends on / 依赖: contMDiffWithinAt_infty
-/
theorem contMDiffAt_infty : ContMDiffAt I I' ∞ f x ↔ forall n : Nat, ContMDiffAt I I' n f x :=
  contMDiffWithinAt_infty

/--
theorem `contMDiffOn_infty` / 定理 `contMDiffOn_infty`

English:
theorem contMDiffOn_infty
  statement: ContMDiffOn I I' ∞ f s ↔ forall n : Nat, ContMDiffOn I I' n f s
  proof: ⟨fun h _ => h.of_le (mod_cast le_top),
    fun h x hx => contMDiffWithinAt_infty.2 fun n => h n x hx⟩

中文:
定理 contMDiffOn_infty
  结论: ContMDiffOn I I' ∞ f s ↔ 对任意 n : 自然数, ContMDiffOn I I' n f s
  证明: ⟨fun h _ => h.of_le (mod_cast le_top),
    fun h x hx => contMDiffWithinAt_infty.2 fun n => h n x hx⟩

Depends on / 依赖: contMDiffWithinAt_infty, h.of_le, le_top, mod_cast, of_le
-/
theorem contMDiffOn_infty : ContMDiffOn I I' ∞ f s ↔ forall n : Nat, ContMDiffOn I I' n f s :=
  ⟨fun h _ => h.of_le (mod_cast le_top),
    fun h x hx => contMDiffWithinAt_infty.2 fun n => h n x hx⟩

/--
theorem `contMDiff_infty` / 定理 `contMDiff_infty`

English:
theorem contMDiff_infty
  statement: ContMDiff I I' ∞ f ↔ forall n : Nat, ContMDiff I I' n f
  proof: ⟨fun h _ => h.of_le (mod_cast le_top), fun h x => contMDiffWithinAt_infty.2 fun n => h n x⟩

中文:
定理 contMDiff_infty
  结论: ContMDiff I I' ∞ f ↔ 对任意 n : 自然数, ContMDiff I I' n f
  证明: ⟨fun h _ => h.of_le (mod_cast le_top), fun h x => contMDiffWithinAt_infty.2 fun n => h n x⟩

Depends on / 依赖: contMDiffWithinAt_infty, h.of_le, le_top, mod_cast, of_le
-/
theorem contMDiff_infty : ContMDiff I I' ∞ f ↔ forall n : Nat, ContMDiff I I' n f :=
  ⟨fun h _ => h.of_le (mod_cast le_top), fun h x => contMDiffWithinAt_infty.2 fun n => h n x⟩

/--
theorem `contMDiffWithinAt_iff_nat` / 定理 `contMDiffWithinAt_iff_nat`

English:
theorem contMDiffWithinAt_iff_nat
  given: {n : Nat∞}
  proof: by
  refine ⟨fun h m hm => h.of_le (mod_cast hm), fun h => ?_⟩
  obtain - | n := n
  · exact contMDiffWithinAt_infty.2 fun n => h n le_top
  · exact h n le_rfl

中文:
定理 contMDiffWithinAt_iff_nat
  条件: {n : 自然数∞}
  证明: by
  refine ⟨fun h m hm => h.of_le (mod_cast hm), fun h => ?_⟩
  obtain - | n := n
  · exact contMDiffWithinAt_infty.2 fun n => h n le_top
  · exact h n le_rfl

Depends on / 依赖: contMDiffWithinAt_infty, h.of_le, le_rfl, le_top, mod_cast, of_le
-/
theorem contMDiffWithinAt_iff_nat {n : Nat∞} :
    ContMDiffWithinAt I I' n f s x ↔ forall m : Nat, (m : Nat∞) <= n -> ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm => h.of_le (mod_cast hm), fun h => ?_⟩
  obtain - | n := n
  · exact contMDiffWithinAt_infty.2 fun n => h n le_top
  · exact h n le_rfl

/--
theorem `contMDiffAt_iff_nat` / 定理 `contMDiffAt_iff_nat`

English:
theorem contMDiffAt_iff_nat
  given: {n : Nat∞}
  proof: by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_nat]

中文:
定理 contMDiffAt_iff_nat
  条件: {n : 自然数∞}
  证明: by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_nat]

Depends on / 依赖: contMDiffWithinAt_iff_nat, contMDiffWithinAt_univ
-/
theorem contMDiffAt_iff_nat {n : Nat∞} :
    ContMDiffAt I I' n f x ↔ forall m : Nat, (m : Nat∞) <= n -> ContMDiffAt I I' m f x := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_nat]

/--
theorem `contMDiffWithinAt_iff_le_ne_infty` / 定理 `contMDiffWithinAt_iff_le_ne_infty`

English:
theorem contMDiffWithinAt_iff_le_ne_infty
  proof: by
  refine ⟨fun h m hm h'm => h.of_le hm, fun h => ?_⟩
  cases n with
  | top =>
    exact h _ le_rfl (by simp)
  | coe n =>
    exact contMDiffWithinAt_iff_nat.2 (fun m hm => h _ (mod_cast hm) (by simp))

中文:
定理 contMDiffWithinAt_iff_le_ne_infty
  证明: by
  refine ⟨fun h m hm h'm => h.of_le hm, fun h => ?_⟩
  cases n with
  | top =>
    exact h _ le_rfl (by simp)
  | coe n =>
    exact contMDiffWithinAt_iff_nat.2 (fun m hm => h _ (mod_cast hm) (by simp))

Depends on / 依赖: contMDiffWithinAt_iff_nat, h.of_le, le_rfl, mod_cast, of_le
-/
theorem contMDiffWithinAt_iff_le_ne_infty :
    ContMDiffWithinAt I I' n f s x ↔ forall m, m <= n -> m != ∞ -> ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm h'm => h.of_le hm, fun h => ?_⟩
  cases n with
  | top =>
    exact h _ le_rfl (by simp)
  | coe n =>
    exact contMDiffWithinAt_iff_nat.2 (fun m hm => h _ (mod_cast hm) (by simp))

/--
theorem `contMDiffAt_iff_le_ne_infty` / 定理 `contMDiffAt_iff_le_ne_infty`

English:
theorem contMDiffAt_iff_le_ne_infty
  proof: by
  simp only [← contMDiffWithinAt_univ]
  rw [contMDiffWithinAt_iff_le_ne_infty]

中文:
定理 contMDiffAt_iff_le_ne_infty
  证明: by
  simp only [← contMDiffWithinAt_univ]
  rw [contMDiffWithinAt_iff_le_ne_infty]

Depends on / 依赖: contMDiffWithinAt_iff_le_ne_infty, contMDiffWithinAt_univ
-/
theorem contMDiffAt_iff_le_ne_infty :
    ContMDiffAt I I' n f x ↔ forall m, m <= n -> m != ∞ -> ContMDiffAt I I' m f x := by
  simp only [← contMDiffWithinAt_univ]
  rw [contMDiffWithinAt_iff_le_ne_infty]


/--
theorem `ContMDiffWithinAt.mono_of_mem_nhdsWithin` / 定理 `ContMDiffWithinAt.mono_of_mem_nhdsWithin`

English:
theorem ContMDiffWithinAt.mono_of_mem_nhdsWithin
  proof: StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin
    (contDiffWithinAtProp_mono_of_mem_nhdsWithin n) hf hts

中文:
定理 ContMDiffWithinAt.mono_of_mem_nhdsWithin
  证明: StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin
    (contDiffWithinAtProp_mono_of_mem_nhdsWithin n) hf hts

Depends on / 依赖: LocalInvariantProp, StructureGroupoid, StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin, contDiffWithinAtProp_mono_of_mem_nhdsWithin, liftPropWithinAt_mono_of_mem_nhdsWithin
-/
theorem ContMDiffWithinAt.mono_of_mem_nhdsWithin
    (hf : ContMDiffWithinAt I I' n f s x) (hts : s in 𝓝[t] x) :
    ContMDiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem_nhdsWithin
    (contDiffWithinAtProp_mono_of_mem_nhdsWithin n) hf hts

/--
theorem `ContMDiffWithinAt.mono` / 定理 `ContMDiffWithinAt.mono`

English:
theorem ContMDiffWithinAt.mono
  given: (hf : ContMDiffWithinAt I I' n f s x) (hts : t subseteq s)
  proof: hf.mono_of_mem_nhdsWithin mem_of_superset self_mem_nhdsWithin hts

中文:
定理 ContMDiffWithinAt.mono
  条件: (hf : ContMDiffWithinAt I I' n f s x) (hts : t subseteq s)
  证明: hf.mono_of_mem_nhdsWithin mem_of_superset self_mem_nhdsWithin hts

Depends on / 依赖: hf.mono_of_mem_nhdsWithin, mem_of_superset, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t subseteq s) :
    ContMDiffWithinAt I I' n f t x :=
hf.mono_of_mem_nhdsWithin mem_of_superset self_mem_nhdsWithin hts

/--
theorem `contMDiffWithinAt_congr_set` / 定理 `contMDiffWithinAt_congr_set`

English:
theorem contMDiffWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_set h

中文:
定理 contMDiffWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_set h

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_set
-/
theorem contMDiffWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_set h

/--
theorem `ContMDiffWithinAt.congr_set` / 定理 `ContMDiffWithinAt.congr_set`

English:
theorem ContMDiffWithinAt.congr_set
  given: (h : ContMDiffWithinAt I I' n f s x) (hst : s =ᶠ[𝓝 x] t)
  proof: (contMDiffWithinAt_congr_set hst).1 h

中文:
定理 ContMDiffWithinAt.congr_set
  条件: (h : ContMDiffWithinAt I I' n f s x) (hst : s =ᶠ[𝓝 x] t)
  证明: (contMDiffWithinAt_congr_set hst).1 h

Depends on / 依赖: contMDiffWithinAt_congr_set
-/
theorem ContMDiffWithinAt.congr_set (h : ContMDiffWithinAt I I' n f s x) (hst : s =ᶠ[𝓝 x] t) :
    ContMDiffWithinAt I I' n f t x :=
  (contMDiffWithinAt_congr_set hst).1 h

/--
theorem `contMDiffWithinAt_insert_self` / 定理 `contMDiffWithinAt_insert_self`

English:
theorem contMDiffWithinAt_insert_self
  proof: by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
refine Iff.rfl.and (contDiffWithinAt_congr_set ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin, nhdsWithin_insert, Filter.map_sup, Filter.map_pure,
    ← nhdsWithin_eq_iff_eventuallyEq]

alias ⟨Con

中文:
定理 contMDiffWithinAt_insert_self
  证明: by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
refine Iff.rfl.and (contDiffWithinAt_congr_set ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin, nhdsWithin_insert, Filter.map_sup, Filter.map_pure,
    ← nhdsWithin_eq_iff_eventuallyEq]

alias ⟨Con

Depends on / 依赖: Filter, Filter.map_pure, Filter.map_sup, Iff.rfl.and, contDiffWithinAt_congr_set, contDiffWithinAt_insert_self, contMDiffWithinAt_iff, continuousWithinAt_insert_self, map_extChartAt_nhdsWithin, map_pure, map_sup, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_insert
-/
theorem contMDiffWithinAt_insert_self :
    ContMDiffWithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
refine Iff.rfl.and (contDiffWithinAt_congr_set ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin, nhdsWithin_insert, Filter.map_sup, Filter.map_pure,
    ← nhdsWithin_eq_iff_eventuallyEq]

alias ⟨ContMDiffWithinAt.of_insert, _⟩ := contMDiffWithinAt_insert_self

-- TODO: use `alias` again once it can make protected theorems
/--
theorem `ContMDiffWithinAt.insert` / 定理 `ContMDiffWithinAt.insert`

English:
theorem ContMDiffWithinAt.insert
  given: (h : ContMDiffWithinAt I I' n f s x)
  proof: contMDiffWithinAt_insert_self.2 h

中文:
定理 ContMDiffWithinAt.insert
  条件: (h : ContMDiffWithinAt I I' n f s x)
  证明: contMDiffWithinAt_insert_self.2 h
-/
protected theorem ContMDiffWithinAt.insert (h : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I' n f (insert x s) x :=
  contMDiffWithinAt_insert_self.2 h

/--
theorem `contMDiffWithinAt_congr_set'` / 定理 `contMDiffWithinAt_congr_set'`

English:
theorem contMDiffWithinAt_congr_set'
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  have : T1Space M := I.t1Space M
  rw [← contMDiffWithinAt_insert_self (s := s)]; rw [← contMDiffWithinAt_insert_self (s := t)]
  exact contMDiffWithinAt_congr_set (eventuallyEq_insert h)

中文:
定理 contMDiffWithinAt_congr_set'
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  have : T1Space M := I.t1Space M
  rw [← contMDiffWithinAt_insert_self (s := s)]; rw [← contMDiffWithinAt_insert_self (s := t)]
  exact contMDiffWithinAt_congr_set (eventuallyEq_insert h)

Depends on / 依赖: I.t1Space, T1Space, contMDiffWithinAt_congr_set, contMDiffWithinAt_insert_self, eventuallyEq_insert, t1Space
-/
theorem contMDiffWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x := by
  have : T1Space M := I.t1Space M
  rw [← contMDiffWithinAt_insert_self (s := s)]; rw [← contMDiffWithinAt_insert_self (s := t)]
  exact contMDiffWithinAt_congr_set (eventuallyEq_insert h)

/--
theorem `ContMDiffAt.contMDiffWithinAt` / 定理 `ContMDiffAt.contMDiffWithinAt`

English:
theorem ContMDiffAt.contMDiffWithinAt
  given: (hf : ContMDiffAt I I' n f x)
  proof: ContMDiffWithinAt.mono hf (subset_univ _)

中文:
定理 ContMDiffAt.contMDiffWithinAt
  条件: (hf : ContMDiffAt I I' n f x)
  证明: ContMDiffWithinAt.mono hf (subset_univ _)
-/
protected theorem ContMDiffAt.contMDiffWithinAt (hf : ContMDiffAt I I' n f x) :
    ContMDiffWithinAt I I' n f s x :=
  ContMDiffWithinAt.mono hf (subset_univ _)

/--
theorem `ContMDiffOn.mono` / 定理 `ContMDiffOn.mono`

English:
theorem ContMDiffOn.mono
  given: (hf : ContMDiffOn I I' n f s) (hts : t subseteq s)
  statement: ContMDiffOn I I' n f t
  proof: fun x hx => (hf x (hts hx)).mono hts

中文:
定理 ContMDiffOn.mono
  条件: (hf : ContMDiffOn I I' n f s) (hts : t subseteq s)
  结论: ContMDiffOn I I' n f t
  证明: fun x hx => (hf x (hts hx)).mono hts
-/
theorem ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t subseteq s) : ContMDiffOn I I' n f t :=
  fun x hx => (hf x (hts hx)).mono hts

/--
theorem `ContMDiff.contMDiffOn` / 定理 `ContMDiff.contMDiffOn`

English:
theorem ContMDiff.contMDiffOn
  given: (hf : ContMDiff I I' n f)
  statement: ContMDiffOn I I' n f s
  proof: fun x _ => (hf x).contMDiffWithinAt

中文:
定理 ContMDiff.contMDiffOn
  条件: (hf : ContMDiff I I' n f)
  结论: ContMDiffOn I I' n f s
  证明: fun x _ => (hf x).contMDiffWithinAt
-/
protected theorem ContMDiff.contMDiffOn (hf : ContMDiff I I' n f) : ContMDiffOn I I' n f s :=
  fun x _ => (hf x).contMDiffWithinAt

/--
theorem `contMDiffWithinAt_inter'` / 定理 `contMDiffWithinAt_inter'`

English:
theorem contMDiffWithinAt_inter'
  given: (ht : t in 𝓝[s] x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter' ht

中文:
定理 contMDiffWithinAt_inter'
  条件: (ht : t in 𝓝[s] x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter' ht

Depends on / 依赖: IsSelfAdjoint, IsSelfAdjoint.star_eq, contDiffWithinAt_localInvariantProp, liftPropWithinAt_inter, realPart_add_I_smul_imaginaryPart, star_eq
-/
theorem contMDiffWithinAt_inter' (ht : t in 𝓝[s] x) :
    ContMDiffWithinAt I I' n f (s inter t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter' ht

/--
theorem `contMDiffWithinAt_inter` / 定理 `contMDiffWithinAt_inter`

English:
theorem contMDiffWithinAt_inter
  given: (ht : t in 𝓝 x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter ht

中文:
定理 contMDiffWithinAt_inter
  条件: (ht : t in 𝓝 x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter ht

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_inter
-/
theorem contMDiffWithinAt_inter (ht : t in 𝓝 x) :
    ContMDiffWithinAt I I' n f (s inter t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_inter ht

/--
theorem `ContMDiffWithinAt.contMDiffAt` / 定理 `ContMDiffWithinAt.contMDiffAt`

English:
theorem ContMDiffWithinAt.contMDiffAt
  proof: (contDiffWithinAt_localInvariantProp n).liftPropAt_of_liftPropWithinAt h ht

中文:
定理 ContMDiffWithinAt.contMDiffAt
  证明: (contDiffWithinAt_localInvariantProp n).liftPropAt_of_liftPropWithinAt h ht
-/
protected theorem ContMDiffWithinAt.contMDiffAt
    (h : ContMDiffWithinAt I I' n f s x) (ht : s in 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_of_liftPropWithinAt h ht

/--
theorem `ContMDiffOn.contMDiffAt` / 定理 `ContMDiffOn.contMDiffAt`

English:
theorem ContMDiffOn.contMDiffAt
  given: (h : ContMDiffOn I I' n f s) (hx : s in 𝓝 x)
  proof: (h x (mem_of_mem_nhds hx)).contMDiffAt hx

中文:
定理 ContMDiffOn.contMDiffAt
  条件: (h : ContMDiffOn I I' n f s) (hx : s in 𝓝 x)
  证明: (h x (mem_of_mem_nhds hx)).contMDiffAt hx
-/
protected theorem ContMDiffOn.contMDiffAt (h : ContMDiffOn I I' n f s) (hx : s in 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (h x (mem_of_mem_nhds hx)).contMDiffAt hx

/--
theorem `contMDiffOn_iff_source_of_mem_maximalAtlas` / 定理 `contMDiffOn_iff_source_of_mem_maximalAtlas`

English:
theorem contMDiffOn_iff_source_of_mem_maximalAtlas
  proof: by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_set
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs (hs hx)]

中文:
定理 contMDiffOn_iff_source_of_mem_maximalAtlas
  证明: by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_set
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs (hs hx)]

Depends on / 依赖: ContMDiffOn, Set.forall_mem_image, contMDiffWithinAt_congr_set, contMDiffWithinAt_iff_source_of_mem_maximalAtlas, e.extend_symm_preimage_inter_range_eventuallyEq, extend_symm_preimage_inter_range_eventuallyEq, forall_mem_image, simp_rw
-/
theorem contMDiffOn_iff_source_of_mem_maximalAtlas
    (he : e in maximalAtlas I n M) (hs : s subseteq e.source) :
    ContMDiffOn I I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_set
  simp_rw [e.extend_symm_preimage_inter_range_eventuallyEq hs (hs hx)]

/--
theorem `contMDiffWithinAt_iff_contMDiffOn_nhds` / 定理 `contMDiffWithinAt_iff_contMDiffOn_nhds`

English:
theorem contMDiffWithinAt_iff_contMDiffOn_nhds
  proof: by
  -- WLOG, `x ∈ s`, otherwise we add `x` to `s`
  wlog hxs : x in s generalizing s
  · rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  -- The `←` implication is trivial
  refine ⟨fun h => ?_, fun ⟨u, hmem, hu⟩ =>
    (hu _ (mem_of_mem_nhdsWit

中文:
定理 contMDiffWithinAt_iff_contMDiffOn_nhds
  证明: by
  -- WLOG, `x ∈ s`, otherwise we add `x` to `s`
  wlog hxs : x in s generalizing s
  · rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  -- The `←` implication is trivial
  refine ⟨fun h => ?_, fun ⟨u, hmem, hu⟩ =>
    (hu _ (mem_of_mem_nhdsWit
-/
theorem contMDiffWithinAt_iff_contMDiffOn_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) :
    ContMDiffWithinAt I I' n f s x ↔ exists u in 𝓝[insert x s] x, ContMDiffOn I I' n f u := by
  -- WLOG, `x ∈ s`, otherwise we add `x` to `s`
  wlog hxs : x in s generalizing s
  · rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  -- The `←` implication is trivial
  refine ⟨fun h => ?_, fun ⟨u, hmem, hu⟩ =>
    (hu _ (mem_of_mem_nhdsWithin hxs hmem)).mono_of_mem_nhdsWithin hmem⟩
  -- The property is true in charts. Let `v` be a good neighborhood in the chart where the function
  -- is `Cⁿ`.
  rcases (contMDiffWithinAt_iff'.1 h).2.contDiffOn le_rfl (by simp [hn]) with ⟨v, hmem, hsub, hv⟩
  have hxs' : extChartAt I x x in (extChartAt I x).target inter
      (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source) :=
    ⟨(extChartAt I x).map_source (mem_extChartAt_source _), by rwa [extChartAt_to_inv], by
      rw [extChartAt_to_inv]; apply mem_extChartAt_source⟩
  rw [insert_eq_of_mem hxs'] at hmem hsub
  -- Then `(extChartAt I x).symm '' v` is the neighborhood we are looking for.
  refine ⟨(extChartAt I x).symm '' v, ?_, ?_⟩
  · rw [← map_extChartAt_symm_nhdsWithin (I := I),
      h.1.nhdsWithin_extChartAt_symm_preimage_inter_range (I := I) (I' := I')]
    exact image_mem_map hmem
  · have hv₁ : (extChartAt I x).symm '' v subseteq (extChartAt I x).source :=
      image_subset_iff.2 fun y hy => (extChartAt I x).map_target (hsub hy).1
    have hv₂ : MapsTo f ((extChartAt I x).symm '' v) (extChartAt I' (f x)).source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hsub hy).2.2
    rwa [contMDiffOn_iff_of_subset_source' hv₁ hv₂, PartialEquiv.image_symm_image_of_subset_target]
    exact hsub.trans inter_subset_left

/--
theorem `ContMDiffWithinAt.contMDiffOn'` / 定理 `ContMDiffWithinAt.contMDiffOn'`

English:
theorem ContMDiffWithinAt.contMDiffOn'
  proof: by
  have : IsManifold I m M := .of_le hm
  have : IsManifold I' m M' := .of_le hm
  match m with
  | (m : Nat) | ω =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp)).1 (h.of_le hm) with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    

中文:
定理 ContMDiffWithinAt.contMDiffOn'
  证明: by
  have : IsManifold I m M := .of_le hm
  have : IsManifold I' m M' := .of_le hm
  match m with
  | (m : Nat) | ω =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp)).1 (h.of_le hm) with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    

Depends on / 依赖: IsManifold, contMDiffWithinAt_iff_contMDiffOn_nhds, h.of_le, inter_comm, mem_nhdsWithin, of_le, t.mono, u_open
-/
theorem ContMDiffWithinAt.contMDiffOn'
    [IsManifold I n M] [IsManifold I' n M']
    (hm : m <= n) (h' : m = ∞ -> n = ω)
    (h : ContMDiffWithinAt I I' n f s x) :
    exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' m f (insert x s inter u) := by
  have : IsManifold I m M := .of_le hm
  have : IsManifold I' m M' := .of_le hm
  match m with
  | (m : Nat) | ω =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp)).1 (h.of_le hm) with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    exact ⟨u, u_open, xu, h't.mono hu⟩
  | ∞ =>
    rcases (contMDiffWithinAt_iff_contMDiffOn_nhds (by simp [h'])).1 h with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, xu, hu⟩
    rw [inter_comm] at hu
    exact ⟨u, u_open, xu, (h't.mono hu).of_le hm⟩

/--
theorem `ContMDiffWithinAt.contMDiffOn` / 定理 `ContMDiffWithinAt.contMDiffOn`

English:
theorem ContMDiffWithinAt.contMDiffOn
  proof: by
  let ⟨_u, uo, xu, h⟩ := h.contMDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

中文:
定理 ContMDiffWithinAt.contMDiffOn
  证明: by
  let ⟨_u, uo, xu, h⟩ := h.contMDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

Depends on / 依赖: contMDiffOn, h.contMDiffOn, inter_mem_nhdsWithin, inter_subset_left, mem_nhds, uo.mem_nhds
-/
theorem ContMDiffWithinAt.contMDiffOn
    [IsManifold I n M] [IsManifold I' n M']
    (hm : m <= n) (h' : m = ∞ -> n = ω)
    (h : ContMDiffWithinAt I I' n f s x) :
    exists u in 𝓝[insert x s] x, u subseteq insert x s ∧ ContMDiffOn I I' m f u := by
  let ⟨_u, uo, xu, h⟩ := h.contMDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

/--
theorem `contMDiffAt_iff_contMDiffOn_nhds` / 定理 `contMDiffAt_iff_contMDiffOn_nhds`

English:
theorem contMDiffAt_iff_contMDiffOn_nhds
  proof: by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds hn, nhdsWithin_univ]

中文:
定理 contMDiffAt_iff_contMDiffOn_nhds
  证明: by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds hn, nhdsWithin_univ]

Depends on / 依赖: contMDiffWithinAt_iff_contMDiffOn_nhds, contMDiffWithinAt_univ, nhdsWithin_univ
-/
theorem contMDiffAt_iff_contMDiffOn_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) :
    ContMDiffAt I I' n f x ↔ exists u in 𝓝 x, ContMDiffOn I I' n f u := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds hn, nhdsWithin_univ]

/--
theorem `contMDiffAt_iff_contMDiffAt_nhds` / 定理 `contMDiffAt_iff_contMDiffAt_nhds`

English:
theorem contMDiffAt_iff_contMDiffAt_nhds
  proof: by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds_iff.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'

中文:
定理 contMDiffAt_iff_contMDiffAt_nhds
  证明: by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds_iff.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'

Depends on / 依赖: contMDiffAt, contMDiffAt_iff_contMDiffOn_nhds, eventually_mem_nhds_iff, eventually_mem_nhds_iff.mpr, h.self_of_nhds, mem_of_mem_nhds, self_of_nhds
-/
theorem contMDiffAt_iff_contMDiffAt_nhds
    [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) :
    ContMDiffAt I I' n f x ↔ forallᶠ x' in 𝓝 x, ContMDiffAt I I' n f x' := by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds_iff.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'

/--
theorem `contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin` / 定理 `contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin`

English:
theorem contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin
  proof: by
  refine ⟨?_, fun h => mem_of_mem_nhdsWithin (mem_insert x s) h⟩
  rw [contMDiffWithinAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  filter_upwards [hu, eventually_mem_nhdsWithin_iff.mpr hu] with x' h'x' hx'
  apply (h x' h'x').mono_of_mem_nhdsWithin
  exact nhdsWithin_mono _ (subset_insert x 

中文:
定理 contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin
  证明: by
  refine ⟨?_, fun h => mem_of_mem_nhdsWithin (mem_insert x s) h⟩
  rw [contMDiffWithinAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  filter_upwards [hu, eventually_mem_nhdsWithin_iff.mpr hu] with x' h'x' hx'
  apply (h x' h'x').mono_of_mem_nhdsWithin
  exact nhdsWithin_mono _ (subset_insert x 

Depends on / 依赖: contMDiffWithinAt_iff_contMDiffOn_nhds, eventually_mem_nhdsWithin_iff, eventually_mem_nhdsWithin_iff.mpr, filter_upwards, mem_insert, mem_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
theorem contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin
    [IsManifold I n M] [IsManifold I' n M'] (hn : n != ∞) :
    ContMDiffWithinAt I I' n f s x ↔
      forallᶠ x' in 𝓝[insert x s] x, ContMDiffWithinAt I I' n f s x' := by
  refine ⟨?_, fun h => mem_of_mem_nhdsWithin (mem_insert x s) h⟩
  rw [contMDiffWithinAt_iff_contMDiffOn_nhds hn]
  rintro ⟨u, hu, h⟩
  filter_upwards [hu, eventually_mem_nhdsWithin_iff.mpr hu] with x' h'x' hx'
  apply (h x' h'x').mono_of_mem_nhdsWithin
  exact nhdsWithin_mono _ (subset_insert x s) hx'


/--
theorem `ContMDiffWithinAt.congr` / 定理 `ContMDiffWithinAt.congr`

English:
theorem ContMDiffWithinAt.congr
  statement: (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall y in s, f₁ y = f y)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr h h₁ hx

中文:
定理 ContMDiffWithinAt.congr
  结论: (h : ContMDiffWithinAt I I' n f s x) (h₁ : 对任意 y in s, f₁ y = f y)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr h h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr
-/
theorem ContMDiffWithinAt.congr (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall y in s, f₁ y = f y)
    (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr h h₁ hx

/--
theorem `ContMDiffWithinAt.congr'` / 定理 `ContMDiffWithinAt.congr'`

English:
theorem ContMDiffWithinAt.congr'
  statement: (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall y in t, f₁ y = f y)
  proof: h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

中文:
定理 ContMDiffWithinAt.congr'
  结论: (h : ContMDiffWithinAt I I' n f s x) (h₁ : 对任意 y in t, f₁ y = f y)
  证明: h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

Depends on / 依赖: h.congr
-/
theorem ContMDiffWithinAt.congr' (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall y in t, f₁ y = f y)
    (hst : s subseteq t) (hxt : x in t) :
    ContMDiffWithinAt I I' n f₁ s x :=
  h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

/--
theorem `contMDiffWithinAt_congr` / 定理 `contMDiffWithinAt_congr`

English:
theorem contMDiffWithinAt_congr
  given: (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff h₁ hx

中文:
定理 contMDiffWithinAt_congr
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : f₁ x = f x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_iff
-/
theorem contMDiffWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff h₁ hx

/--
theorem `ContMDiffWithinAt.congr_of_mem` / 定理 `ContMDiffWithinAt.congr_of_mem`

English:
theorem ContMDiffWithinAt.congr_of_mem
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_mem h h₁ hx

中文:
定理 ContMDiffWithinAt.congr_of_mem
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_mem h h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_of_mem
-/
theorem ContMDiffWithinAt.congr_of_mem
    (h : ContMDiffWithinAt I I' n f s x) (h₁ : forall y in s, f₁ y = f y) (hx : x in s) :
    ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_mem h h₁ hx

/--
theorem `contMDiffWithinAt_congr_of_mem` / 定理 `contMDiffWithinAt_congr_of_mem`

English:
theorem contMDiffWithinAt_congr_of_mem
  given: (h₁ : forall y in s, f₁ y = f y) (hx : x in s)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_mem h₁ hx

中文:
定理 contMDiffWithinAt_congr_of_mem
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : x in s)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_mem h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_iff_of_mem
-/
theorem contMDiffWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx : x in s) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_mem h₁ hx

/--
theorem `ContMDiffWithinAt.congr_of_eventuallyEq` / 定理 `ContMDiffWithinAt.congr_of_eventuallyEq`

English:
theorem ContMDiffWithinAt.congr_of_eventuallyEq
  statement: (h : ContMDiffWithinAt I I' n f s x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx

中文:
定理 ContMDiffWithinAt.congr_of_eventuallyEq
  结论: (h : ContMDiffWithinAt I I' n f s x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_of_eventuallyEq
-/
theorem ContMDiffWithinAt.congr_of_eventuallyEq (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx

/--
theorem `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem ContMDiffWithinAt.congr_of_eventuallyEq_of_mem
  statement: (h : ContMDiffWithinAt I I' n f s x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq_of_mem h h₁ hx

中文:
定理 ContMDiffWithinAt.congr_of_eventuallyEq_of_mem
  结论: (h : ContMDiffWithinAt I I' n f s x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq_of_mem h h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_of_eventuallyEq_of_mem
-/
theorem ContMDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_of_eventuallyEq_of_mem h h₁ hx

/--
theorem `Filter.EventuallyEq.contMDiffWithinAt_iff` / 定理 `Filter.EventuallyEq.contMDiffWithinAt_iff`

English:
theorem Filter.EventuallyEq.contMDiffWithinAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

中文:
定理 滤子.EventuallyEq.contMDiffWithinAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropWithinAt_congr_iff_of_eventuallyEq
-/
theorem Filter.EventuallyEq.contMDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

/--
theorem `ContMDiffAt.congr_of_eventuallyEq` / 定理 `ContMDiffAt.congr_of_eventuallyEq`

English:
theorem ContMDiffAt.congr_of_eventuallyEq
  given: (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_of_eventuallyEq h h₁

中文:
定理 ContMDiffAt.congr_of_eventuallyEq
  条件: (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_of_eventuallyEq h h₁

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropAt_congr_of_eventuallyEq
-/
theorem ContMDiffAt.congr_of_eventuallyEq (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_of_eventuallyEq h h₁

/--
theorem `Filter.EventuallyEq.contMDiffAt_iff` / 定理 `Filter.EventuallyEq.contMDiffAt_iff`

English:
theorem Filter.EventuallyEq.contMDiffAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_iff_of_eventuallyEq h₁

中文:
定理 滤子.EventuallyEq.contMDiffAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_iff_of_eventuallyEq h₁

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropAt_congr_iff_of_eventuallyEq
-/
theorem Filter.EventuallyEq.contMDiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x ↔ ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp n).liftPropAt_congr_iff_of_eventuallyEq h₁

/--
theorem `ContMDiffOn.congr` / 定理 `ContMDiffOn.congr`

English:
theorem ContMDiffOn.congr
  given: (h : ContMDiffOn I I' n f s) (h₁ : forall y in s, f₁ y = f y)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_congr h h₁

中文:
定理 ContMDiffOn.congr
  条件: (h : ContMDiffOn I I' n f s) (h₁ : 对任意 y in s, f₁ y = f y)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_congr h h₁

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropOn_congr
-/
theorem ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : forall y in s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr h h₁

/--
theorem `contMDiffOn_congr` / 定理 `contMDiffOn_congr`

English:
theorem contMDiffOn_congr
  given: (h₁ : forall y in s, f₁ y = f y)
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_congr_iff h₁

中文:
定理 contMDiffOn_congr
  条件: (h₁ : 对任意 y in s, f₁ y = f y)
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_congr_iff h₁

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropOn_congr_iff
-/
theorem contMDiffOn_congr (h₁ : forall y in s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_congr_iff h₁

/--
theorem `ContMDiffOn.congr_mono` / 定理 `ContMDiffOn.congr_mono`

English:
theorem ContMDiffOn.congr_mono
  statement: (hf : ContMDiffOn I I' n f s) (h₁ : forall y in s₁, f₁ y = f y)
  proof: (hf.mono hs).congr h₁

中文:
定理 ContMDiffOn.congr_mono
  结论: (hf : ContMDiffOn I I' n f s) (h₁ : 对任意 y in s₁, f₁ y = f y)
  证明: (hf.mono hs).congr h₁

Depends on / 依赖: hf.mono
-/
theorem ContMDiffOn.congr_mono (hf : ContMDiffOn I I' n f s) (h₁ : forall y in s₁, f₁ y = f y)
    (hs : s₁ subseteq s) : ContMDiffOn I I' n f₁ s₁ :=
  (hf.mono hs).congr h₁

/--
theorem `ContMDiff.congr` / 定理 `ContMDiff.congr`

English:
theorem ContMDiff.congr
  given: (h : ContMDiff I I' n f) (h₁ : forall y, f₁ y = f y)
  proof: by
  rw [← contMDiffOn_univ] at h ⊢
  exact (contMDiffOn_congr fun y _ => h₁ y).mpr h

中文:
定理 ContMDiff.congr
  条件: (h : ContMDiff I I' n f) (h₁ : 对任意 y, f₁ y = f y)
  证明: by
  rw [← contMDiffOn_univ] at h ⊢
  exact (contMDiffOn_congr fun y _ => h₁ y).mpr h

Depends on / 依赖: contMDiffOn_congr, contMDiffOn_univ
-/
theorem ContMDiff.congr (h : ContMDiff I I' n f) (h₁ : forall y, f₁ y = f y) :
    ContMDiff I I' n f₁ := by
  rw [← contMDiffOn_univ] at h ⊢
  exact (contMDiffOn_congr fun y _ => h₁ y).mpr h

/--
theorem `contMDiff_congr` / 定理 `contMDiff_congr`

English:
theorem contMDiff_congr
  given: (h₁ : forall y, f₁ y = f y)
  proof: by
  simp_rw [← contMDiffOn_univ]
  exact contMDiffOn_congr fun y _ => h₁ y

中文:
定理 contMDiff_congr
  条件: (h₁ : 对任意 y, f₁ y = f y)
  证明: by
  simp_rw [← contMDiffOn_univ]
  exact contMDiffOn_congr fun y _ => h₁ y

Depends on / 依赖: contMDiffOn_congr, contMDiffOn_univ, simp_rw
-/
theorem contMDiff_congr (h₁ : forall y, f₁ y = f y) :
    ContMDiff I I' n f₁ ↔ ContMDiff I I' n f := by
  simp_rw [← contMDiffOn_univ]
  exact contMDiffOn_congr fun y _ => h₁ y

/-! ### Locality -/


/--
theorem `contMDiffOn_of_locally_contMDiffOn` / 定理 `contMDiffOn_of_locally_contMDiffOn`

English:
theorem contMDiffOn_of_locally_contMDiffOn
  proof: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_locally_liftPropOn h

中文:
定理 contMDiffOn_of_locally_contMDiffOn
  证明: (contDiffWithinAt_localInvariantProp n).liftPropOn_of_locally_liftPropOn h

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropOn_of_locally_liftPropOn
-/
theorem contMDiffOn_of_locally_contMDiffOn
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f (s inter u)) : ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp n).liftPropOn_of_locally_liftPropOn h

/--
theorem `contMDiff_of_locally_contMDiffOn` / 定理 `contMDiff_of_locally_contMDiffOn`

English:
theorem contMDiff_of_locally_contMDiffOn
  given: (h : forall x, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f u)
  proof: (contDiffWithinAt_localInvariantProp n).liftProp_of_locally_liftPropOn h

中文:
定理 contMDiff_of_locally_contMDiffOn
  条件: (h : 对任意 x, 存在 u, 是开集 u ∧ x in u ∧ ContMDiffOn I I' n f u)
  证明: (contDiffWithinAt_localInvariantProp n).liftProp_of_locally_liftPropOn h

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftProp_of_locally_liftPropOn
-/
theorem contMDiff_of_locally_contMDiffOn (h : forall x, exists u, IsOpen u ∧ x in u ∧ ContMDiffOn I I' n f u) :
    ContMDiff I I' n f :=
  (contDiffWithinAt_localInvariantProp n).liftProp_of_locally_liftPropOn h
