/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Lengths of paths in manifolds

Consider a manifold in which the tangent spaces have an enormed structure. Then one defines
`pathELength γ a b` as the length of the path `γ : ℝ → M` between `a` and `b`, i.e., the integral
of the norm of its derivative on `Icc a b`.

We give several ways to write this quantity (as an integral over `Icc`, or `Ioo`, or the subtype
`Icc`, using either `mfderiv` or `mfderivWithin`).

We show that this notion is invariant under reparameterization by a monotone map, in
`pathELength_comp_of_monotoneOn`.

We define `riemannianEDist x y` as the infimum of the length of `C^1` paths between `x`
and `y`. We prove, in `exists_lt_locally_constant_of_riemannianEDist_lt`, that it is also the
infimum on such paths that are moreover locally constant near their endpoints. Such paths can be
glued while retaining the `C^1` property. We deduce that `riemannianEDist` satisfies the triangle
inequality, in `riemannianEDist_triangle`.

Note that `riemannianEDist x y` could also be named `finslerEDist x y` as we do not require that
the metric comes from an inner product space. However, as all the current applications in mathlib
are to Riemannian spaces we stick with the simpler name. This could be changed when Finsler
manifolds are studied in mathlib.
-/

@[expose] public section

open Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H} {n : Nat∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace Manifold

variable [forall (x : M), ENorm (TangentSpace% x)] {a b c a' b' : Real} {γ γ' : Real -> M}

variable (I) in
/-- The length on `Icc a b` of a path into a manifold, where the path is defined on the whole real
line.

We use the whole real line to avoid subtype hell in API, but this is equivalent to
considering functions on the manifold with boundary `Icc a b`, see
`lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`.

We use `mfderiv` instead of `mfderivWithin` in the definition as these coincide (apart from the two
endpoints which have zero measure) and `mfderiv` is easier to manipulate. However, we give
a lemma `pathELength_eq_integral_mfderivWithin_Icc` to rewrite with the `mfderivWithin` form. -/
irreducible_def pathELength (γ : Real -> M) (a b : Real) : Real>=0∞ :=
  ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ

/--
lemma `pathELength_eq_lintegral_mfderiv_Icc` / 引理 `pathELength_eq_lintegral_mfderiv_Icc`

English:
lemma pathELength_eq_lintegral_mfderiv_Icc
  proof: by simp [pathELength]

中文:
引理 pathELength_eq_lintegral_mfderiv_Icc
  证明: by simp [pathELength]

Depends on / 依赖: pathELength
-/
lemma pathELength_eq_lintegral_mfderiv_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv% γ t 1‖ₑ := by simp [pathELength]

/--
lemma `pathELength_eq_lintegral_mfderiv_Ioo` / 引理 `pathELength_eq_lintegral_mfderiv_Ioo`

English:
lemma pathELength_eq_lintegral_mfderiv_Ioo
  proof: by
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [restrict_Ioo_eq_restrict_Icc]

中文:
引理 pathELength_eq_lintegral_mfderiv_Ioo
  证明: by
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [restrict_Ioo_eq_restrict_Icc]

Depends on / 依赖: pathELength_eq_lintegral_mfderiv_Icc, restrict_Ioo_eq_restrict_Icc
-/
lemma pathELength_eq_lintegral_mfderiv_Ioo :
    pathELength I γ a b = ∫⁻ t in Ioo a b, ‖mfderiv% γ t 1‖ₑ := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [restrict_Ioo_eq_restrict_Icc]

/--
lemma `pathELength_eq_lintegral_mfderivWithin_Icc` / 引理 `pathELength_eq_lintegral_mfderivWithin_Icc`

English:
lemma pathELength_eq_lintegral_mfderivWithin_Icc
  proof: by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  rw [mfderivWithin_of_mem_n

中文:
引理 pathELength_eq_lintegral_mfderivWithin_Icc
  证明: by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  rw [mfderivWithin_of_mem_n
-/
lemma pathELength_eq_lintegral_mfderivWithin_Icc :
    pathELength I γ a b = ∫⁻ t in Icc a b, ‖mfderiv[Icc a b] γ t 1‖ₑ := by
  -- we use that the endpoints have measure 0 to rewrite on `Ioo a b`, where `mfderiv` and
  -- `mfderivWithin` coincide.
  rw [pathELength_eq_lintegral_mfderiv_Icc]; rw [← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  rw [mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2

/--
lemma `pathELength_self` / 引理 `pathELength_self`

English:
lemma pathELength_self
  statement: pathELength I γ a a = 0
  proof: by
  simp [pathELength]

中文:
引理 pathELength_self
  结论: pathELength I γ a a = 0
  证明: by
  simp [pathELength]
-/
@[simp] lemma pathELength_self : pathELength I γ a a = 0 := by
  simp [pathELength]

/--
lemma `pathELength_congr_Ioo` / 引理 `pathELength_congr_Ioo`

English:
lemma pathELength_congr_Ioo
  given: (h : EqOn γ γ' (Ioo a b))
  proof: by
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha using h ha

中文:
引理 pathELength_congr_Ioo
  条件: (h : EqOn γ γ' (开区间 a b))
  证明: by
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha using h ha

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.mfderiv_eq, Ioo_mem_nhds, filter_upwards, measurableSet_Ioo, mfderiv_eq, pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun
-/
lemma pathELength_congr_Ioo (h : EqOn γ γ' (Ioo a b)) :
    pathELength I γ a b = pathELength I γ' a b := by
  simp only [pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have A : γ t = γ' t := h ht
  congr! 2
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with a ha using h ha

/--
lemma `pathELength_congr` / 引理 `pathELength_congr`

English:
lemma pathELength_congr
  given: (h : EqOn γ γ' (Icc a b))
  statement: pathELength I γ a b = pathELength I γ' a b
  proof: pathELength_congr_Ioo (fun _ hx => h ⟨hx.1.le, hx.2.le⟩)

@[gcongr]

中文:
引理 pathELength_congr
  条件: (h : EqOn γ γ' (闭区间 a b))
  结论: pathELength I γ a b = pathELength I γ' a b
  证明: pathELength_congr_Ioo (fun _ hx => h ⟨hx.1.le, hx.2.le⟩)

@[gcongr]

Depends on / 依赖: pathELength_congr_Ioo
-/
lemma pathELength_congr (h : EqOn γ γ' (Icc a b)) : pathELength I γ a b = pathELength I γ' a b :=
  pathELength_congr_Ioo (fun _ hx => h ⟨hx.1.le, hx.2.le⟩)

@[gcongr]
/--
lemma `pathELength_mono` / 引理 `pathELength_mono`

English:
lemma pathELength_mono
  given: (h : a' <= a) (h' : b <= b')
  proof: by
  simpa [pathELength_eq_lintegral_mfderiv_Icc] using lintegral_mono_set (Icc_subset_Icc h h')

中文:
引理 pathELength_mono
  条件: (h : a' <= a) (h' : b <= b')
  证明: by
  simpa [pathELength_eq_lintegral_mfderiv_Icc] using lintegral_mono_set (Icc_subset_Icc h h')

Depends on / 依赖: Icc_subset_Icc, lintegral_mono_set, pathELength_eq_lintegral_mfderiv_Icc
-/
lemma pathELength_mono (h : a' <= a) (h' : b <= b') :
    pathELength I γ a b <= pathELength I γ a' b' := by
  simpa [pathELength_eq_lintegral_mfderiv_Icc] using lintegral_mono_set (Icc_subset_Icc h h')

/--
lemma `pathELength_add` / 引理 `pathELength_add`

English:
lemma pathELength_add
  given: (h : a <= b) (h' : b <= c)
  proof: by
  symm
  have : Icc a c = Icc a b union Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength]; rw [this]; rw [lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb => (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

中文:
引理 pathELength_add
  条件: (h : a <= b) (h' : b <= c)
  证明: by
  symm
  have : Icc a c = Icc a b union Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength]; rw [this]; rw [lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb => (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

Depends on / 依赖: Icc_union_Ioc_eq_Icc, disjoint_iff_forall_ne, disjoint_iff_forall_ne.mpr, lintegral_union, measurableSet_Ioc, pathELength, restrict_Ioc_eq_restrict_Icc, trans_lt
-/
lemma pathELength_add (h : a <= b) (h' : b <= c) :
    pathELength I γ a b + pathELength I γ b c = pathELength I γ a c := by
  symm
  have : Icc a c = Icc a b union Ioc b c := (Icc_union_Ioc_eq_Icc h h').symm
  rw [pathELength]; rw [this]; rw [lintegral_union measurableSet_Ioc]; swap
  · exact disjoint_iff_forall_ne.mpr (fun a ha b hb => (ha.2.trans_lt hb.1).ne)
  simp [restrict_Ioc_eq_restrict_Icc, pathELength]

attribute [local instance] Measure.Subtype.measureSpace

/--
lemma `lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc` / 引理 `lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc`

English:
lemma lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc
  statement: {a b : Real}
  proof: by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc a b -> Real) volume
    (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasurePreserving.lintegral_comp_emb this
   

中文:
引理 lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc
  结论: {a b : 实数}
  证明: by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc a b -> Real) volume
    (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasurePreserving.lintegral_comp_emb this
   

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, MeasurePreserving, MeasurePreserving.lintegral_comp_emb, Subtype, Subtype.val, h.out.le, lintegral_comp_emb, measurableSet_Icc, measurePreserving_subtype_coe, mfderivWithin_comp_projIcc_one, pathELength_eq_lintegral_mfderivWithin_Icc, projIcc, restrict, simp_rw, subtype_coe, volume, volume.restrict
-/
lemma lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc {a b : Real}
    [h : Fact (a < b)] {γ : Icc a b -> M} :
    ∫⁻ t, ‖mfderiv% γ t 1‖ₑ = pathELength I (γ ∘ (projIcc a b h.out.le)) a b := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  simp_rw [← mfderivWithin_comp_projIcc_one]
  have : MeasurePreserving (Subtype.val : Icc a b -> Real) volume
    (volume.restrict (Icc a b)) := measurePreserving_subtype_coe measurableSet_Icc
  rw [← MeasurePreserving.lintegral_comp_emb this
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  congr
  ext t
  have : t = projIcc a b h.out.le (t : Real) := by simp
  congr

open MeasureTheory

variable [forall (x : M), ENormSMulClass Real (TangentSpace% x)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pathELength_comp_of_monotoneOn` / 引理 `pathELength_comp_of_monotoneOn`

English:
lemma pathELength_comp_of_monotoneOn
  statement: {f : Real -> Real} (h : a <= b) (hf : MonotoneOn f (Icc a b))
  proof: by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f a) (f b) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b)

中文:
引理 pathELength_comp_of_monotoneOn
  结论: {f : 实数 -> 实数} (h : a <= b) (hf : MonotoneOn f (闭区间 a b))
  证明: by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f a) (f b) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b)

Depends on / 依赖: HasDerivWithinAt, continuousOn, derivWithin, eq_or_lt, f.continuousOn.image_Icc_of_monotoneOn, f_im, h.eq_or_lt, h.le, hasDerivWithinAt, image_Icc_of_monotoneOn, lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn, measurableSet_Icc, mfderiv, pathELength_eq_lintegral_mfderivWithin_Icc, setLIntegral_congr_fun
-/
lemma pathELength_comp_of_monotoneOn {f : Real -> Real} (h : a <= b) (hf : MonotoneOn f (Icc a b))
    (h'f : DifferentiableOn Real f (Icc a b)) (hγ : MDiff[Icc (f a) (f b)] γ) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f a) (f b) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f a) (f b) := h'f.continuousOn.image_Icc_of_monotoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have : (mfderiv[Icc a b] (γ ∘ f) t) =
      (mfderiv[Icc (f a) (f b)] γ (f t)) ∘L mfderiv[Icc a b] f t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : mfderiv[Icc a b] f t 1 = derivWithin f (Icc a b) t • (1 : TangentSpace% (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 <= derivWithin f (Icc a b) t := hf.derivWithin_nonneg
  simp only [map_smul, enorm_smul, ← Real.enorm_of_nonneg this, f_im]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pathELength_comp_of_antitoneOn` / 引理 `pathELength_comp_of_antitoneOn`

English:
lemma pathELength_comp_of_antitoneOn
  statement: {f : Real -> Real} (h : a <= b) (hf : AntitoneOn f (Icc a b))
  proof: by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f b) (f a) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b)

中文:
引理 pathELength_comp_of_antitoneOn
  结论: {f : 实数 -> 实数} (h : a <= b) (hf : AntitoneOn f (闭区间 a b))
  证明: by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f b) (f a) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b)

Depends on / 依赖: HasDerivWithinAt, continuousOn, derivWithin, eq_or_lt, f.continuousOn.image_Icc_of_antitoneOn, f_im, h.eq_or_lt, h.le, hasDerivWithinAt, image_Icc_of_antitoneOn, lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn, measurableSet_Icc, mfderiv, pathELength_eq_lintegral_mfderivWithin_Icc, setLIntegral_congr_fun
-/
lemma pathELength_comp_of_antitoneOn {f : Real -> Real} (h : a <= b) (hf : AntitoneOn f (Icc a b))
    (h'f : DifferentiableOn Real f (Icc a b)) (hγ : MDiff[Icc (f b) (f a)] γ) :
    pathELength I (γ ∘ f) a b = pathELength I γ (f b) (f a) := by
  rcases h.eq_or_lt with rfl | h
  · simp
  have f_im : f '' (Icc a b) = Icc (f b) (f a) := h'f.continuousOn.image_Icc_of_antitoneOn h.le hf
  simp only [pathELength_eq_lintegral_mfderivWithin_Icc, ← f_im]
  have B (t) (ht : t in Icc a b) : HasDerivWithinAt f (derivWithin f (Icc a b) t) (Icc a b) t :=
    (h'f t ht).hasDerivWithinAt
  rw [lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Icc B hf]
  apply setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have : (mfderiv[Icc a b] (γ ∘ f) t)
      = (mfderiv[Icc (f b) (f a)] γ (f t)) ∘L mfderiv[Icc a b] f t := by
    rw [← f_im] at hγ ⊢
    apply mfderivWithin_comp
    · apply hγ _ (mem_image_of_mem _ ht)
    · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact h'f _ ht
    · exact subset_preimage_image _ _
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc h _ ht
  rw [this]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : mfderiv[Icc a b] f t 1
      = derivWithin f (Icc a b) t • (1 : TangentSpace% (f t)) := by
    simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin, smul_eq_mul, mul_one]
    rfl
  rw [this]
  have : 0 <= -derivWithin f (Icc a b) t := by simp [hf.derivWithin_nonpos]
  simp only [map_smul, enorm_smul, f_im, ← Real.enorm_of_nonneg this, enorm_neg]

section

variable {x y z : M} {r : Real>=0∞} {a b : Real}

variable (I) in
/-- The Riemannian extended distance between two points, in a manifold where the tangent spaces
have an extended norm, defined as the infimum of the lengths of `C^1` paths between the points. -/
noncomputable irreducible_def riemannianEDist (x y : M) : Real>=0∞ :=
  ⨅ (γ : Path x y) (_ : CMDiff 1 γ), ∫⁻ x, ‖mfderiv% γ x 1‖ₑ

/--
lemma `riemannianEDist_le_pathELength` / 引理 `riemannianEDist_le_pathELength`

English:
lemma riemannianEDist_le_pathELength
  statement: {γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ)
  proof: by
  let η : Real ->ᴬ[Real] Real := ContinuousAffineMap.lineMap a b
  have hη : CMDiff[Icc 0 1] 1 (γ ∘ η) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    

中文:
引理 riemannianEDist_le_pathELength
  结论: {γ : 实数 -> M} (hγ : CMDiff[闭区间 a b] 1 γ)
  证明: by
  let η : Real ->ᴬ[Real] Real := ContinuousAffineMap.lineMap a b
  have hη : CMDiff[Icc 0 1] 1 (γ ∘ η) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
    

Depends on / 依赖: CMDiff, ContinuousAffineMap, ContinuousAffineMap.coe_lineMap_eq, ContinuousAffineMap.lineMap, Function, Function.comp_apply, coe_lineMap_eq, comp_apply, contDiff, contDiff.contDiffOn, contDiffOn, contMDiffOn_comp_projIcc_iff, contMDiffOn_iff_contDiffOn, image_subset_iff, lineMap, projIcc_of_mem, segment_eq_image_lineMap, unitInterval
-/
lemma riemannianEDist_le_pathELength {γ : Real -> M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a <= b) :
    riemannianEDist I x y <= pathELength I γ a b := by
  let η : Real ->ᴬ[Real] Real := ContinuousAffineMap.lineMap a b
  have hη : CMDiff[Icc 0 1] 1 (γ ∘ η) := by
    apply hγ.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact η.contDiff.contDiffOn
    · rw [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap]
      simp [hab]
  let f : unitInterval -> M := fun t => (γ ∘ η) t
  have hf : CMDiff 1 f := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hη.congr (fun t ht => ?_)
    simp only [Function.comp_apply, f, projIcc_of_mem, ht]
  let g : Path x y := by
    refine ⟨⟨f, hf.continuous⟩, ?_, ?_⟩ <;>
    simp [f, η, ContinuousAffineMap.coe_lineMap_eq, ha, hb]
  have A : riemannianEDist I x y <= ∫⁻ x, ‖mfderiv% g x 1‖ₑ := by
    rw [riemannianEDist]; exact biInf_le _ hf
  apply A.trans_eq
  rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]
  have E : pathELength I (g ∘ projIcc 0 1 zero_le_one) 0 1 = pathELength I (γ ∘ η) 0 1 := by
    apply pathELength_congr (fun t ht => ?_)
    simp only [Function.comp_apply, ht, projIcc_of_mem]
    rfl
  rw [E]; rw [pathELength_comp_of_monotoneOn zero_le_one _ η.differentiableOn]
  · simp [η, ContinuousAffineMap.coe_lineMap_eq]
  · simpa [η, ContinuousAffineMap.coe_lineMap_eq] using hγ.mdifferentiableOn one_ne_zero
  · apply (AffineMap.lineMap_mono hab).monotoneOn

omit [forall (x : M), ENormSMulClass Real (TangentSpace% x)] in
/--
lemma `exists_lt_of_riemannianEDist_lt` / 引理 `exists_lt_of_riemannianEDist_lt`

English:
lemma exists_lt_of_riemannianEDist_lt
  given: (hr : riemannianEDist I x y < r)
  proof: by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

中文:
引理 存在_lt_of_riemannianEDist_lt
  条件: (hr : riemannianEDist I x y < r)
  证明: by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

Depends on / 依赖: contMDiffOn_comp_projIcc_iff, exists_prop, iInf_lt_iff, lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc, projIcc, riemannianEDist, zero_le_one
-/
lemma exists_lt_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) :
    exists γ : Real -> M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧
    pathELength I γ 0 1 < r := by
  simp only [riemannianEDist, iInf_lt_iff, exists_prop] at hr
  rcases hr with ⟨γ, γ_smooth, hγ⟩
  refine ⟨γ ∘ (projIcc 0 1 zero_le_one), by simp, by simp,
    contMDiffOn_comp_projIcc_iff.2 γ_smooth, ?_⟩
  rwa [← lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

/--
lemma `exists_lt_locally_constant_of_riemannianEDist_lt` / 引理 `exists_lt_locally_constant_of_riemannianEDist_lt`

English:
lemma exists_lt_locally_constant_of_riemannianEDist_lt
  proof: by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with length `< r`. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`.

  Note that

中文:
引理 存在_lt_locally_constant_of_riemannianEDist_lt
  证明: by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with length `< r`. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`.

  Note that
-/
lemma exists_lt_locally_constant_of_riemannianEDist_lt
    (hr : riemannianEDist I x y < r) (hab : a < b) :
    exists γ : Real -> M, γ a = x ∧ γ b = y ∧ CMDiff 1 γ ∧
    pathELength I γ a b < r ∧ γ =ᶠ[𝓝 a] (fun _ => x) ∧ γ =ᶠ[𝓝 b] (fun _ => y) := by
  /- We start from a path from `x` to `y` defined on `[0, 1]` with length `< r`. Then, we
  reparameterize it using a smooth monotone map `η` from `[a, b]` to `[0, 1]` which is moreover
  locally constant around `a` and `b`.
  Such a map is easy to build with `Real.smoothTransition`.

  Note that this is a very standard construction in differential topology.
  TODO: refactor once we have more differential topology in Mathlib and this gets duplicated. -/
  rcases exists_lt_of_riemannianEDist_lt hr with ⟨γ, hγx, hγy, γ_smooth, hγ⟩
  rcases exists_between hab with ⟨a', haa', ha'b⟩
  rcases exists_between ha'b with ⟨b', ha'b', hb'b⟩
  let η (t : Real) : Real := Real.smoothTransition ((b' - a')⁻¹ * (t - a'))
  have A (t) (ht : t < a') : η t = 0 := by
    simp only [η, Real.smoothTransition.zero_iff_nonpos]
    apply mul_nonpos_of_nonneg_of_nonpos
    · simpa using ha'b'.le
    · linarith
  have A' (t) (ht : t < a') : (γ ∘ η) t = x := by simp [A t ht, hγx]
  have B (t) (ht : b' < t) : η t = 1 := by
    simp only [η, Real.smoothTransition.eq_one_iff_one_le, inv_mul_eq_div]
    rw [one_le_div₀] <;> linarith
  have B' (t) (ht : b' < t) : (γ ∘ η) t = y := by simp [B t ht, hγy]
  refine ⟨γ ∘ η, A' _ haa', B' _ hb'b, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiffOn_univ]
    apply γ_smooth.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      fun_prop
    · intro t ht
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · convert! hγ using 1
    rw [← A a haa']; rw [← B b hb'b]
    apply pathELength_comp_of_monotoneOn hab.le
    · apply Monotone.monotoneOn
      apply Real.smoothTransition.monotone.comp
      intro t u htu
      dsimp only
      gcongr
    · simp only [η]
      apply (ContDiff.contDiffOn _).differentiableOn one_ne_zero
      fun_prop
    · rw [A a haa', B b hb'b]
      apply γ_smooth.mdifferentiableOn one_ne_zero
  · filter_upwards [Iio_mem_nhds haa'] with t ht using A' t ht
  · filter_upwards [Ioi_mem_nhds hb'b] with t ht using B' t ht

/--
lemma `riemannianEDist_self` / 引理 `riemannianEDist_self`

English:
lemma riemannianEDist_self
  statement: riemannianEDist I x x = 0
  proof: by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : Real) => x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)

中文:
引理 riemannianEDist_self
  结论: riemannianEDist I x x = 0
  证明: by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : Real) => x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)

Depends on / 依赖: bot_le, contMDiffOn_const, le_antisymm, le_rfl, riemannianEDist_le_pathELength, trans_eq
-/
lemma riemannianEDist_self : riemannianEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (riemannianEDist_le_pathELength (γ := fun (t : Real) => x) (a := 0) (b := 0)
    contMDiffOn_const rfl rfl le_rfl).trans_eq (by simp)

/--
lemma `riemannianEDist_comm` / 引理 `riemannianEDist_comm`

English:
lemma riemannianEDist_comm
  statement: riemannianEDist I x y = riemannianEDist I y x
  proof: by
  suffices H : forall x y, riemannianEDist I y x <= riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr => ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, hγ, -⟩
  let η : Real -> Real := 

中文:
引理 riemannianEDist_comm
  结论: riemannianEDist I x y = riemannianEDist I y x
  证明: by
  suffices H : forall x y, riemannianEDist I y x <= riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr => ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, hγ, -⟩
  let η : Real -> Real := 

Depends on / 依赖: CMDiff, _smooth.comp, contMDiff_iff_contDiff, exists_lt_locally_constant_of_riemannianEDist_lt, fun_prop, h_smooth, le_antisymm, le_of_forall_gt, pathELength, riemannianEDist, riemannianEDist_le, zero_lt_one
-/
lemma riemannianEDist_comm : riemannianEDist I x y = riemannianEDist I y x := by
  suffices H : forall x y, riemannianEDist I y x <= riemannianEDist I x y from le_antisymm (H y x) (H x y)
  intro x y
  apply le_of_forall_gt (fun r hr => ?_)
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    with ⟨γ, γ0, γ1, γ_smooth, hγ, -⟩
  let η : Real -> Real := fun t => -t
  have h_smooth : CMDiff 1 (γ ∘ η) := by
    apply γ_smooth.comp ?_
    simp only [contMDiff_iff_contDiff]
    fun_prop
  have : riemannianEDist I y x <= pathELength I (γ ∘ η) (η 1) (η 0) := by
    apply riemannianEDist_le_pathELength h_smooth.contMDiffOn <;> simp [η, γ0, γ1]
  rw [← pathELength_comp_of_antitoneOn zero_le_one] at this; rotate_left
  · exact monotone_id.neg.antitoneOn _
  · exact differentiableOn_neg _
  · exact h_smooth.contMDiffOn.mdifferentiableOn one_ne_zero
  apply this.trans_lt
  convert! hγ
  ext t
  simp [η]

/--
lemma `riemannianEDist_triangle` / 引理 `riemannianEDist_triangle`

English:
lemma riemannianEDist_triangle
  proof: by
  apply le_of_forall_gt (fun r hr => ?_)
  rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨u, hu, v, hv, huv⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hu zero_lt_one with
    ⟨γ₁, hγ₁0, hγ₁1, hγ₁_smooth, hγ₁, -, hγ₁_const⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt

中文:
引理 riemannianEDist_triangle
  证明: by
  apply le_of_forall_gt (fun r hr => ?_)
  rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨u, hu, v, hv, huv⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hu zero_lt_one with
    ⟨γ₁, hγ₁0, hγ₁1, hγ₁_smooth, hγ₁, -, hγ₁_const⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt

Depends on / 依赖: ContMDif, ENNReal, ENNReal.exists_add_lt_of_add_lt, exists_add_lt_of_add_lt, exists_lt_locally_constant_of_riemannianEDist_lt, le_of_forall_gt, one_lt_two, pathELength, piecewise, riemannianEDist, riemannianEDist_le_pathELength, zero_lt_one
-/
lemma riemannianEDist_triangle :
    riemannianEDist I x z <= riemannianEDist I x y + riemannianEDist I y z := by
  apply le_of_forall_gt (fun r hr => ?_)
  rcases ENNReal.exists_add_lt_of_add_lt hr with ⟨u, hu, v, hv, huv⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hu zero_lt_one with
    ⟨γ₁, hγ₁0, hγ₁1, hγ₁_smooth, hγ₁, -, hγ₁_const⟩
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hv one_lt_two with
    ⟨γ₂, hγ₂1, hγ₂2, hγ₂_smooth, hγ₂, hγ₂_const, -⟩
  let γ := piecewise (Iic 1) γ₁ γ₂
  have : riemannianEDist I x z <= pathELength I γ 0 2 := by
    apply riemannianEDist_le_pathELength
    · apply ContMDiff.contMDiffOn
      exact ContMDiff.piecewise_Iic hγ₁_smooth hγ₂_smooth (hγ₁_const.trans hγ₂_const.symm)
    · simp [γ, hγ₁0]
    · simp [γ, hγ₂2]
    · exact zero_le_two
  apply this.trans_lt (lt_trans ?_ huv)
  rw [← pathELength_add zero_le_one one_le_two]
  gcongr
  · convert! hγ₁ using 1
    apply pathELength_congr
    intro t ht
    simp [γ, ht.2]
  · convert! hγ₂ using 1
    apply pathELength_congr_Ioo
    intro t ht
    simp [γ, ht.1]

end

end Manifold
