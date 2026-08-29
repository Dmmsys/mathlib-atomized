/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Density
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `α` and `γ` be two measurable spaces, where either `α` is countable or `γ` is
countably generated. Let `κ, η : Kernel α γ` be finite kernels.
Then there exists a function `Kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `Kernel.singularPart κ η : Kernel α γ` such that
* `κ = Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η`,
* for all `a : α`, `Kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `Kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `Kernel.withDensity η (Kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

When `γ` is countably generated, the construction of the derivative starts from `Kernel.density`:
for two finite kernels `κ' : Kernel α (γ × β)` and `η' : Kernel α γ` with `fst κ' ≤ η'`,
the function `density κ' η' : α → γ → Set β → ℝ` is jointly measurable in the first two arguments
and satisfies that for all `a : α` and all measurable sets `s : Set β` and `A : Set γ`,
`∫ x in A, density κ' η' a x s ∂(η' a) = (κ' a (A ×ˢ s)).toReal`.
We use that definition for `β = Unit` and `κ' = map κ (fun a ↦ (a, ()))`. We can't choose `η' = η`
in general because we might not have `κ ≤ η`, but if we could, we would get a measurable function
`f` with the property `κ = withDensity η f`, which is the decomposition we want for `κ ≤ η`.
To circumvent that difficulty, we take `η' = κ + η` and thus define `rnDerivAux κ η`.
Finally, `rnDeriv κ η a x` is given by
`ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)`.
Up to some conversions between `ℝ` and `ℝ≥0`, the singular part is
`withDensity (κ + η) (rnDerivAux κ (κ + η) - (1 - rnDerivAux κ (κ + η)) * rnDeriv κ η)`.

The countably generated measurable space assumption is not needed to have a decomposition for
measures, but the additional difficulty with kernels is to obtain joint measurability of the
derivative. This is why we can't simply define `rnDeriv κ η` by `a ↦ (κ a).rnDeriv (ν a)`
everywhere unless `α` is countable (although `rnDeriv κ η` has that value almost everywhere).
See the construction of `Kernel.density` for details on how the countably generated hypothesis
is used.

## Main definitions

* `ProbabilityTheory.Kernel.rnDeriv`: a function `α → γ → ℝ≥0∞` jointly measurable on `α × γ`
* `ProbabilityTheory.Kernel.singularPart`: a `Kernel α γ`

## Main statements

* `ProbabilityTheory.Kernel.mutuallySingular_singularPart`: for all `a : α`,
  `Kernel.singularPart κ η a ⟂ₘ η a`
* `ProbabilityTheory.Kernel.rnDeriv_add_singularPart`:
  `Kernel.withDensity η (Kernel.rnDeriv κ η) + Kernel.singularPart κ η = κ`
* `ProbabilityTheory.Kernel.measurableSet_absolutelyContinuous` : the set `{a | κ a ≪ η a}`
  is Measurable
* `ProbabilityTheory.Kernel.measurableSet_mutuallySingular` : the set `{a | κ a ⟂ₘ η a}`
  is Measurable

Uniqueness results: if `κ = η.withDensity f + ξ` for measurable `f` and `ξ` is such that
`ξ a ⟂ₘ η a` for some `a : α` then
* `ProbabilityTheory.Kernel.eq_rnDeriv`: `f a =ᵐ[η a] Kernel.rnDeriv κ η a`
* `ProbabilityTheory.Kernel.eq_singularPart`: `ξ a = Kernel.singularPart κ η a`

## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

-/

@[expose] public section

open MeasureTheory Set Filter ENNReal

open scoped NNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Kernel α γ}
  [hαγ : MeasurableSpace.CountableOrCountablyGenerated α γ]

open scoped Classical in
/-- Auxiliary function used to define `ProbabilityTheory.Kernel.rnDeriv` and
`ProbabilityTheory.Kernel.singularPart`.

This has the properties we want for a Radon-Nikodym derivative only if `κ ≪ ν`. The definition of
`rnDeriv κ η` will be built from `rnDerivAux κ (κ + η)`. -/
noncomputable
/--
Definition of `rnDerivAux` / `rnDerivAux` 的定义

English:
definition rnDerivAux
  signature: (κ η : Kernel α γ) (a : α) (x : γ)
  body: if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a => (a, ()))) η a x univ

中文:
定义 rnDerivAux
  签名: (κ η : 核 α γ) (a : α) (x : γ)
  定义体: if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a => (a, ()))) η a x univ

Depends on / 依赖: Countable, countableOrCountablyGenerated, countableOrCountablyGenerated.resolve_left, density, resolve_left, rnDeriv, toReal
-/
def rnDerivAux (κ η : Kernel α γ) (a : α) (x : γ) : Real :=
  if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a => (a, ()))) η a x univ

/--
lemma `rnDerivAux_nonneg` / 引理 `rnDerivAux_nonneg`

English:
lemma rnDerivAux_nonneg
  given: (hκη : κ <= η) {a : α} {x : γ}
  statement: 0 <= rnDerivAux κ η a x
  proof: by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

中文:
引理 rnDerivAux_nonneg
  条件: (hκη : κ <= η) {a : α} {x : γ}
  结论: 0 <= rnDerivAux κ η a x
  证明: by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, countableOrCountablyGenerated, countableOrCountablyGenerated.resolve_left, density_nonneg, fst_map_id_prod, measurable_const, resolve_left, rnDerivAux, split_ifs, toReal_nonneg, trans_le
-/
lemma rnDerivAux_nonneg (hκη : κ <= η) {a : α} {x : γ} : 0 <= rnDerivAux κ η a x := by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

/--
lemma `rnDerivAux_le_one` / 引理 `rnDerivAux_le_one`

English:
lemma rnDerivAux_le_one
  given: [IsFiniteKernel η] (hκη : κ <= η) {a : α}
  proof: by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

@[fun_prop]

中文:
引理 rnDerivAux_le_one
  条件: [是FiniteKernel η] (hκη : κ <= η) {a : α}
  证明: by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

@[fun_prop]

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, ENNReal.toReal_le_of_le_ofReal, Measure, Measure.rnDeriv_le_one_of_le, Pi.one_apply, countableOrCountablyGenerated, countableOrCountablyGenerated.resolve_left, density_le_one, filter_upwards, fst_map_id_prod, hx_le_one, measurable_const, ofReal_one, one_apply, resolve_left, rnDerivAux, rnDeriv_le_one_of_le, simp_rw, split_ifs
-/
lemma rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ <= η) {a : α} :
    rnDerivAux κ η a <=ᵐ[η a] 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

@[fun_prop]
/--
lemma `measurable_rnDerivAux` / 引理 `measurable_rnDerivAux`

English:
lemma measurable_rnDerivAux
  given: (κ η : Kernel α γ)
  proof: by
  simp_rw [rnDerivAux]
  split_ifs with hα
· refine Measurable.ennreal_toReal measurable_from_prod_countable_right'
      (fun a => Measure.measurable_rnDeriv (κ a) (η a)) fun a a' c ha'_mem_a => ?_
    have h_eq : forall κ : Kernel α γ, κ a' = κ a := fun κ => by
      ext s hs
      exact mem_of_mem_measurableAtom ha'_mem_a
        (Kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
    rw [h_eq κ]; rw [h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ

@[fun_prop]

中文:
引理 measurable_rnDerivAux
  条件: (κ η : 核 α γ)
  证明: by
  simp_rw [rnDerivAux]
  split_ifs with hα
· refine Measurable.ennreal_toReal measurable_from_prod_countable_right'
      (fun a => Measure.measurable_rnDeriv (κ a) (η a)) fun a a' c ha'_mem_a => ?_
    have h_eq : forall κ : Kernel α γ, κ a' = κ a := fun κ => by
      ext s hs
      exact mem_of_mem_measurableAtom ha'_mem_a
        (Kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
    rw [h_eq κ]; rw [h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ

@[fun_prop]

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measurable, Measurable.ennreal_toReal, MeasurableSet, MeasurableSet.u, Measure, Measure.measurable_rnDeriv, _mem_a, countableOrCountablyGenerated, countableOrCountablyGenerated.resolve_left, ennreal_toReal, h_eq, measurableSet_singleton, measurable_coe, measurable_density, measurable_from_prod_countable_right, measurable_rnDeriv, mem_of_mem_measurableAtom, resolve_left
-/
lemma measurable_rnDerivAux (κ η : Kernel α γ) :
    Measurable (fun p : α × γ => Kernel.rnDerivAux κ η p.1 p.2) := by
  simp_rw [rnDerivAux]
  split_ifs with hα
· refine Measurable.ennreal_toReal measurable_from_prod_countable_right'
      (fun a => Measure.measurable_rnDeriv (κ a) (η a)) fun a a' c ha'_mem_a => ?_
    have h_eq : forall κ : Kernel α γ, κ a' = κ a := fun κ => by
      ext s hs
      exact mem_of_mem_measurableAtom ha'_mem_a
        (Kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
    rw [h_eq κ]; rw [h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ

@[fun_prop]
/--
lemma `measurable_rnDerivAux_right` / 引理 `measurable_rnDerivAux_right`

English:
lemma measurable_rnDerivAux_right
  given: (κ η : Kernel α γ) (a : α)
  proof: by fun_prop

中文:
引理 measurable_rnDerivAux_right
  条件: (κ η : 核 α γ) (a : α)
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
lemma measurable_rnDerivAux_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ => rnDerivAux κ η a x) := by fun_prop

/--
lemma `setLIntegral_rnDerivAux` / 引理 `setLIntegral_rnDerivAux`

English:
lemma setLIntegral_rnDerivAux
  statement: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.setLIntegral_rnDeriv h_ac]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [setLIntegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs]; rw [map_apply' _ (by fun_prop) _ (hs.prod MeasurableSet.univ)]
    congr 1 with x
    simp

中文:
引理 setL整数egral_rnDerivAux
  结论: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.setLIntegral_rnDeriv h_ac]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [setLIntegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs]; rw [map_apply' _ (by fun_prop) _ (hs.prod MeasurableSet.univ)]
    congr 1 with x
    simp

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Measure, Measure.absolutelyContinuous_of_le, Measure.rnDeriv_lt_top, Measure.setLIntegral_rnDeriv, absolutelyContinuous_of_le, bot_le, countableOrCountablyGenerated, countableOrCountablyGenerated.resolve_left, filter_upwards, fst_map_id_prod, h_ac, h_le, hx_lt, hx_lt.ne, le_add_of_nonneg_right, measurable_const, ofReal_toReal, resolve_left
-/
lemma setLIntegral_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s := by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.setLIntegral_rnDeriv h_ac]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [setLIntegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs]; rw [map_apply' _ (by fun_prop) _ (hs.prod MeasurableSet.univ)]
    congr 1 with x
    simp

/--
lemma `withDensity_rnDerivAux` / 引理 `withDensity_rnDerivAux`

English:
lemma withDensity_rnDerivAux
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  ext a s hs
  rw [Kernel.withDensity_apply']
  swap; · fun_prop
  simp_rw [ofNNReal_toNNReal]
  exact setLIntegral_rnDerivAux κ η a hs

中文:
引理 withDensity_rnDerivAux
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  ext a s hs
  rw [Kernel.withDensity_apply']
  swap; · fun_prop
  simp_rw [ofNNReal_toNNReal]
  exact setLIntegral_rnDerivAux κ η a hs

Depends on / 依赖: Kernel, Kernel.withDensity_apply, fun_prop, ofNNReal_toNNReal, setLIntegral_rnDerivAux, simp_rw, withDensity_apply
-/
lemma withDensity_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x)) = κ := by
  ext a s hs
  rw [Kernel.withDensity_apply']
  swap; · fun_prop
  simp_rw [ofNNReal_toNNReal]
  exact setLIntegral_rnDerivAux κ η a hs

/--
lemma `withDensity_one_sub_rnDerivAux` / 引理 `withDensity_one_sub_rnDerivAux`

English:
lemma withDensity_one_sub_rnDerivAux
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  simp_rw [ofNNReal_toNNReal, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · fun_prop
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx

中文:
引理 withDensity_one_sub_rnDerivAux
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  simp_rw [ofNNReal_toNNReal, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · fun_prop
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx

Depends on / 依赖: FunLike, FunLike.coe_add, Measure, Measure.coe, Pi.add_apply, Real.toNNReal, add_apply, bot_le, coe_add, h_le, le_add_of_nonneg_right, rnDerivAux, toNNReal, withDensity
-/
lemma withDensity_one_sub_rnDerivAux (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) = η := by
  have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  simp_rw [ofNNReal_toNNReal, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · fun_prop
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx

/--
Definition of `mutuallySingularSet` / `mutuallySingularSet` 的定义

English:
definition mutuallySingularSet
  signature: (κ η : Kernel α γ)
  body: {p | 1 <= rnDerivAux κ (κ + η) p.1 p.2}

中文:
定义 mutuallySingularSet
  签名: (κ η : 核 α γ)
  定义体: {p | 1 <= rnDerivAux κ (κ + η) p.1 p.2}

Depends on / 依赖: rnDerivAux
-/
def mutuallySingularSet (κ η : Kernel α γ) : Set (α × γ) := {p | 1 <= rnDerivAux κ (κ + η) p.1 p.2}

/--
Definition of `mutuallySingularSetSlice` / `mutuallySingularSetSlice` 的定义

English:
definition mutuallySingularSetSlice
  signature: (κ η : Kernel α γ) (a : α)
  body: {x | 1 <= rnDerivAux κ (κ + η) a x}

中文:
定义 mutuallySingularSetSlice
  签名: (κ η : 核 α γ) (a : α)
  定义体: {x | 1 <= rnDerivAux κ (κ + η) a x}

Depends on / 依赖: rnDerivAux
-/
def mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) : Set γ :=
  {x | 1 <= rnDerivAux κ (κ + η) a x}

/--
lemma `mem_mutuallySingularSetSlice` / 引理 `mem_mutuallySingularSetSlice`

English:
lemma mem_mutuallySingularSetSlice
  given: (κ η : Kernel α γ) (a : α) (x : γ)
  proof: by
  rw [mutuallySingularSetSlice]; rw [mem_ofPred]

中文:
引理 mem_mutuallySingularSetSlice
  条件: (κ η : 核 α γ) (a : α) (x : γ)
  证明: by
  rw [mutuallySingularSetSlice]; rw [mem_ofPred]

Depends on / 依赖: mem_ofPred, mutuallySingularSetSlice
-/
lemma mem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x in mutuallySingularSetSlice κ η a ↔ 1 <= rnDerivAux κ (κ + η) a x := by
  rw [mutuallySingularSetSlice]; rw [mem_ofPred]

/--
lemma `notMem_mutuallySingularSetSlice` / 引理 `notMem_mutuallySingularSetSlice`

English:
lemma notMem_mutuallySingularSetSlice
  given: (κ η : Kernel α γ) (a : α) (x : γ)
  proof: by
  simp [mutuallySingularSetSlice]

中文:
引理 notMem_mutuallySingularSetSlice
  条件: (κ η : 核 α γ) (a : α) (x : γ)
  证明: by
  simp [mutuallySingularSetSlice]

Depends on / 依赖: mutuallySingularSetSlice
-/
lemma notMem_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) (x : γ) :
    x ∉ mutuallySingularSetSlice κ η a ↔ rnDerivAux κ (κ + η) a x < 1 := by
  simp [mutuallySingularSetSlice]

/--
lemma `measurableSet_mutuallySingularSet` / 引理 `measurableSet_mutuallySingularSet`

English:
lemma measurableSet_mutuallySingularSet
  given: (κ η : Kernel α γ)
  proof: measurable_rnDerivAux κ (κ + η) measurableSet_Ici

中文:
引理 measurableSet_mutuallySingularSet
  条件: (κ η : 核 α γ)
  证明: measurable_rnDerivAux κ (κ + η) measurableSet_Ici

Depends on / 依赖: measurableSet_Ici, measurable_rnDerivAux
-/
lemma measurableSet_mutuallySingularSet (κ η : Kernel α γ) :
    MeasurableSet (mutuallySingularSet κ η) :=
  measurable_rnDerivAux κ (κ + η) measurableSet_Ici

/--
lemma `measurableSet_mutuallySingularSetSlice` / 引理 `measurableSet_mutuallySingularSetSlice`

English:
lemma measurableSet_mutuallySingularSetSlice
  given: (κ η : Kernel α γ) (a : α)
  proof: measurable_prodMk_left (measurableSet_mutuallySingularSet κ η)

中文:
引理 measurableSet_mutuallySingularSetSlice
  条件: (κ η : 核 α γ) (a : α)
  证明: measurable_prodMk_left (measurableSet_mutuallySingularSet κ η)

Depends on / 依赖: measurableSet_mutuallySingularSet, measurable_prodMk_left
-/
lemma measurableSet_mutuallySingularSetSlice (κ η : Kernel α γ) (a : α) :
    MeasurableSet (mutuallySingularSetSlice κ η a) :=
  measurable_prodMk_left (measurableSet_mutuallySingularSet κ η)

/--
lemma `measure_mutuallySingularSetSlice` / 引理 `measure_mutuallySingularSetSlice`

English:
lemma measure_mutuallySingularSetSlice
  statement: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  suffices withDensity (κ + η) (fun a x => Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 <= rnDerivAux κ (κ + η) a x} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
  simp_rw [ofNNReal_toNNReal]
  rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  rotate_left
  · exact (measurableSet_singleton 0).preimage (by fun_prop)
  · fun_prop
  · fun_prop
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_ofPred_eq] at hx
  simp [hx]

中文:
引理 measure_mutuallySingularSetSlice
  结论: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  suffices withDensity (κ + η) (fun a x => Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 <= rnDerivAux κ (κ + η) a x} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
  simp_rw [ofNNReal_toNNReal]
  rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  rotate_left
  · exact (measurableSet_singleton 0).preimage (by fun_prop)
  · fun_prop
  · fun_prop
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_ofPred_eq] at hx
  simp [hx]

Depends on / 依赖: EventuallyEq, Kernel, Kernel.withDensity_apply, Real.toNNReal, ae_of_all, ae_restrict_iff, fun_prop, lintegral_eq_zero_iff, measurableSet_singleton, mem_ofPred_eq, ofNNReal_toNNReal, preimage, rnDerivAux, rotate_left, simp_rw, toNNReal, withDensity, withDensity_apply, withDensity_one_sub_rnDerivAux
-/
lemma measure_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    η a (mutuallySingularSetSlice κ η a) = 0 := by
  suffices withDensity (κ + η) (fun a x => Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 <= rnDerivAux κ (κ + η) a x} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
  simp_rw [ofNNReal_toNNReal]
  rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  rotate_left
  · exact (measurableSet_singleton 0).preimage (by fun_prop)
  · fun_prop
  · fun_prop
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_ofPred_eq] at hx
  simp [hx]

/-- Radon-Nikodym derivative of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
irreducible_def rnDeriv (κ η : Kernel α γ) (a : α) (x : γ) : Real>=0∞ :=
  ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)

/--
lemma `rnDeriv_def'` / 引理 `rnDeriv_def'`

English:
lemma rnDeriv_def'
  given: (κ η : Kernel α γ)
  proof: by ext; rw [rnDeriv_def]

@[fun_prop]

中文:
引理 rnDeriv_def'
  条件: (κ η : 核 α γ)
  证明: by ext; rw [rnDeriv_def]

@[fun_prop]

Depends on / 依赖: rnDeriv_def
-/
lemma rnDeriv_def' (κ η : Kernel α γ) :
    rnDeriv κ η = fun a x => ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
      / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x) := by ext; rw [rnDeriv_def]

@[fun_prop]
/--
lemma `measurable_rnDeriv` / 引理 `measurable_rnDeriv`

English:
lemma measurable_rnDeriv
  given: (κ η : Kernel α γ)
  proof: by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

@[fun_prop]

中文:
引理 measurable_rnDeriv
  条件: (κ η : 核 α γ)
  证明: by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

@[fun_prop]

Depends on / 依赖: ennreal_ofReal, ennreal_ofReal.div, measurable_const, measurable_const.sub, measurable_rnDerivAux, rnDeriv_def, simp_rw
-/
lemma measurable_rnDeriv (κ η : Kernel α γ) :
    Measurable (fun p : α × γ => rnDeriv κ η p.1 p.2) := by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

@[fun_prop]
/--
lemma `measurable_rnDeriv_right` / 引理 `measurable_rnDeriv_right`

English:
lemma measurable_rnDeriv_right
  given: (κ η : Kernel α γ) (a : α)
  proof: by fun_prop

中文:
引理 measurable_rnDeriv_right
  条件: (κ η : 核 α γ) (a : α)
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
lemma measurable_rnDeriv_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ => rnDeriv κ η a x) := by fun_prop

/--
lemma `rnDeriv_eq_top_iff` / 引理 `rnDeriv_eq_top_iff`

English:
lemma rnDeriv_eq_top_iff
  given: (κ η : Kernel α γ) (a : α) (x : γ)
  proof: by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_ofPred_eq, and_iff_right_iff_imp]
  exact fun h => zero_lt_one.trans_le h

中文:
引理 rnDeriv_eq_top_iff
  条件: (κ η : 核 α γ) (a : α) (x : γ)
  证明: by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_ofPred_eq, and_iff_right_iff_imp]
  exact fun h => zero_lt_one.trans_le h

Depends on / 依赖: ENNReal, ENNReal.div_eq_top, ENNReal.ofReal_eq_zero, ENNReal.ofReal_ne_top, and_iff_right_iff_imp, and_true, div_eq_top, mem_ofPred_eq, mutuallySingularSet, ne_eq, not_false_eq_true, not_le, ofReal_eq_zero, ofReal_ne_top, or_false, rnDeriv, trans_le, tsub_le_iff_right, zero_add, zero_lt_one
-/
lemma rnDeriv_eq_top_iff (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ (a, x) in mutuallySingularSet κ η := by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_ofPred_eq, and_iff_right_iff_imp]
  exact fun h => zero_lt_one.trans_le h

/--
lemma `rnDeriv_eq_top_iff'` / 引理 `rnDeriv_eq_top_iff'`

English:
lemma rnDeriv_eq_top_iff'
  given: (κ η : Kernel α γ) (a : α) (x : γ)
  proof: by
  rw [rnDeriv_eq_top_iff]; rw [mutuallySingularSet]; rw [mutuallySingularSetSlice]; rw [mem_ofPred]; rw [mem_ofPred]

中文:
引理 rnDeriv_eq_top_iff'
  条件: (κ η : 核 α γ) (a : α) (x : γ)
  证明: by
  rw [rnDeriv_eq_top_iff]; rw [mutuallySingularSet]; rw [mutuallySingularSetSlice]; rw [mem_ofPred]; rw [mem_ofPred]

Depends on / 依赖: mem_ofPred, mutuallySingularSet, mutuallySingularSetSlice, rnDeriv_eq_top_iff
-/
lemma rnDeriv_eq_top_iff' (κ η : Kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ x in mutuallySingularSetSlice κ η a := by
  rw [rnDeriv_eq_top_iff]; rw [mutuallySingularSet]; rw [mutuallySingularSetSlice]; rw [mem_ofPred]; rw [mem_ofPred]

/-- Singular part of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
irreducible_def singularPart (κ η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    Kernel α γ :=
  withDensity (κ + η) (fun a x => Real.toNNReal (rnDerivAux κ (κ + η) a x)
    - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x)

/--
lemma `measurable_singularPart_fun` / 引理 `measurable_singularPart_fun`

English:
lemma measurable_singularPart_fun
  given: (κ η : Kernel α γ)
  proof: by fun_prop

中文:
引理 measurable_singularPart_fun
  条件: (κ η : 核 α γ)
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
lemma measurable_singularPart_fun (κ η : Kernel α γ) :
    Measurable (fun p : α × γ => Real.toNNReal (rnDerivAux κ (κ + η) p.1 p.2)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) p.1 p.2) * rnDeriv κ η p.1 p.2) := by fun_prop

/--
lemma `measurable_singularPart_fun_right` / 引理 `measurable_singularPart_fun_right`

English:
lemma measurable_singularPart_fun_right
  given: (κ η : Kernel α γ) (a : α)
  proof: by
  change Measurable ((Function.uncurry fun a b =>
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b => (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prodMk_left

中文:
引理 measurable_singularPart_fun_right
  条件: (κ η : 核 α γ) (a : α)
  证明: by
  change Measurable ((Function.uncurry fun a b =>
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b => (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prodMk_left

Depends on / 依赖: ENNReal, ENNReal.ofReal, Function, Function.uncurry, Measurable, measurable_prodMk_left, measurable_singularPart_fun, ofReal, rnDeriv, rnDerivAux, uncurry
-/
lemma measurable_singularPart_fun_right (κ η : Kernel α γ) (a : α) :
    Measurable (fun x : γ => Real.toNNReal (rnDerivAux κ (κ + η) a x)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x) := by
  change Measurable ((Function.uncurry fun a b =>
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b => (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prodMk_left

/--
lemma `singularPart_compl_mutuallySingularSetSlice` / 引理 `singularPart_compl_mutuallySingularSetSlice`

English:
lemma singularPart_compl_mutuallySingularSetSlice
  statement: (κ η : Kernel α γ) [IsSFiniteKernel κ]
  proof: by
  rw [singularPart]; rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  all_goals simp_rw [ofNNReal_toNNReal]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_compl_iff, mutuallySingularSetSlice, mem_ofPred, not_le] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]; rw [tsub_self]; rw [Pi.zero_apply]
  · simp only [ne_eq, sub_eq_zero, hx.ne', not_false_eq_true]
  · simp only [sub_nonneg, hx.le]
  · simp only [sub_pos, hx]

中文:
引理 singularPart_compl_mutuallySingularSetSlice
  结论: (κ η : 核 α γ) [是SFiniteKernel κ]
  证明: by
  rw [singularPart]; rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  all_goals simp_rw [ofNNReal_toNNReal]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_compl_iff, mutuallySingularSetSlice, mem_ofPred, not_le] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]; rw [tsub_self]; rw [Pi.zero_apply]
  · simp only [ne_eq, sub_eq_zero, hx.ne', not_false_eq_true]
  · simp only [sub_nonneg, hx.le]
  · simp only [sub_pos, hx]

Depends on / 依赖: EventuallyEq, Kernel, Kernel.withDensity_apply, ae_of_all, ae_restrict_iff, all_goals, lintegral_eq_zero_iff, measurableSet_preimage, measurableSet_singleton, measurable_singularPart_fun, measurable_singularPart_fun_right, mem_compl_iff, mem_ofPred, mutuallySingularSetSlice, not_le, ofNNReal_toNNReal, rnDeriv, rotate_left, simp_rw, singularPart
-/
lemma singularPart_compl_mutuallySingularSetSlice (κ η : Kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [singularPart]; rw [Kernel.withDensity_apply']; rw [lintegral_eq_zero_iff]; rw [EventuallyEq]; rw [ae_restrict_iff]
  all_goals simp_rw [ofNNReal_toNNReal]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx => ?_)
  simp only [mem_compl_iff, mutuallySingularSetSlice, mem_ofPred, not_le] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]; rw [tsub_self]; rw [Pi.zero_apply]
  · simp only [ne_eq, sub_eq_zero, hx.ne', not_false_eq_true]
  · simp only [sub_nonneg, hx.le]
  · simp only [sub_pos, hx]

/--
lemma `singularPart_of_subset_compl_mutuallySingularSetSlice` / 引理 `singularPart_of_subset_compl_mutuallySingularSetSlice`

English:
lemma singularPart_of_subset_compl_mutuallySingularSetSlice
  statement: [IsSFiniteKernel κ]
  proof: measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

中文:
引理 singularPart_of_subset_compl_mutuallySingularSetSlice
  结论: [是SFiniteKernel κ]
  证明: measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

Depends on / 依赖: measure_mono_null, singularPart_compl_mutuallySingularSetSlice
-/
lemma singularPart_of_subset_compl_mutuallySingularSetSlice [IsSFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s subseteq (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 :=
  measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

/--
lemma `singularPart_of_subset_mutuallySingularSetSlice` / 引理 `singularPart_of_subset_mutuallySingularSetSlice`

English:
lemma singularPart_of_subset_mutuallySingularSetSlice
  statement: [IsFiniteKernel κ]
  proof: by
  have hs' : forall x in s, 1 <= rnDerivAux κ (κ + η) a x := fun _ hx => hs hx
  rw [singularPart]; rw [Kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine setLIntegral_congr_fun_ae hsm ?_
        have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)

中文:
引理 singularPart_of_subset_mutuallySingularSetSlice
  结论: [是FiniteKernel κ]
  证明: by
  have hs' : forall x in s, 1 <= rnDerivAux κ (κ + η) a x := fun _ hx => hs hx
  rw [singularPart]; rw [Kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine setLIntegral_congr_fun_ae hsm ?_
        have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)

Depends on / 依赖: Kernel, Kernel.withDensity_apply, Real.toNNReal, bot_le, filter_upwards, h_le, le_add_of_nonneg_right, measurable_singularPart_fun, rnDeriv, rnDerivAux, rnDerivAux_le_one, setLIntegral_congr_fun_ae, singularPart, subsingleton_iff, toNNReal, withDensity_apply
-/
lemma singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s subseteq mutuallySingularSetSlice κ η a) :
    singularPart κ η a s = κ a s := by
  have hs' : forall x in s, 1 <= rnDerivAux κ (κ + η) a x := fun _ hx => hs hx
  rw [singularPart]; rw [Kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine setLIntegral_congr_fun_ae hsm ?_
        have h_le : κ <= κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)

/--
lemma `withDensity_rnDeriv_mutuallySingularSetSlice` / 引理 `withDensity_rnDeriv_mutuallySingularSetSlice`

English:
lemma withDensity_rnDeriv_mutuallySingularSetSlice
  statement: (κ η : Kernel α γ) [IsFiniteKernel κ]
  proof: by
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η

中文:
引理 withDensity_rnDeriv_mutuallySingularSetSlice
  结论: (κ η : 核 α γ) [是FiniteKernel κ]
  证明: by
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η

Depends on / 依赖: Kernel, Kernel.withDensity_apply, measurable_rnDeriv, measure_mutuallySingularSetSlice, setLIntegral_measure_zero, withDensity_apply
-/
lemma withDensity_rnDeriv_mutuallySingularSetSlice (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η

/--
lemma `withDensity_rnDeriv_of_subset_mutuallySingularSetSlice` / 引理 `withDensity_rnDeriv_of_subset_mutuallySingularSetSlice`

English:
lemma withDensity_rnDeriv_of_subset_mutuallySingularSetSlice
  statement: [IsFiniteKernel κ]
  proof: measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)

中文:
引理 withDensity_rnDeriv_of_subset_mutuallySingularSetSlice
  结论: [是FiniteKernel κ]
  证明: measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)

Depends on / 依赖: measure_mono_null, withDensity_rnDeriv_mutuallySingularSetSlice
-/
lemma withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s subseteq mutuallySingularSetSlice κ η a) :
    withDensity η (rnDeriv κ η) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)

/--
lemma `withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice` / 引理 `withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice`

English:
lemma withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
  proof: by
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this]; rw [← withDensity_mul]; rw [Kernel.withDensity_apply']
  rotate_left
  · fun_prop
  · fun_prop
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : forall x in s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← notMem_mutuallySingularSetSlice]
    exact fun x hx hx_mem => hs hx hx_mem
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine setLIntegral_congr_fun hsm (fun x hx => ?_)
      rw [ofNNReal_toNNReal]; rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := setLIntegral_rnDerivAux κ η a hsm

中文:
引理 withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
  证明: by
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this]; rw [← withDensity_mul]; rw [Kernel.withDensity_apply']
  rotate_left
  · fun_prop
  · fun_prop
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : forall x in s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← notMem_mutuallySingularSetSlice]
    exact fun x hx hx_mem => hs hx hx_mem
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine setLIntegral_congr_fun hsm (fun x hx => ?_)
      rw [ofNNReal_toNNReal]; rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := setLIntegral_rnDerivAux κ η a hsm

Depends on / 依赖: Kernel, Kernel.withDensity_apply, Real.toNNReal, fun_prop, hx_mem, measurable_rnDeriv, notMem_mutuallySingularSetSlice, rnDeriv, rnDerivAux, rnDeriv_def, rotate_left, simp_rw, toNNReal, withDensity, withDensity_apply, withDensity_mul, withDensity_one_sub_rnDerivAux
-/
lemma withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s subseteq (mutuallySingularSetSlice κ η a)ᶜ) :
    withDensity η (rnDeriv κ η) a s = κ a s := by
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x => Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this]; rw [← withDensity_mul]; rw [Kernel.withDensity_apply']
  rotate_left
  · fun_prop
  · fun_prop
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : forall x in s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← notMem_mutuallySingularSetSlice]
    exact fun x hx hx_mem => hs hx hx_mem
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine setLIntegral_congr_fun hsm (fun x hx => ?_)
      rw [ofNNReal_toNNReal]; rw [← ENNReal.ofReal_div_of_pos]; rw [div_eq_inv_mul]; rw [← ENNReal.ofReal_mul]; rw [← mul_assoc]; rw [mul_inv_cancel₀]; rw [one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := setLIntegral_rnDerivAux κ η a hsm

/--
lemma `mutuallySingular_singularPart` / 引理 `mutuallySingular_singularPart`

English:
lemma mutuallySingular_singularPart
  statement: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

中文:
引理 mutuallySingular_singularPart
  结论: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

Depends on / 依赖: measurableSet_mutuallySingularSetSlice, measure_mutuallySingularSetSlice, mutuallySingularSetSlice, singularPart_compl_mutuallySingularSetSlice
-/
lemma mutuallySingular_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    singularPart κ η a ⟂ₘ η a := by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

/--
lemma `rnDeriv_add_singularPart` / 引理 `rnDeriv_add_singularPart`

English:
lemma rnDeriv_add_singularPart
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  ext a s hs
  rw [← inter_union_sdiff s (mutuallySingularSetSlice κ η a)]
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono inter_subset_right le_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) inter_subset_right]; rw [singularPart_of_subset_compl_mutuallySingularSetSlice (sdiff_subset_iff.mpr (by simp))]; rw [add_zero]; rw [withDensity_rnDeriv_of_subset_mutuallySingularSetSlice inter_subset_right]; rw [zero_add]; rw [withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (sdiff_subset_iff.mpr (by simp))]; rw [add_comm]

中文:
引理 rnDeriv_add_singularPart
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  ext a s hs
  rw [← inter_union_sdiff s (mutuallySingularSetSlice κ η a)]
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono inter_subset_right le_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) inter_subset_right]; rw [singularPart_of_subset_compl_mutuallySingularSetSlice (sdiff_subset_iff.mpr (by simp))]; rw [add_zero]; rw [withDensity_rnDeriv_of_subset_mutuallySingularSetSlice inter_subset_right]; rw [zero_add]; rw [withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (sdiff_subset_iff.mpr (by simp))]; rw [add_comm]

Depends on / 依赖: Disjoint, Disjoint.mono, FunLike, FunLike.coe_add, Measure, Measure.coe_add, Pi.add_apply, add_apply, add_zero, coe_add, disjoint_sdiff_right, hs.diff, hs.inter, inter_subset_right, inter_union_sdiff, le_rfl, measurableSet_mutuallySingularSetSlice, measure_union, mutuallySingularSetSlice, sdiff_subset_iff
-/
lemma rnDeriv_add_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity η (rnDeriv κ η) + singularPart κ η = κ := by
  ext a s hs
  rw [← inter_union_sdiff s (mutuallySingularSetSlice κ η a)]
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono inter_subset_right le_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) inter_subset_right]; rw [singularPart_of_subset_compl_mutuallySingularSetSlice (sdiff_subset_iff.mpr (by simp))]; rw [add_zero]; rw [withDensity_rnDeriv_of_subset_mutuallySingularSetSlice inter_subset_right]; rw [zero_add]; rw [withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (sdiff_subset_iff.mpr (by simp))]; rw [add_comm]

section EqZeroIff

/--
lemma `singularPart_eq_zero_iff_apply_eq_zero` / 引理 `singularPart_eq_zero_iff_apply_eq_zero`

English:
lemma singularPart_eq_zero_iff_apply_eq_zero
  statement: (κ η : Kernel α γ) [IsSFiniteKernel κ]
  proof: by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [singularPart_compl_mutuallySingularSetSlice]; rw [add_zero]

中文:
引理 singularPart_eq_zero_iff_apply_eq_zero
  结论: (κ η : 核 α γ) [是SFiniteKernel κ]
  证明: by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [singularPart_compl_mutuallySingularSetSlice]; rw [add_zero]

Depends on / 依赖: Measure, Measure.measure_univ_eq_zero, add_zero, disjoint_compl_right, measurableSet_mutuallySingularSetSlice, measure_union, measure_univ_eq_zero, mutuallySingularSetSlice, singularPart_compl_mutuallySingularSetSlice
-/
lemma singularPart_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ singularPart κ η a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [singularPart_compl_mutuallySingularSetSlice]; rw [add_zero]

/--
lemma `withDensity_rnDeriv_eq_zero_iff_apply_eq_zero` / 引理 `withDensity_rnDeriv_eq_zero_iff_apply_eq_zero`

English:
lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero
  statement: (κ η : Kernel α γ) [IsFiniteKernel κ]
  proof: by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [withDensity_rnDeriv_mutuallySingularSetSlice]; rw [zero_add]

中文:
引理 withDensity_rnDeriv_eq_zero_iff_apply_eq_zero
  结论: (κ η : 核 α γ) [是FiniteKernel κ]
  证明: by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [withDensity_rnDeriv_mutuallySingularSetSlice]; rw [zero_add]

Depends on / 依赖: Measure, Measure.measure_univ_eq_zero, disjoint_compl_right, measurableSet_mutuallySingularSetSlice, measure_union, measure_univ_eq_zero, mutuallySingularSetSlice, withDensity_rnDeriv_mutuallySingularSetSlice, zero_add
-/
lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0
      ↔ withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) union (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this]; rw [measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl]; rw [withDensity_rnDeriv_mutuallySingularSetSlice]; rw [zero_add]

/--
lemma `singularPart_eq_zero_iff_absolutelyContinuous` / 引理 `singularPart_eq_zero_iff_absolutelyContinuous`

English:
lemma singularPart_eq_zero_iff_absolutelyContinuous
  statement: (κ η : Kernel α γ)
  proof: by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)

中文:
引理 singularPart_eq_zero_iff_absolutelyContinuous
  结论: (κ η : 核 α γ)
  证明: by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.add_left_iff, Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular, add_apply, add_left_iff, add_zero, conv_rhs, eq_zero_of_absolutelyContinuous_of_mutuallySingular, mutuallySingular_singularPart, rnDeriv_add_singularPart, withDensity_absolutelyContinuous
-/
lemma singularPart_eq_zero_iff_absolutelyContinuous (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a ≪ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)

/--
lemma `withDensity_rnDeriv_eq_zero_iff_mutuallySingular` / 引理 `withDensity_rnDeriv_eq_zero_iff_mutuallySingular`

English:
lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular
  statement: (κ η : Kernel α γ)
  proof: by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)

中文:
引理 withDensity_rnDeriv_eq_zero_iff_mutuallySingular
  结论: (κ η : 核 α γ)
  证明: by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.rfl, Measure.MutuallySingular.add_left_iff, Measure.MutuallySingular.self_iff, MutuallySingular, add_apply, add_left_iff, conv_rhs, mono_ac, mutuallySingular_singularPart, rnDeriv, rnDeriv_add_singularPart, self_iff, withDensity_absolutelyContinuous, zero_add
-/
lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, add_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)

/--
lemma `singularPart_eq_zero_iff_measure_eq_zero` / 引理 `singularPart_eq_zero_iff_measure_eq_zero`

English:
lemma singularPart_eq_zero_iff_measure_eq_zero
  statement: (κ η : Kernel α γ)
  proof: by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a

中文:
引理 singularPart_eq_zero_iff_measure_eq_zero
  结论: (κ η : 核 α γ)
  证明: by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a

Depends on / 依赖: FunLike, FunLike.coe_add, Kernel, Kernel.ext_iff, Measure, Measure.coe_add, Measure.ext_iff, Pi.add_apply, add_apply, coe_add, ext_iff, h_eq_add, measurableSet_mutuallySingularSetSlice, mutuallySingularSetSlice, rnDeriv_add_singularPart, simp_rw, singularPart_eq_zero_iff_apply_eq_zero, specialize, withDensity_rnDeriv_mutuallySingularSetSlice, zero_add
-/
lemma singularPart_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a

/--
lemma `withDensity_rnDeriv_eq_zero_iff_measure_eq_zero` / 引理 `withDensity_rnDeriv_eq_zero_iff_measure_eq_zero`

English:
lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero
  statement: (κ η : Kernel α γ)
  proof: by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a

中文:
引理 withDensity_rnDeriv_eq_zero_iff_measure_eq_zero
  结论: (κ η : 核 α γ)
  证明: by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a

Depends on / 依赖: FunLike, FunLike.coe_add, Kernel, Kernel.ext_iff, Measure, Measure.coe_add, Measure.ext_iff, Pi.add_apply, add_apply, add_zero, coe_add, ext_iff, h_eq_add, measurableSet_mutuallySingularSetSlice, mutuallySingularSetSlice, rnDeriv_add_singularPart, simp_rw, singularPart_compl_mutuallySingularSetSlice, specialize, withDensity_rnDeriv_eq_zero_iff_apply_eq_zero
-/
lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : Kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [Kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [FunLike.coe_add, Pi.add_apply, Measure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a

end EqZeroIff

/-- The set of points `a : α` such that `κ a ≪ η a` is measurable. -/
@[measurability]
/--
lemma `measurableSet_absolutelyContinuous` / 引理 `measurableSet_absolutelyContinuous`

English:
lemma measurableSet_absolutelyContinuous
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

中文:
引理 measurableSet_absolutelyContinuous
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

Depends on / 依赖: measurableSet_mutuallySingularSet, measurableSet_singleton, measurable_kernel_prodMk_left, simp_rw, singularPart_eq_zero_iff_absolutelyContinuous, singularPart_eq_zero_iff_measure_eq_zero
-/
lemma measurableSet_absolutelyContinuous (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≪ η a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

/-- The set of points `a : α` such that `κ a ⟂ₘ η a` is measurable. -/
@[measurability]
/--
lemma `measurableSet_mutuallySingular` / 引理 `measurableSet_mutuallySingular`

English:
lemma measurableSet_mutuallySingular
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)

@[simp]

中文:
引理 measurableSet_mutuallySingular
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)

@[simp]

Depends on / 依赖: measurableSet_mutuallySingularSet, measurableSet_singleton, measurable_kernel_prodMk_left, simp_rw, withDensity_rnDeriv_eq_zero_iff_measure_eq_zero, withDensity_rnDeriv_eq_zero_iff_mutuallySingular
-/
lemma measurableSet_mutuallySingular (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ⟂ₘ η a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prodMk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)

@[simp]
/--
lemma `singularPart_self` / 引理 `singularPart_self`

English:
lemma singularPart_self
  given: (κ : Kernel α γ) [IsFiniteKernel κ]
  statement: κ.singularPart κ = 0
  proof: by
  ext : 1; rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]

中文:
引理 singularPart_self
  条件: (κ : 核 α γ) [是FiniteKernel κ]
  结论: κ.singularPart κ = 0
  证明: by
  ext : 1; rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]

Depends on / 依赖: singularPart_eq_zero_iff_absolutelyContinuous, zero_apply
-/
lemma singularPart_self (κ : Kernel α γ) [IsFiniteKernel κ] : κ.singularPart κ = 0 := by
  ext : 1; rw [zero_apply, singularPart_eq_zero_iff_absolutelyContinuous]

section Unique

variable {ξ : Kernel α γ} {f : α -> γ -> Real>=0∞} [IsFiniteKernel η]

omit hαγ in
/--
lemma `eq_rnDeriv_measure` / 引理 `eq_rnDeriv_measure`

English:
lemma eq_rnDeriv_measure
  statement: (h : κ = η.withDensity f + ξ)
  proof: by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prodMk_left).aemeasurable hξ this

omit hαγ in

中文:
引理 eq_rnDeriv_measure
  结论: (h : κ = η.withDensity f + ξ)
  证明: by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prodMk_left).aemeasurable hξ this

omit hαγ in

Depends on / 依赖: add_apply, add_comm, aemeasurable, hf.comp, measurable_prodMk_left, withDensity, withDensity_apply
-/
lemma eq_rnDeriv_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] ∂(κ a)/∂(η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prodMk_left).aemeasurable hξ this

omit hαγ in
/--
lemma `eq_singularPart_measure` / 引理 `eq_singularPart_measure`

English:
lemma eq_singularPart_measure
  statement: (h : κ = η.withDensity f + ξ)
  proof: by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prodMk_left) hξ this

中文:
引理 eq_singularPart_measure
  结论: (h : κ = η.withDensity f + ξ)
  证明: by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prodMk_left) hξ this

Depends on / 依赖: add_apply, add_comm, eq_singularPart, hf.comp, measurable_prodMk_left, withDensity, withDensity_apply
-/
lemma eq_singularPart_measure (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = (κ a).singularPart (η a) := by
  have : κ a = ξ a + (η a).withDensity (f a) := by
    rw [h]; rw [add_apply]; rw [η.withDensity_apply hf]; rw [add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prodMk_left) hξ this

variable [IsFiniteKernel κ] {a : α}

/--
lemma `rnDeriv_eq_rnDeriv_measure` / 引理 `rnDeriv_eq_rnDeriv_measure`

English:
lemma rnDeriv_eq_rnDeriv_measure
  statement: rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
  proof: eq_rnDeriv_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

中文:
引理 rnDeriv_eq_rnDeriv_measure
  结论: rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)
  证明: eq_rnDeriv_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

Depends on / 依赖: classical, eq_rnDeriv_measure, measurable_rnDeriv, mutuallySingular_singularPart, nthRoots, of_equiv, rnDeriv_add_singularPart, rootsOfUnityEquivNthRoots
-/
lemma rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

/--
lemma `singularPart_eq_singularPart_measure` / 引理 `singularPart_eq_singularPart_measure`

English:
lemma singularPart_eq_singularPart_measure
  statement: singularPart κ η a = (κ a).singularPart (η a)
  proof: eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

中文:
引理 singularPart_eq_singularPart_measure
  结论: singularPart κ η a = (κ a).singularPart (η a)
  证明: eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

Depends on / 依赖: eq_singularPart_measure, measurable_rnDeriv, mutuallySingular_singularPart, rnDeriv_add_singularPart
-/
lemma singularPart_eq_singularPart_measure : singularPart κ η a = (κ a).singularPart (η a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ η).symm (measurable_rnDeriv κ η) a
    (mutuallySingular_singularPart κ η a)

/--
lemma `eq_rnDeriv` / 引理 `eq_rnDeriv`

English:
lemma eq_rnDeriv
  statement: (h : κ = η.withDensity f + ξ)
  proof: (eq_rnDeriv_measure h hf a hξ).trans rnDeriv_eq_rnDeriv_measure.symm

中文:
引理 eq_rnDeriv
  结论: (h : κ = η.withDensity f + ξ)
  证明: (eq_rnDeriv_measure h hf a hξ).trans rnDeriv_eq_rnDeriv_measure.symm

Depends on / 依赖: eq_rnDeriv_measure, rnDeriv_eq_rnDeriv_measure, rnDeriv_eq_rnDeriv_measure.symm
-/
lemma eq_rnDeriv (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    f a =ᵐ[η a] rnDeriv κ η a :=
  (eq_rnDeriv_measure h hf a hξ).trans rnDeriv_eq_rnDeriv_measure.symm

/--
lemma `eq_singularPart` / 引理 `eq_singularPart`

English:
lemma eq_singularPart
  statement: (h : κ = η.withDensity f + ξ)
  proof: (eq_singularPart_measure h hf a hξ).trans singularPart_eq_singularPart_measure.symm

中文:
引理 eq_singularPart
  结论: (h : κ = η.withDensity f + ξ)
  证明: (eq_singularPart_measure h hf a hξ).trans singularPart_eq_singularPart_measure.symm

Depends on / 依赖: eq_singularPart_measure, singularPart_eq_singularPart_measure, singularPart_eq_singularPart_measure.symm
-/
lemma eq_singularPart (h : κ = η.withDensity f + ξ)
    (hf : Measurable (Function.uncurry f)) (a : α) (hξ : ξ a ⟂ₘ η a) :
    ξ a = singularPart κ η a :=
  (eq_singularPart_measure h hf a hξ).trans singularPart_eq_singularPart_measure.symm

end Unique

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hκ
  signature: : IsFiniteKernel κ] [IsFiniteKernel η] :
  body: by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  rw [Kernel.withDensity_apply']; rw [setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae rnDeriv_eq_rnDeriv_measure]
  exact Measure.lintegral_rnDeriv_le.trans (measure_le_bound _ _ _)

中文:
实例 [hκ
  签名: : 是FiniteKernel κ] [是FiniteKernel η] :
  定义体: by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  rw [Kernel.withDensity_apply']; rw [setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae rnDeriv_eq_rnDeriv_measure]
  exact Measure.lintegral_rnDeriv_le.trans (measure_le_bound _ _ _)

Depends on / 依赖: DFunLike, DFunLike.coe_injective, Finite, Kernel, Kernel.withDensity_apply, Measure, Measure.lintegral_rnDeriv_le.trans, Monoid, Monoid.exponent, Monoid.pow_exponent_eq_one, MonoidHom, MonoidHom.ext, Subgroup, Subgroup.subtype, bound_lt_top, codRestrict, coe_injective, exponent, lintegral_congr_ae, lintegral_rnDeriv_le
-/
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (withDensity η (rnDeriv κ η)) := by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  rw [Kernel.withDensity_apply']; rw [setLIntegral_univ]
  swap; · exact measurable_rnDeriv κ η
  rw [lintegral_congr_ae rnDeriv_eq_rnDeriv_measure]
  exact Measure.lintegral_rnDeriv_le.trans (measure_le_bound _ _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hκ
  signature: : IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (singularPart κ η)
  body: by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

中文:
实例 [hκ
  签名: : 是FiniteKernel κ] [是FiniteKernel η] : 是FiniteKernel (singularPart κ η)
  定义体: by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

Depends on / 依赖: bound_lt_top, conv_rhs, h.le.trans, measure_le_bound, rnDeriv, rnDeriv_add_singularPart, self_le_add_left, singularPart, withDensity
-/
instance [hκ : IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (singularPart κ η) := by
  refine ⟨κ.bound, κ.bound_lt_top, fun a => ?_⟩
  have h : withDensity η (rnDeriv κ η) a univ + singularPart κ η a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ η]
    simp
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

/--
lemma `measurable_singularPart` / 引理 `measurable_singularPart`

English:
lemma measurable_singularPart
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  simp_rw [← κ.singularPart_eq_singularPart_measure, κ.singularPart_def η]
  exact Kernel.measurable_coe _ hs

中文:
引理 measurable_singularPart
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  simp_rw [← κ.singularPart_eq_singularPart_measure, κ.singularPart_def η]
  exact Kernel.measurable_coe _ hs

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measure, Measure.measurable_of_measurable_coe, measurable_coe, measurable_of_measurable_coe, simp_rw, singularPart_def, singularPart_eq_singularPart_measure
-/
lemma measurable_singularPart (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a => (κ a).singularPart (η a)) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  simp_rw [← κ.singularPart_eq_singularPart_measure, κ.singularPart_def η]
  exact Kernel.measurable_coe _ hs

/--
lemma `rnDeriv_self` / 引理 `rnDeriv_self`

English:
lemma rnDeriv_self
  given: (κ : Kernel α γ) [IsFiniteKernel κ] (a : α)
  statement: rnDeriv κ κ a =ᵐ[κ a] 1
  proof: (κ.rnDeriv_eq_rnDeriv_measure).trans (κ a).rnDeriv_self

中文:
引理 rnDeriv_self
  条件: (κ : 核 α γ) [是FiniteKernel κ] (a : α)
  结论: rnDeriv κ κ a =ᵐ[κ a] 1
  证明: (κ.rnDeriv_eq_rnDeriv_measure).trans (κ a).rnDeriv_self

Depends on / 依赖: rnDeriv_eq_rnDeriv_measure, rnDeriv_self
-/
lemma rnDeriv_self (κ : Kernel α γ) [IsFiniteKernel κ] (a : α) : rnDeriv κ κ a =ᵐ[κ a] 1 :=
  (κ.rnDeriv_eq_rnDeriv_measure).trans (κ a).rnDeriv_self

/--
lemma `rnDeriv_singularPart` / 引理 `rnDeriv_singularPart`

English:
lemma rnDeriv_singularPart
  given: (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α)
  proof: by
  filter_upwards [(singularPart κ ν).rnDeriv_eq_rnDeriv_measure,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1]; rw [h2]

中文:
引理 rnDeriv_singularPart
  条件: (κ ν : 核 α γ) [是FiniteKernel κ] [是FiniteKernel ν] (a : α)
  证明: by
  filter_upwards [(singularPart κ ν).rnDeriv_eq_rnDeriv_measure,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1]; rw [h2]

Depends on / 依赖: Measure, Measure.rnDeriv_eq_zero, filter_upwards, mutuallySingular_singularPart, rnDeriv_eq_rnDeriv_measure, rnDeriv_eq_zero, singularPart
-/
lemma rnDeriv_singularPart (κ ν : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0 := by
  filter_upwards [(singularPart κ ν).rnDeriv_eq_rnDeriv_measure,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1]; rw [h2]

/--
lemma `rnDeriv_lt_top` / 引理 `rnDeriv_lt_top`

English:
lemma rnDeriv_lt_top
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α}
  proof: by
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_ne_top _]
    with x heq htop using heq ▸ htop.lt_top

中文:
引理 rnDeriv_lt_top
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η] {a : α}
  证明: by
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_ne_top _]
    with x heq htop using heq ▸ htop.lt_top

Depends on / 依赖: filter_upwards, htop.lt_top, lt_top, rnDeriv_eq_rnDeriv_measure, rnDeriv_ne_top
-/
lemma rnDeriv_lt_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    forallᵐ x ∂(η a), rnDeriv κ η a x < ∞ := by
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_ne_top _]
    with x heq htop using heq ▸ htop.lt_top

/--
lemma `rnDeriv_ne_top` / 引理 `rnDeriv_ne_top`

English:
lemma rnDeriv_ne_top
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α}
  proof: by
  filter_upwards [κ.rnDeriv_lt_top η] with a h using h.ne

中文:
引理 rnDeriv_ne_top
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η] {a : α}
  证明: by
  filter_upwards [κ.rnDeriv_lt_top η] with a h using h.ne

Depends on / 依赖: filter_upwards, h.ne, rnDeriv_lt_top
-/
lemma rnDeriv_ne_top (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} :
    forallᵐ x ∂(η a), rnDeriv κ η a x != ∞ := by
  filter_upwards [κ.rnDeriv_lt_top η] with a h using h.ne

/--
lemma `rnDeriv_pos` / 引理 `rnDeriv_pos`

English:
lemma rnDeriv_pos
  given: [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a)
  proof: by
  filter_upwards [ha.ae_le κ.rnDeriv_eq_rnDeriv_measure, Measure.rnDeriv_pos ha]
    with x heq hpos using heq ▸ hpos

中文:
引理 rnDeriv_pos
  条件: [是FiniteKernel κ] [是FiniteKernel η] {a : α} (ha : κ a ≪ η a)
  证明: by
  filter_upwards [ha.ae_le κ.rnDeriv_eq_rnDeriv_measure, Measure.rnDeriv_pos ha]
    with x heq hpos using heq ▸ hpos

Depends on / 依赖: Measure, Measure.rnDeriv_pos, ae_le, filter_upwards, ha.ae_le, rnDeriv_eq_rnDeriv_measure, rnDeriv_pos
-/
lemma rnDeriv_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (ha : κ a ≪ η a) :
    forallᵐ x ∂(κ a), 0 < rnDeriv κ η a x := by
  filter_upwards [ha.ae_le κ.rnDeriv_eq_rnDeriv_measure, Measure.rnDeriv_pos ha]
    with x heq hpos using heq ▸ hpos

/--
lemma `rnDeriv_toReal_pos` / 引理 `rnDeriv_toReal_pos`

English:
lemma rnDeriv_toReal_pos
  given: [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a)
  proof: by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true]

中文:
引理 rnDeriv_to实数_pos
  条件: [是FiniteKernel κ] [是FiniteKernel η] {a : α} (h : κ a ≪ η a)
  证明: by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, ae_le, filter_upwards, h.ae_le, ne_eq, not_false_eq_true, pos_iff_ne_zero, rnDeriv_ne_top, rnDeriv_pos, toReal_pos
-/
lemma rnDeriv_toReal_pos [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    forallᵐ x ∂(κ a), 0 < (rnDeriv κ η a x).toReal := by
  filter_upwards [rnDeriv_pos h, h.ae_le (rnDeriv_ne_top κ _)] with x h0 htop
  simp_all only [pos_iff_ne_zero, ne_eq, ENNReal.toReal_pos, not_false_eq_true]

/--
lemma `rnDeriv_add` / 引理 `rnDeriv_add`

English:
lemma rnDeriv_add
  statement: (κ ν η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
  proof: by
  filter_upwards [(κ + ν).rnDeriv_eq_rnDeriv_measure, κ.rnDeriv_eq_rnDeriv_measure,
    ν.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_add (ν a) (η a)] with x h1 h2 h3 h4
  simp [h1, h2, h3, h4]

中文:
引理 rnDeriv_add
  结论: (κ ν η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel ν] [是FiniteKernel η]
  证明: by
  filter_upwards [(κ + ν).rnDeriv_eq_rnDeriv_measure, κ.rnDeriv_eq_rnDeriv_measure,
    ν.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_add (ν a) (η a)] with x h1 h2 h3 h4
  simp [h1, h2, h3, h4]

Depends on / 依赖: filter_upwards, rnDeriv_add, rnDeriv_eq_rnDeriv_measure
-/
lemma rnDeriv_add (κ ν η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
    (a : α) :
    rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν η a := by
  filter_upwards [(κ + ν).rnDeriv_eq_rnDeriv_measure, κ.rnDeriv_eq_rnDeriv_measure,
    ν.rnDeriv_eq_rnDeriv_measure, (κ a).rnDeriv_add (ν a) (η a)] with x h1 h2 h3 h4
  simp [h1, h2, h3, h4]

/--
lemma `setLIntegral_rnDeriv_le` / 引理 `setLIntegral_rnDeriv_le`

English:
lemma setLIntegral_rnDeriv_le
  statement: {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply' _ s]
  exact (κ a).withDensity_rnDeriv_le _ _

中文:
引理 setL整数egral_rnDeriv_le
  结论: {κ η : 核 α γ} [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply' _ s]
  exact (κ a).withDensity_rnDeriv_le _ _

Depends on / 依赖: rnDeriv_eq_rnDeriv_measure, setLIntegral_congr_fun_ae, withDensity_apply, withDensity_rnDeriv_le
-/
lemma setLIntegral_rnDeriv_le {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ c in s, κ.rnDeriv η a c ∂η a <= κ a s := by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply' _ s]
  exact (κ a).withDensity_rnDeriv_le _ _

/--
lemma `setLIntegral_rnDeriv` / 引理 `setLIntegral_rnDeriv`

English:
lemma setLIntegral_rnDeriv
  statement: {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply _ hs]; rw [(κ a).withDensity_rnDeriv_eq _ h]

中文:
引理 setL整数egral_rnDeriv
  结论: {κ η : 核 α γ} [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply _ hs]; rw [(κ a).withDensity_rnDeriv_eq _ h]

Depends on / 依赖: rnDeriv_eq_rnDeriv_measure, setLIntegral_congr_fun_ae, withDensity_apply, withDensity_rnDeriv_eq
-/
lemma setLIntegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} (h : κ a ≪ η a) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ c in s, κ.rnDeriv η a c ∂η a = κ a s := by
  rw [setLIntegral_congr_fun_ae hs ((κ.rnDeriv_eq_rnDeriv_measure).mono (fun x hx _ => hx))]; rw [← withDensity_apply _ hs]; rw [(κ a).withDensity_rnDeriv_eq _ h]

/--
lemma `lintegral_rnDeriv` / 引理 `lintegral_rnDeriv`

English:
lemma lintegral_rnDeriv
  statement: {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
  proof: by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv h MeasurableSet.univ]

中文:
引理 lintegral_rnDeriv
  结论: {κ η : 核 α γ} [是FiniteKernel κ] [是FiniteKernel η]
  证明: by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv h MeasurableSet.univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, setLIntegral_rnDeriv, setLIntegral_univ
-/
lemma lintegral_rnDeriv {κ η : Kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η]
    {a : α} (h : κ a ≪ η a) :
    ∫⁻ c, κ.rnDeriv η a c ∂η a = κ a univ := by
  rw [← setLIntegral_univ]; rw [setLIntegral_rnDeriv h MeasurableSet.univ]

/--
lemma `withDensity_rnDeriv_le` / 引理 `withDensity_rnDeriv_le`

English:
lemma withDensity_rnDeriv_le
  given: (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α)
  proof: by
  refine Measure.le_intro (fun s hs _ => ?_)
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_rnDeriv_le hs
  · exact κ.measurable_rnDeriv _

中文:
引理 withDensity_rnDeriv_le
  条件: (κ η : 核 α γ) [是FiniteKernel κ] [是FiniteKernel η] (a : α)
  证明: by
  refine Measure.le_intro (fun s hs _ => ?_)
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_rnDeriv_le hs
  · exact κ.measurable_rnDeriv _

Depends on / 依赖: Kernel, Kernel.withDensity_apply, Measure, Measure.le_intro, le_intro, measurable_rnDeriv, setLIntegral_rnDeriv_le, withDensity_apply
-/
lemma withDensity_rnDeriv_le (κ η : Kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    η.withDensity (κ.rnDeriv η) a <= κ a := by
  refine Measure.le_intro (fun s hs _ => ?_)
  rw [Kernel.withDensity_apply']
  · exact setLIntegral_rnDeriv_le hs
  · exact κ.measurable_rnDeriv _

/--
lemma `withDensity_rnDeriv_eq` / 引理 `withDensity_rnDeriv_eq`

English:
lemma withDensity_rnDeriv_eq
  given: [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a)
  proof: by
  rw [Kernel.withDensity_apply]
  swap; · exact κ.measurable_rnDeriv _
  have h_ae := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [MeasureTheory.withDensity_congr_ae h_ae]; rw [(κ a).withDensity_rnDeriv_eq _ h]

中文:
引理 withDensity_rnDeriv_eq
  条件: [是FiniteKernel κ] [是FiniteKernel η] {a : α} (h : κ a ≪ η a)
  证明: by
  rw [Kernel.withDensity_apply]
  swap; · exact κ.measurable_rnDeriv _
  have h_ae := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [MeasureTheory.withDensity_congr_ae h_ae]; rw [(κ a).withDensity_rnDeriv_eq _ h]

Depends on / 依赖: Kernel, Kernel.withDensity_apply, MeasureTheory, MeasureTheory.withDensity_congr_ae, h_ae, measurable_rnDeriv, rnDeriv_eq_rnDeriv_measure, withDensity_apply, withDensity_congr_ae, withDensity_rnDeriv_eq
-/
lemma withDensity_rnDeriv_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} (h : κ a ≪ η a) :
    η.withDensity (κ.rnDeriv η) a = κ a := by
  rw [Kernel.withDensity_apply]
  swap; · exact κ.measurable_rnDeriv _
  have h_ae := κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a)
  rw [MeasureTheory.withDensity_congr_ae h_ae]; rw [(κ a).withDensity_rnDeriv_eq _ h]

/--
lemma `rnDeriv_withDensity` / 引理 `rnDeriv_withDensity`

English:
lemma rnDeriv_withDensity
  statement: [IsFiniteKernel κ] {f : α -> γ -> Real>=0∞} [IsFiniteKernel (withDensity κ f)]
  proof: by
  have h_ae := (κ.withDensity f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := a)
  have hf' : forall a, Measurable (f a) := fun _ => hf.of_uncurry_left
  filter_upwards [h_ae, (κ a).rnDeriv_withDensity (hf' a)] with x hx1 hx2
  rw [hx1]; rw [κ.withDensity_apply hf]; rw [hx2]

中文:
引理 rnDeriv_withDensity
  结论: [是FiniteKernel κ] {f : α -> γ -> 实数>=0∞} [是FiniteKernel (withDensity κ f)]
  证明: by
  have h_ae := (κ.withDensity f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := a)
  have hf' : forall a, Measurable (f a) := fun _ => hf.of_uncurry_left
  filter_upwards [h_ae, (κ a).rnDeriv_withDensity (hf' a)] with x hx1 hx2
  rw [hx1]; rw [κ.withDensity_apply hf]; rw [hx2]

Depends on / 依赖: Measurable, filter_upwards, h_ae, hf.of_uncurry_left, of_uncurry_left, rnDeriv_eq_rnDeriv_measure, rnDeriv_withDensity, withDensity, withDensity_apply
-/
lemma rnDeriv_withDensity [IsFiniteKernel κ] {f : α -> γ -> Real>=0∞} [IsFiniteKernel (withDensity κ f)]
    (hf : Measurable (Function.uncurry f)) (a : α) :
    (κ.withDensity f).rnDeriv κ a =ᵐ[κ a] f a := by
  have h_ae := (κ.withDensity f).rnDeriv_eq_rnDeriv_measure (η := κ) (a := a)
  have hf' : forall a, Measurable (f a) := fun _ => hf.of_uncurry_left
  filter_upwards [h_ae, (κ a).rnDeriv_withDensity (hf' a)] with x hx1 hx2
  rw [hx1]; rw [κ.withDensity_apply hf]; rw [hx2]

/--
lemma `rnDeriv_eq_one_iff_eq` / 引理 `rnDeriv_eq_one_iff_eq`

English:
lemma rnDeriv_eq_one_iff_eq
  statement: [IsFiniteKernel κ] [IsFiniteKernel η] {a : α}
  proof: by
  rw [← Measure.rnDeriv_eq_one_iff_eq h_ac]
  refine eventually_congr ?_
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with c hc
  rw [hc]; rw [Pi.one_apply]

中文:
引理 rnDeriv_eq_one_iff_eq
  结论: [是FiniteKernel κ] [是FiniteKernel η] {a : α}
  证明: by
  rw [← Measure.rnDeriv_eq_one_iff_eq h_ac]
  refine eventually_congr ?_
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with c hc
  rw [hc]; rw [Pi.one_apply]

Depends on / 依赖: Measure, Measure.rnDeriv_eq_one_iff_eq, Pi.one_apply, eventually_congr, filter_upwards, h_ac, one_apply, rnDeriv_eq_one_iff_eq, rnDeriv_eq_rnDeriv_measure
-/
lemma rnDeriv_eq_one_iff_eq [IsFiniteKernel κ] [IsFiniteKernel η] {a : α}
    (h_ac : κ a ≪ η a) :
    (forallᵐ b ∂(η a), κ.rnDeriv η a b = 1) ↔ κ a = η a := by
  rw [← Measure.rnDeriv_eq_one_iff_eq h_ac]
  refine eventually_congr ?_
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with c hc
  rw [hc]; rw [Pi.one_apply]

end ProbabilityTheory.Kernel
