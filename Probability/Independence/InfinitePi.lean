/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Independence of an infinite family of random variables

In this file we provide several results about independence of arbitrary families of random
variables, relying on `Measure.infinitePi`.

## Implementation note

There are several possible measurability assumptions:
* The map `ω ↦ (Xᵢ(ω))ᵢ` is measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is measurable.
* The map `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is almost everywhere measurable.

Although the first two options are equivalent, the last two are not if the index set is not
countable.
-/

public section

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓧 : ι -> Type*} {m𝓧 : forall i, MeasurableSpace (𝓧 i)} {X : Π i, Ω -> 𝓧 i}

/--
lemma `iIndepFun.map_fun_eq_infinitePi_map₀` / 引理 `iIndepFun.map_fun_eq_infinitePi_map₀`

English:
lemma iIndepFun.map_fun_eq_infinitePi_map₀
  statement: (mX : AEMeasurable (fun ω i => X i ω) P)
  proof: by
  have := h.isProbabilityMeasure
  have _ i := isProbabilityMeasure_map (mX.eval i)
  refine eq_infinitePi _ fun s t ht => ?_
  rw [iIndepFun_iff_finset] at h
  have : (s : Set ι).pi t = s.restrict ⁻¹' (Set.univ.pi fun i => t i) := by ext; simp
  rw [this]; rw [← map_apply]; rw [AEMeasurable.map_map_of_aemeasurable]
  · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
    rw [this]; rw [(h s).map_fun_eq_pi_map]; rw [pi_pi]
    · simp only [Finset.restrict]
      rw [s.prod_coe_sort fun i => P.map (X i) (t i)]
    exact fun i => mX.eval i
  any_goals fun_prop
  · exact mX
  · exact .univ_pi fun i => ht i

中文:
引理 iIndepFun.map_fun_eq_infinitePi_map₀
  结论: (mX : 几乎处处可测 (fun ω i => X i ω) P)
  证明: by
  have := h.isProbabilityMeasure
  have _ i := isProbabilityMeasure_map (mX.eval i)
  refine eq_infinitePi _ fun s t ht => ?_
  rw [iIndepFun_iff_finset] at h
  have : (s : Set ι).pi t = s.restrict ⁻¹' (Set.univ.pi fun i => t i) := by ext; simp
  rw [this]; rw [← map_apply]; rw [AEMeasurable.map_map_of_aemeasurable]
  · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
    rw [this]; rw [(h s).map_fun_eq_pi_map]; rw [pi_pi]
    · simp only [Finset.restrict]
      rw [s.prod_coe_sort fun i => P.map (X i) (t i)]
    exact fun i => mX.eval i
  any_goals fun_prop
  · exact mX
  · exact .univ_pi fun i => ht i

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Finset, Finset.restrict, Set.univ.pi, eq_infinitePi, h.isProbabilityMeasure, iIndepFun_iff_finset, isProbabilityMeasure, isProbabilityMeasure_map, mX.eval, map_apply, map_fun_eq_pi_map, map_map_of_aemeasurable, pi_pi, prod_coe_sort, restrict, s.prod_coe_sort, s.restrict
-/
lemma iIndepFun.map_fun_eq_infinitePi_map₀ (mX : AEMeasurable (fun ω i => X i ω) P)
    (h : iIndepFun X P) :
    P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) := by
  have := h.isProbabilityMeasure
  have _ i := isProbabilityMeasure_map (mX.eval i)
  refine eq_infinitePi _ fun s t ht => ?_
  rw [iIndepFun_iff_finset] at h
  have : (s : Set ι).pi t = s.restrict ⁻¹' (Set.univ.pi fun i => t i) := by ext; simp
  rw [this]; rw [← map_apply]; rw [AEMeasurable.map_map_of_aemeasurable]
  · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
    rw [this]; rw [(h s).map_fun_eq_pi_map]; rw [pi_pi]
    · simp only [Finset.restrict]
      rw [s.prod_coe_sort fun i => P.map (X i) (t i)]
    exact fun i => mX.eval i
  any_goals fun_prop
  · exact mX
  · exact .univ_pi fun i => ht i

/--
lemma `iIndepFun_iff_map_fun_eq_infinitePi_map₀` / 引理 `iIndepFun_iff_map_fun_eq_infinitePi_map₀`

English:
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀
  statement: [IsProbabilityMeasure P]
  proof: h.map_fun_eq_infinitePi_map₀ mX
  mpr h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
      rw [← this]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [h]; rw [infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i => mX.eval i

中文:
引理 iIndepFun_iff_map_fun_eq_infinitePi_map₀
  结论: [是概率测度 P]
  证明: h.map_fun_eq_infinitePi_map₀ mX
  mpr h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
      rw [← this]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [h]; rw [infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i => mX.eval i

Depends on / 依赖: h.map_fun_eq_infinitePi_map
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ [IsProbabilityMeasure P]
    (mX : AEMeasurable (fun ω i => X i ω) P) :
    iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) where
  mp h := h.map_fun_eq_infinitePi_map₀ mX
  mpr h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i => X i ω) = fun ω i => s.restrict X i ω := by ext; simp
      rw [← this]; rw [← AEMeasurable.map_map_of_aemeasurable]; rw [h]; rw [infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i => mX.eval i

/--
lemma `iIndepFun.map_fun_eq_infinitePi_map₀'` / 引理 `iIndepFun.map_fun_eq_infinitePi_map₀'`

English:
lemma iIndepFun.map_fun_eq_infinitePi_map₀'
  statement: [Countable ι] (mX : forall i, AEMeasurable (X i) P)
  proof: h.map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

中文:
引理 iIndepFun.map_fun_eq_infinitePi_map₀'
  结论: [可数 ι] (mX : 对任意 i, 几乎处处可测 (X i) P)
  证明: h.map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

Depends on / 依赖: aemeasurable_pi_iff, h.map_fun_eq_infinitePi_map
-/
lemma iIndepFun.map_fun_eq_infinitePi_map₀' [Countable ι] (mX : forall i, AEMeasurable (X i) P)
    (h : iIndepFun X P) :
    P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) :=
h.map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

/--
lemma `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` / 引理 `iIndepFun_iff_map_fun_eq_infinitePi_map₀'`

English:
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀'
  statement: [IsProbabilityMeasure P] [Countable ι]
  proof: iIndepFun_iff_map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

中文:
引理 iIndepFun_iff_map_fun_eq_infinitePi_map₀'
  结论: [是概率测度 P] [可数 ι]
  证明: iIndepFun_iff_map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

Depends on / 依赖: aemeasurable_pi_iff
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀' [IsProbabilityMeasure P] [Countable ι]
    (mX : forall i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) :=
iIndepFun_iff_map_fun_eq_infinitePi_map₀ aemeasurable_pi_iff.2 mX

/--
lemma `iIndepFun.map_fun_eq_infinitePi_map` / 引理 `iIndepFun.map_fun_eq_infinitePi_map`

English:
lemma iIndepFun.map_fun_eq_infinitePi_map
  given: (mX : forall i, Measurable (X i)) (h : iIndepFun X P)
  proof: h.map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

中文:
引理 iIndepFun.map_fun_eq_infinitePi_map
  条件: (mX : 对任意 i, 可测 (X i)) (h : iIndepFun X P)
  证明: h.map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

Depends on / 依赖: aemeasurable, h.map_fun_eq_infinitePi_map, measurable_pi_iff
-/
lemma iIndepFun.map_fun_eq_infinitePi_map (mX : forall i, Measurable (X i)) (h : iIndepFun X P) :
    P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) :=
h.map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

/--
lemma `iIndepFun_iff_map_fun_eq_infinitePi_map` / 引理 `iIndepFun_iff_map_fun_eq_infinitePi_map`

English:
lemma iIndepFun_iff_map_fun_eq_infinitePi_map
  statement: [IsProbabilityMeasure P]
  proof: iIndepFun_iff_map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

中文:
引理 iIndepFun_iff_map_fun_eq_infinitePi_map
  结论: [是概率测度 P]
  证明: iIndepFun_iff_map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

Depends on / 依赖: aemeasurable, measurable_pi_iff
-/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map [IsProbabilityMeasure P]
    (mX : forall i, Measurable (X i)) :
    iIndepFun X P ↔ P.map (fun ω i => X i ω) = infinitePi (fun i => P.map (X i)) :=
iIndepFun_iff_map_fun_eq_infinitePi_map₀ .aemeasurable measurable_pi_iff.2 mX

/--
lemma `iIndepFun.hasLaw_infinitePi` / 引理 `iIndepFun.hasLaw_infinitePi`

English:
lemma iIndepFun.hasLaw_infinitePi
  statement: {μ : (i : ι) -> Measure (𝓧 i)} (hX : forall i, HasLaw (X i) (μ i) P)
  proof: h2
  map_eq := by
    have := h1.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀ h2).1 h1]
    simp_rw [fun i => (hX i).map_eq]

中文:
引理 iIndepFun.hasLaw_infinitePi
  结论: {μ : (i : ι) -> 测度 (𝓧 i)} (hX : 对任意 i, 有Law (X i) (μ i) P)
  证明: h2
  map_eq := by
    have := h1.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀ h2).1 h1]
    simp_rw [fun i => (hX i).map_eq]
-/
lemma iIndepFun.hasLaw_infinitePi {μ : (i : ι) -> Measure (𝓧 i)} (hX : forall i, HasLaw (X i) (μ i) P)
    (h1 : iIndepFun X P) (h2 : AEMeasurable (fun ω i => X i ω) P) :
    HasLaw (fun ω i => X i ω) (infinitePi μ) P where
  aemeasurable := h2
  map_eq := by
    have := h1.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀ h2).1 h1]
    simp_rw [fun i => (hX i).map_eq]

/--
lemma `iIndepFun_iff_hasLaw_Pi_infinitePi` / 引理 `iIndepFun_iff_hasLaw_Pi_infinitePi`

English:
lemma iIndepFun_iff_hasLaw_Pi_infinitePi
  statement: [IsProbabilityMeasure P] {μ : (i : ι) -> Measure (𝓧 i)}
  proof: h.hasLaw_infinitePi hX hm
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

中文:
引理 iIndepFun_iff_hasLaw_Pi_infinitePi
  结论: [是概率测度 P] {μ : (i : ι) -> 测度 (𝓧 i)}
  证明: h.hasLaw_infinitePi hX hm
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

Depends on / 依赖: h.hasLaw_infinitePi, hasLaw_infinitePi
-/
lemma iIndepFun_iff_hasLaw_Pi_infinitePi [IsProbabilityMeasure P] {μ : (i : ι) -> Measure (𝓧 i)}
    (hX : forall i, HasLaw (X i) (μ i) P) (hm : AEMeasurable (fun ω i => X i ω) P) :
    iIndepFun X P ↔ HasLaw (fun ω i => X i ω) (infinitePi μ) P where
  mp h := h.hasLaw_infinitePi hX hm
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm]; rw [h.map_eq]
    simp_rw [fun i => (hX i).map_eq]

/--
lemma `iIndepFun_infinitePi` / 引理 `iIndepFun_infinitePi`

English:
lemma iIndepFun_infinitePi
  statement: {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i)}
  proof: by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [infinitePi_map_pi _ mX]
  congrm infinitePi fun i => ?_
  rw [← infinitePi_map_eval P i]; rw [map_map (mX i) (by fun_prop)]; rw [Function.comp_def]

中文:
引理 iIndepFun_infinitePi
  结论: {Ω : ι -> 类型} {mΩ : 对任意 i, 可测空间 (Ω i)}
  证明: by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [infinitePi_map_pi _ mX]
  congrm infinitePi fun i => ?_
  rw [← infinitePi_map_eval P i]; rw [map_map (mX i) (by fun_prop)]; rw [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, congrm, fun_prop, iIndepFun_iff_map_fun_eq_infinitePi_map, infinitePi, infinitePi_map_eval, infinitePi_map_pi, map_map
-/
lemma iIndepFun_infinitePi {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpace (Ω i)}
    {P : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (P i)] {X : (i : ι) -> Ω i -> 𝓧 i}
    (mX : forall i, Measurable (X i)) :
    iIndepFun (fun i ω => X i (ω i)) (infinitePi P) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [infinitePi_map_pi _ mX]
  congrm infinitePi fun i => ?_
  rw [← infinitePi_map_eval P i]; rw [map_map (mX i) (by fun_prop)]; rw [Function.comp_def]

/--
lemma `_root_.MeasureTheory.Measure.infinitePi_map_eval_prod` / 引理 `_root_.MeasureTheory.Measure.infinitePi_map_eval_prod`

English:
lemma _root_.MeasureTheory.Measure.infinitePi_map_eval_prod
  statement: {Ω : ι -> Type*}
  proof: by
  rw [IndepFun.map_prod_eq_prod_map_map]; rotate_right
.indepFun hij · exact iIndepFun_infinitePi (X := fun x ω => ω) (by fun_prop)
  · simp [infinitePi_map_eval]
  all_goals exact Measurable.aemeasurable (by fun_prop)

中文:
引理 _root_.测度论.测度.infinitePi_map_eval_prod
  结论: {Ω : ι -> 类型}
  证明: by
  rw [IndepFun.map_prod_eq_prod_map_map]; rotate_right
.indepFun hij · exact iIndepFun_infinitePi (X := fun x ω => ω) (by fun_prop)
  · simp [infinitePi_map_eval]
  all_goals exact Measurable.aemeasurable (by fun_prop)

Depends on / 依赖: IndepFun, IndepFun.map_prod_eq_prod_map_map, Measurable, Measurable.aemeasurable, aemeasurable, all_goals, fun_prop, iIndepFun_infinitePi, indepFun, infinitePi_map_eval, map_prod_eq_prod_map_map, rotate_right
-/
lemma _root_.MeasureTheory.Measure.infinitePi_map_eval_prod {Ω : ι -> Type*}
    {mΩ : forall i, MeasurableSpace (Ω i)} {P : forall i, Measure (Ω i)}
    [forall i, IsProbabilityMeasure (P i)] {i j : ι} (hij : i != j) :
    (infinitePi P).map (fun ω => (ω i, ω j)) = (P i).prod (P j) := by
  rw [IndepFun.map_prod_eq_prod_map_map]; rotate_right
.indepFun hij · exact iIndepFun_infinitePi (X := fun x ω => ω) (by fun_prop)
  · simp [infinitePi_map_eval]
  all_goals exact Measurable.aemeasurable (by fun_prop)

/--
lemma `_root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj` / 引理 `_root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj`

English:
lemma _root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
  statement: {α : Type*} {Ω : ι -> Type*}
  proof: by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map <| by fun_prop).mp ?_]
  · simp [infinitePi_map_eval]
exact .precomp hf iIndepFun_infinitePi (X := fun x ω => ω) by fun_prop

中文:
引理 _root_.测度论.测度.map_infinitePi_infinitePi_of_inj
  结论: {α : 类型} {Ω : ι -> 类型}
  证明: by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map <| by fun_prop).mp ?_]
  · simp [infinitePi_map_eval]
exact .precomp hf iIndepFun_infinitePi (X := fun x ω => ω) by fun_prop

Depends on / 依赖: fun_prop, iIndepFun_iff_map_fun_eq_infinitePi_map, iIndepFun_infinitePi, infinitePi_map_eval, precomp
-/
lemma _root_.MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj {α : Type*} {Ω : ι -> Type*}
    {mΩ : forall i, MeasurableSpace (Ω i)} {P : forall i, Measure (Ω i)}
    [forall i, IsProbabilityMeasure (P i)] {f : α -> ι} (hf : Function.Injective f) :
    (infinitePi P).map (fun ω i => ω (f i)) = infinitePi (fun i => P (f i)) := by
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map <| by fun_prop).mp ?_]
  · simp [infinitePi_map_eval]
exact .precomp hf iIndepFun_infinitePi (X := fun x ω => ω) by fun_prop

section curry

section dependent

variable {κ : ι -> Type*} {𝓧 : (i : ι) -> κ i -> Type*} {m𝓧 : forall i j, MeasurableSpace (𝓧 i j)}

/--
lemma `iIndepFun_uncurry` / 引理 `iIndepFun_uncurry`

English:
lemma iIndepFun_uncurry
  statement: {X : (i : ι) -> (j : κ i) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j))
  proof: by
  have := h1.isProbabilityMeasure
  have : forall i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => isProbabilityMeasure_map (mX i j).aemeasurable
  have : forall i, IsProbabilityMeasure (P.map (fun ω => (X i · ω))) :=
    fun i => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p => X p.1 p.2 ω) = fun ω i j => X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [← (MeasurableEquiv.piCurry 𝓧).map_measurableEquiv_injective.eq_iff]; rw [map_map (by fun_prop) (by fun_prop)]; rw [this]; rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h1]; rw [infinitePi_map_piCurry (fun i j => P.map (X i j))]
  congrm infinitePi fun i => ?_
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 (h2 i)]

中文:
引理 iIndepFun_uncurry
  结论: {X : (i : ι) -> (j : κ i) -> Ω -> 𝓧 i j} (mX : 对任意 i j, 可测 (X i j))
  证明: by
  have := h1.isProbabilityMeasure
  have : forall i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => isProbabilityMeasure_map (mX i j).aemeasurable
  have : forall i, IsProbabilityMeasure (P.map (fun ω => (X i · ω))) :=
    fun i => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p => X p.1 p.2 ω) = fun ω i j => X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [← (MeasurableEquiv.piCurry 𝓧).map_measurableEquiv_injective.eq_iff]; rw [map_map (by fun_prop) (by fun_prop)]; rw [this]; rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h1]; rw [infinitePi_map_piCurry (fun i j => P.map (X i j))]
  congrm infinitePi fun i => ?_
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 (h2 i)]

Depends on / 依赖: IsProbabilityMeasure, Measurable, Measurable.aemeasurable, MeasurableEquiv, MeasurableEquiv.piCurr, MeasurableEquiv.piCurry, P.map, Sigma.curry, aemeasurable, fun_prop, h1.isProbabilityMeasure, iIndepFun_iff_map_fun_eq_infinitePi_map, isProbabilityMeasure, isProbabilityMeasure_map, piCurr, piCurry
-/
lemma iIndepFun_uncurry {X : (i : ι) -> (j : κ i) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω => (X i · ω)) P) (h2 : forall i, iIndepFun (X i) P) :
    iIndepFun (fun (p : (i : ι) × (κ i)) ω => X p.1 p.2 ω) P := by
  have := h1.isProbabilityMeasure
  have : forall i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j => isProbabilityMeasure_map (mX i j).aemeasurable
  have : forall i, IsProbabilityMeasure (P.map (fun ω => (X i · ω))) :=
    fun i => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p => X p.1 p.2 ω) = fun ω i j => X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [← (MeasurableEquiv.piCurry 𝓧).map_measurableEquiv_injective.eq_iff]; rw [map_map (by fun_prop) (by fun_prop)]; rw [this]; rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h1]; rw [infinitePi_map_piCurry (fun i j => P.map (X i j))]
  congrm infinitePi fun i => ?_
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 (h2 i)]

/--
lemma `iIndepFun_uncurry_infinitePi` / 引理 `iIndepFun_uncurry_infinitePi`

English:
lemma iIndepFun_uncurry_infinitePi
  statement: {Ω : (i : ι) -> κ i -> Type*} {mΩ : forall i j, MeasurableSpace (Ω i j)}
  proof: by
  refine iIndepFun_uncurry (P := infinitePi (fun i => infinitePi (μ i)))
    (X := fun i j ω => X i j (ω i j)) (by fun_prop) ?_ fun i => ?_
  · exact iIndepFun_infinitePi (P := fun i => infinitePi (μ i))
      (X := fun i u j => X i j (u j)) (by fun_prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change map ((fun f => f i) ∘ (fun ω i j => X i j (ω i j)))
    (infinitePi fun i => infinitePi (μ i)) = _
  rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j) (μ := fun i => infinitePi (μ i))
      (f := fun i f j => X i j (f j))]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]
  · congrm infinitePi fun j => ?_
    change _ = map (((fun f => f j) ∘ (fun f => f i)) ∘ (fun ω i j => X i j (ω i j)))
      (infinitePi fun i => infinitePi (μ i))
    rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j)
        (μ := fun i => infinitePi (μ i)) (f := fun i f j => X i j (f j))]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]; rw [@infinitePi_map_eval ..]
    any_goals fun_prop
    · exact fun _ => isProbabilityMeasure_map (by fun_prop)
    · exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  any_goals fun_prop
  exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

中文:
引理 iIndepFun_uncurry_infinitePi
  结论: {Ω : (i : ι) -> κ i -> 类型} {mΩ : 对任意 i j, 可测空间 (Ω i j)}
  证明: by
  refine iIndepFun_uncurry (P := infinitePi (fun i => infinitePi (μ i)))
    (X := fun i j ω => X i j (ω i j)) (by fun_prop) ?_ fun i => ?_
  · exact iIndepFun_infinitePi (P := fun i => infinitePi (μ i))
      (X := fun i u j => X i j (u j)) (by fun_prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change map ((fun f => f i) ∘ (fun ω i j => X i j (ω i j)))
    (infinitePi fun i => infinitePi (μ i)) = _
  rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j) (μ := fun i => infinitePi (μ i))
      (f := fun i f j => X i j (f j))]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]
  · congrm infinitePi fun j => ?_
    change _ = map (((fun f => f j) ∘ (fun f => f i)) ∘ (fun ω i j => X i j (ω i j)))
      (infinitePi fun i => infinitePi (μ i))
    rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j)
        (μ := fun i => infinitePi (μ i)) (f := fun i f j => X i j (f j))]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]; rw [@infinitePi_map_eval ..]
    any_goals fun_prop
    · exact fun _ => isProbabilityMeasure_map (by fun_prop)
    · exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  any_goals fun_prop
  exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

Depends on / 依赖: fun_prop, iIndepFun_iff_map_fun_eq_infinitePi_map, iIndepFun_infinitePi, iIndepFun_uncurry, infinitePi, infinitePi_map_pi, map_map
-/
lemma iIndepFun_uncurry_infinitePi {Ω : (i : ι) -> κ i -> Type*} {mΩ : forall i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) -> (j : κ i) -> Ω i j -> 𝓧 i j}
    (μ : (i : ι) -> (j : κ i) -> Measure (Ω i j)) [forall i j, IsProbabilityMeasure (μ i j)]
    (mX : forall i j, Measurable (X i j)) :
    iIndepFun (fun (p : (i : ι) × κ i) (ω : Π i, Π j, Ω i j) => X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i => infinitePi (μ i))) := by
  refine iIndepFun_uncurry (P := infinitePi (fun i => infinitePi (μ i)))
    (X := fun i j ω => X i j (ω i j)) (by fun_prop) ?_ fun i => ?_
  · exact iIndepFun_infinitePi (P := fun i => infinitePi (μ i))
      (X := fun i u j => X i j (u j)) (by fun_prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change map ((fun f => f i) ∘ (fun ω i j => X i j (ω i j)))
    (infinitePi fun i => infinitePi (μ i)) = _
  rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j) (μ := fun i => infinitePi (μ i))
      (f := fun i f j => X i j (f j))]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]
  · congrm infinitePi fun j => ?_
    change _ = map (((fun f => f j) ∘ (fun f => f i)) ∘ (fun ω i j => X i j (ω i j)))
      (infinitePi fun i => infinitePi (μ i))
    rw [← map_map (by fun_prop) (by fun_prop)]; rw [infinitePi_map_pi (X := fun i => (j : κ i) -> Ω i j)
        (μ := fun i => infinitePi (μ i)) (f := fun i f j => X i j (f j))]; rw [← map_map (by fun_prop) (by fun_prop)]; rw [@infinitePi_map_eval ..]; rw [infinitePi_map_pi]; rw [@infinitePi_map_eval ..]
    any_goals fun_prop
    · exact fun _ => isProbabilityMeasure_map (by fun_prop)
    · exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  any_goals fun_prop
  exact fun _ => isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

end dependent

section nondependent

variable {κ : Type*} {𝓧 : ι -> κ -> Type*} {m𝓧 : forall i j, MeasurableSpace (𝓧 i j)}

/--
lemma `iIndepFun_uncurry'` / 引理 `iIndepFun_uncurry'`

English:
lemma iIndepFun_uncurry'
  statement: {X : (i : ι) -> (j : κ) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j))
  proof: (iIndepFun_uncurry mX h1 h2).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

中文:
引理 iIndepFun_uncurry'
  结论: {X : (i : ι) -> (j : κ) -> Ω -> 𝓧 i j} (mX : 对任意 i j, 可测 (X i j))
  证明: (iIndepFun_uncurry mX h1 h2).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

Depends on / 依赖: Equiv.sigmaEquivProd, iIndepFun_uncurry, of_precomp, sigmaEquivProd, surjective
-/
lemma iIndepFun_uncurry' {X : (i : ι) -> (j : κ) -> Ω -> 𝓧 i j} (mX : forall i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω => (X i · ω)) P) (h2 : forall i, iIndepFun (X i) P) :
    iIndepFun (fun (p : ι × κ) ω => X p.1 p.2 ω) P :=
  (iIndepFun_uncurry mX h1 h2).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

/--
lemma `iIndepFun_uncurry_infinitePi'` / 引理 `iIndepFun_uncurry_infinitePi'`

English:
lemma iIndepFun_uncurry_infinitePi'
  statement: {Ω : ι -> κ -> Type*} {mΩ : forall i j, MeasurableSpace (Ω i j)}
  proof: (iIndepFun_uncurry_infinitePi μ mX).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

中文:
引理 iIndepFun_uncurry_infinitePi'
  结论: {Ω : ι -> κ -> 类型} {mΩ : 对任意 i j, 可测空间 (Ω i j)}
  证明: (iIndepFun_uncurry_infinitePi μ mX).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

Depends on / 依赖: Equiv.sigmaEquivProd, iIndepFun_uncurry_infinitePi, of_precomp, sigmaEquivProd, surjective
-/
lemma iIndepFun_uncurry_infinitePi' {Ω : ι -> κ -> Type*} {mΩ : forall i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) -> (j : κ) -> Ω i j -> 𝓧 i j}
    (μ : (i : ι) -> (j : κ) -> Measure (Ω i j)) [forall i j, IsProbabilityMeasure (μ i j)]
    (mX : forall i j, Measurable (X i j)) :
    iIndepFun (fun (p : ι × κ) (ω : Π i, Π j, Ω i j) => X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i => infinitePi (μ i))) :=
  (iIndepFun_uncurry_infinitePi μ mX).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

end nondependent

end curry

end ProbabilityTheory
