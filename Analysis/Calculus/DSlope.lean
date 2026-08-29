/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

@[expose] public section

open scoped Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open scoped Classical in
/--
Definition of `dslope` / `dslope` 的定义

English:
definition dslope
  signature: (f : 𝕜 -> E) (a : 𝕜)
  body: update (slope f a) a (deriv f a)

@[simp]

中文:
定义 dslope
  签名: (f : 𝕜 -> E) (a : 𝕜)
  定义体: update (slope f a) a (deriv f a)

@[simp]

Depends on / 依赖: update
-/
noncomputable def dslope (f : 𝕜 -> E) (a : 𝕜) : 𝕜 -> E :=
  update (slope f a) a (deriv f a)

@[simp]
/--
theorem `dslope_same` / 定理 `dslope_same`

English:
theorem dslope_same
  given: (f : 𝕜 -> E) (a : 𝕜)
  statement: dslope f a a = deriv f a
  proof: by
  classical
  exact update_self ..

中文:
定理 dslope_same
  条件: (f : 𝕜 -> E) (a : 𝕜)
  结论: dslope f a a = deriv f a
  证明: by
  classical
  exact update_self ..

Depends on / 依赖: classical, update_self
-/
theorem dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a := by
  classical
  exact update_self ..

variable {f : 𝕜 -> E} {a b : 𝕜} {s : Set 𝕜}

/--
theorem `dslope_of_ne` / 定理 `dslope_of_ne`

English:
theorem dslope_of_ne
  given: (f : 𝕜 -> E) (h : b != a)
  statement: dslope f a b = slope f a b
  proof: by
  classical
  exact update_of_ne h ..

中文:
定理 dslope_of_ne
  条件: (f : 𝕜 -> E) (h : b != a)
  结论: dslope f a b = slope f a b
  证明: by
  classical
  exact update_of_ne h ..

Depends on / 依赖: classical, update_of_ne
-/
theorem dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = slope f a b := by
  classical
  exact update_of_ne h ..

/--
theorem `ContinuousLinearMap.dslope_comp` / 定理 `ContinuousLinearMap.dslope_comp`

English:
theorem ContinuousLinearMap.dslope_comp
  statement: {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  proof: by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using! f.toLinearMap.slope_comp g a b

中文:
定理 ContinuousLinearMap.dslope_comp
  结论: {F : 类型} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  证明: by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using! f.toLinearMap.slope_comp g a b

Depends on / 依赖: comp_hasDerivAt, dslope_of_ne, dslope_same, eq_or_ne, f.hasFDerivAt.comp_hasDerivAt, f.toLinearMap.slope_comp, hasDerivAt, hasFDerivAt, slope_comp, toLinearMap
-/
theorem ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E ->L[𝕜] F) (g : 𝕜 -> E) (a b : 𝕜) (H : a = b -> DifferentiableAt 𝕜 g a) :
    dslope (f ∘ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using! f.toLinearMap.slope_comp g a b

/--
theorem `eqOn_dslope_slope` / 定理 `eqOn_dslope_slope`

English:
theorem eqOn_dslope_slope
  given: (f : 𝕜 -> E) (a : 𝕜)
  statement: EqOn (dslope f a) (slope f a) {a}ᶜ
  proof: fun _ =>
  dslope_of_ne f

中文:
定理 eqOn_dslope_slope
  条件: (f : 𝕜 -> E) (a : 𝕜)
  结论: EqOn (dslope f a) (slope f a) {a}ᶜ
  证明: fun _ =>
  dslope_of_ne f
-/
theorem eqOn_dslope_slope (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope f a) (slope f a) {a}ᶜ := fun _ =>
  dslope_of_ne f

/--
theorem `dslope_eventuallyEq_slope_of_ne` / 定理 `dslope_eventuallyEq_slope_of_ne`

English:
theorem dslope_eventuallyEq_slope_of_ne
  given: (f : 𝕜 -> E) (h : b != a)
  statement: dslope f a =ᶠ[𝓝 b] slope f a
  proof: (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)

中文:
定理 dslope_eventuallyEq_slope_of_ne
  条件: (f : 𝕜 -> E) (h : b != a)
  结论: dslope f a =ᶠ[𝓝 b] slope f a
  证明: (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)

Depends on / 依赖: eqOn_dslope_slope, eventuallyEq_of_mem, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds
-/
theorem dslope_eventuallyEq_slope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a =ᶠ[𝓝 b] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)

/--
theorem `dslope_eventuallyEq_slope_nhdsNE` / 定理 `dslope_eventuallyEq_slope_nhdsNE`

English:
theorem dslope_eventuallyEq_slope_nhdsNE
  given: (f : 𝕜 -> E)
  statement: dslope f a =ᶠ[𝓝[!=] a] slope f a
  proof: (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin

@[simp]

中文:
定理 dslope_eventuallyEq_slope_nhdsNE
  条件: (f : 𝕜 -> E)
  结论: dslope f a =ᶠ[𝓝[!=] a] slope f a
  证明: (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin

@[simp]

Depends on / 依赖: eqOn_dslope_slope, eventuallyEq_of_mem, self_mem_nhdsWithin
-/
theorem dslope_eventuallyEq_slope_nhdsNE (f : 𝕜 -> E) : dslope f a =ᶠ[𝓝[!=] a] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin

@[simp]
/--
theorem `sub_smul_dslope` / 定理 `sub_smul_dslope`

English:
theorem sub_smul_dslope
  given: (f : 𝕜 -> E) (a b : 𝕜)
  statement: (b - a) • dslope f a b = f b - f a
  proof: by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]

中文:
定理 sub_smul_dslope
  条件: (f : 𝕜 -> E) (a b : 𝕜)
  结论: (b - a) • dslope f a b = f b - f a
  证明: by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]

Depends on / 依赖: dslope_of_ne, eq_or_ne
-/
theorem sub_smul_dslope (f : 𝕜 -> E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]

/--
theorem `dslope_sub_smul_of_ne` / 定理 `dslope_sub_smul_of_ne`

English:
theorem dslope_sub_smul_of_ne
  given: (f : 𝕜 -> E) (h : b != a)
  proof: by
  rw [dslope_of_ne _ h]; rw [slope_sub_smul _ h.symm]

中文:
定理 dslope_sub_smul_of_ne
  条件: (f : 𝕜 -> E) (h : b != a)
  证明: by
  rw [dslope_of_ne _ h]; rw [slope_sub_smul _ h.symm]

Depends on / 依赖: dslope_of_ne, h.symm, slope_sub_smul
-/
theorem dslope_sub_smul_of_ne (f : 𝕜 -> E) (h : b != a) :
    dslope (fun x => (x - a) • f x) a b = f b := by
  rw [dslope_of_ne _ h]; rw [slope_sub_smul _ h.symm]

/--
theorem `eqOn_dslope_sub_smul` / 定理 `eqOn_dslope_sub_smul`

English:
theorem eqOn_dslope_sub_smul
  given: (f : 𝕜 -> E) (a : 𝕜)
  proof: fun _ => dslope_sub_smul_of_ne f

中文:
定理 eqOn_dslope_sub_smul
  条件: (f : 𝕜 -> E) (a : 𝕜)
  证明: fun _ => dslope_sub_smul_of_ne f

Depends on / 依赖: dslope_sub_smul_of_ne
-/
theorem eqOn_dslope_sub_smul (f : 𝕜 -> E) (a : 𝕜) :
    EqOn (dslope (fun x => (x - a) • f x) a) f {a}ᶜ := fun _ => dslope_sub_smul_of_ne f

/--
theorem `dslope_sub_smul` / 定理 `dslope_sub_smul`

English:
theorem dslope_sub_smul
  given: [DecidableEq 𝕜] (f : 𝕜 -> E) (a : 𝕜)
  proof: eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]

中文:
定理 dslope_sub_smul
  条件: [DecidableEq 𝕜] (f : 𝕜 -> E) (a : 𝕜)
  证明: eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]

Depends on / 依赖: dslope_same, eqOn_dslope_sub_smul, eq_update_iff
-/
theorem dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 -> E) (a : 𝕜) :
    dslope (fun x => (x - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a) :=
  eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]
/--
theorem `continuousAt_dslope_same` / 定理 `continuousAt_dslope_same`

English:
theorem continuousAt_dslope_same
  statement: ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a
  proof: by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]

中文:
定理 continuousAt_dslope_same
  结论: ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a
  证明: by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]

Depends on / 依赖: continuousAt_update_same, dslope, hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope
-/
theorem continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a := by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]

/--
theorem `ContinuousWithinAt.of_dslope` / 定理 `ContinuousWithinAt.of_dslope`

English:
theorem ContinuousWithinAt.of_dslope
  given: (h : ContinuousWithinAt (dslope f a) s b)
  proof: by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this

中文:
定理 ContinuousWithinAt.of_dslope
  条件: (h : ContinuousWithinAt (dslope f a) s b)
  证明: by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this

Depends on / 依赖: ContinuousWithinAt, continuousWithinAt_const, continuousWithinAt_id, continuousWithinAt_id.sub, dslope, sub_add_cancel, sub_smul_dslope
-/
theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) :
    ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this

/--
theorem `ContinuousAt.of_dslope` / 定理 `ContinuousAt.of_dslope`

English:
theorem ContinuousAt.of_dslope
  given: (h : ContinuousAt (dslope f a) b)
  statement: ContinuousAt f b
  proof: (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope

中文:
定理 ContinuousAt.of_dslope
  条件: (h : ContinuousAt (dslope f a) b)
  结论: ContinuousAt f b
  证明: (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope

Depends on / 依赖: continuousWithinAt, continuousWithinAt_univ, h.continuousWithinAt.of_dslope, of_dslope
-/
theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope

/--
theorem `ContinuousOn.of_dslope` / 定理 `ContinuousOn.of_dslope`

English:
theorem ContinuousOn.of_dslope
  given: (h : ContinuousOn (dslope f a) s)
  statement: ContinuousOn f s
  proof: fun x hx =>
  (h x hx).of_dslope

中文:
定理 ContinuousOn.of_dslope
  条件: (h : ContinuousOn (dslope f a) s)
  结论: ContinuousOn f s
  证明: fun x hx =>
  (h x hx).of_dslope
-/
theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx =>
  (h x hx).of_dslope

/--
theorem `continuousWithinAt_dslope_of_ne` / 定理 `continuousWithinAt_dslope_of_ne`

English:
theorem continuousWithinAt_dslope_of_ne
  given: (h : b != a)
  proof: by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  classical
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)

中文:
定理 continuousWithinAt_dslope_of_ne
  条件: (h : b != a)
  证明: by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  classical
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.of_dslope, classical, continuousWithinAt_const, continuousWithinAt_id, continuousWithinAt_id.sub, continuousWithinAt_update_of_ne, dslope, hc.sub, of_dslope, sub_ne_zero
-/
theorem continuousWithinAt_dslope_of_ne (h : b != a) :
    ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b := by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  classical
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)

/--
theorem `continuousAt_dslope_of_ne` / 定理 `continuousAt_dslope_of_ne`

English:
theorem continuousAt_dslope_of_ne
  given: (h : b != a)
  statement: ContinuousAt (dslope f a) b ↔ ContinuousAt f b
  proof: by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]

中文:
定理 continuousAt_dslope_of_ne
  条件: (h : b != a)
  结论: ContinuousAt (dslope f a) b ↔ ContinuousAt f b
  证明: by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]

Depends on / 依赖: continuousWithinAt_dslope_of_ne, continuousWithinAt_univ
-/
theorem continuousAt_dslope_of_ne (h : b != a) : ContinuousAt (dslope f a) b ↔ ContinuousAt f b := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]

/--
theorem `continuousOn_dslope` / 定理 `continuousOn_dslope`

English:
theorem continuousOn_dslope
  given: (h : s in 𝓝 a)
  proof: by
refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]

中文:
定理 continuousOn_dslope
  条件: (h : s in 𝓝 a)
  证明: by
refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]

Depends on / 依赖: continuousAt, continuousAt_dslope_same, continuousWithinAt, continuousWithinAt_dslope_of_ne, eq_or_ne, exacts, hc.continuousAt, hc.of_dslope, of_dslope
-/
theorem continuousOn_dslope (h : s in 𝓝 a) :
    ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a := by
refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]

/--
theorem `DifferentiableWithinAt.of_dslope` / 定理 `DifferentiableWithinAt.of_dslope`

English:
theorem DifferentiableWithinAt.of_dslope
  given: (h : DifferentiableWithinAt 𝕜 (dslope f a) s b)
  proof: by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)

中文:
定理 DifferentiableWithinAt.of_dslope
  条件: (h : DifferentiableWithinAt 𝕜 (dslope f a) s b)
  证明: by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)

Depends on / 依赖: add_const, differentiableWithinAt_id, differentiableWithinAt_id.sub_const, fun_smul, sub_add_cancel, sub_const, sub_smul_dslope
-/
theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a) s b) :
    DifferentiableWithinAt 𝕜 f s b := by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)

/--
theorem `DifferentiableAt.of_dslope` / 定理 `DifferentiableAt.of_dslope`

English:
theorem DifferentiableAt.of_dslope
  given: (h : DifferentiableAt 𝕜 (dslope f a) b)
  proof: differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope

中文:
定理 DifferentiableAt.of_dslope
  条件: (h : DifferentiableAt 𝕜 (dslope f a) b)
  证明: differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_univ, h.differentiableWithinAt.of_dslope, of_dslope
-/
theorem DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) :
    DifferentiableAt 𝕜 f b :=
  differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope

/--
theorem `DifferentiableOn.of_dslope` / 定理 `DifferentiableOn.of_dslope`

English:
theorem DifferentiableOn.of_dslope
  given: (h : DifferentiableOn 𝕜 (dslope f a) s)
  proof: fun x hx => (h x hx).of_dslope

中文:
定理 DifferentiableOn.of_dslope
  条件: (h : DifferentiableOn 𝕜 (dslope f a) s)
  证明: fun x hx => (h x hx).of_dslope

Depends on / 依赖: of_dslope
-/
theorem DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).of_dslope

/--
theorem `differentiableWithinAt_dslope_of_ne` / 定理 `differentiableWithinAt_dslope_of_ne`

English:
theorem differentiableWithinAt_dslope_of_ne
  given: (h : b != a)
  proof: by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds

中文:
定理 differentiableWithinAt_dslope_of_ne
  条件: (h : b != a)
  证明: by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.of_dslope, congr_of_eventuallyEq, differentiableWithinAt_id, differentiableWithinAt_id.sub_const, dslope_of_ne, eqOn_dslope_slope, eventuallyEq_of_mem, hd.sub_const, isOpen_ne, isOpen_ne.mem_nhds, mem_nhds, mem_nhdsWithin_of_mem_nhds, of_dslope, sub_const, sub_ne_zero
-/
theorem differentiableWithinAt_dslope_of_ne (h : b != a) :
    DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b := by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

/--
theorem `differentiableOn_dslope_of_notMem` / 定理 `differentiableOn_dslope_of_notMem`

English:
theorem differentiableOn_dslope_of_notMem
  given: (h : a ∉ s)
  proof: forall_congr' fun _ =>
forall_congr' fun hx => differentiableWithinAt_dslope_of_ne ne_of_mem_of_not_mem hx h

中文:
定理 differentiableOn_dslope_of_notMem
  条件: (h : a ∉ s)
  证明: forall_congr' fun _ =>
forall_congr' fun hx => differentiableWithinAt_dslope_of_ne ne_of_mem_of_not_mem hx h

Depends on / 依赖: differentiableWithinAt_dslope_of_ne, forall_congr, ne_of_mem_of_not_mem
-/
theorem differentiableOn_dslope_of_notMem (h : a ∉ s) :
    DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s :=
  forall_congr' fun _ =>
forall_congr' fun hx => differentiableWithinAt_dslope_of_ne ne_of_mem_of_not_mem hx h

/--
theorem `differentiableAt_dslope_of_ne` / 定理 `differentiableAt_dslope_of_ne`

English:
theorem differentiableAt_dslope_of_ne
  given: (h : b != a)
  proof: by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]

中文:
定理 differentiableAt_dslope_of_ne
  条件: (h : b != a)
  证明: by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]

Depends on / 依赖: differentiableWithinAt_dslope_of_ne, differentiableWithinAt_univ
-/
theorem differentiableAt_dslope_of_ne (h : b != a) :
    DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]

/--
lemma `sub_smul_dslope_of_zero` / 引理 `sub_smul_dslope_of_zero`

English:
lemma sub_smul_dslope_of_zero
  given: {f : 𝕜 -> E} {a : 𝕜} (hf : f a = 0) (b : 𝕜)
  proof: by
  simp [hf]

中文:
引理 sub_smul_dslope_of_zero
  条件: {f : 𝕜 -> E} {a : 𝕜} (hf : f a = 0) (b : 𝕜)
  证明: by
  simp [hf]
-/
lemma sub_smul_dslope_of_zero {f : 𝕜 -> E} {a : 𝕜} (hf : f a = 0) (b : 𝕜) :
    (b - a) • dslope f a b = f b := by
  simp [hf]

/--
lemma `pow_sub_smul_iterate_dslope_of_zero` / 引理 `pow_sub_smul_iterate_dslope_of_zero`

English:
lemma pow_sub_smul_iterate_dslope_of_zero
  statement: {f : 𝕜 -> E} {a : 𝕜} (n : Nat)
  proof: by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [pow_succ]; rw [mul_smul]; rw [sub_smul_dslope_of_zero (hf n n.lt_succ_self)]; rw [ih (by grind)]

中文:
引理 pow_sub_smul_iterate_dslope_of_zero
  结论: {f : 𝕜 -> E} {a : 𝕜} (n : 自然数)
  证明: by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [pow_succ]; rw [mul_smul]; rw [sub_smul_dslope_of_zero (hf n n.lt_succ_self)]; rw [ih (by grind)]

Depends on / 依赖: Function, Function.iterate_succ_apply, generalizing, iterate_succ_apply, lt_succ_self, mul_smul, n.lt_succ_self, pow_succ, sub_smul_dslope_of_zero
-/
lemma pow_sub_smul_iterate_dslope_of_zero {f : 𝕜 -> E} {a : 𝕜} (n : Nat)
    (hf : forall k < n, (Function.swap dslope a)^[k] f a = 0) (b : 𝕜) :
    (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; rw [pow_succ]; rw [mul_smul]; rw [sub_smul_dslope_of_zero (hf n n.lt_succ_self)]; rw [ih (by grind)]
