/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Evaluation of power series

Power series in one indeterminate are the particular case of multivariate power series,
for the `Unit` type of indeterminates.
This file provides a simpler syntax.

Let `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : S`, and `f : MvPowerSeries σ R`,
`PowerSeries.eval₂ f φ a` is the evaluation of the power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` is topologically
nilpotent (`a ^ n` tends to 0 when `n` tends to infinity).

For consistency with the case of multivariate power series,
we define `PowerSeries.HasEval` as an abbrev to `IsTopologicallyNilpotent`.

Under `Continuous φ` and `HasEval a`,
the following lemmas furnish the properties of evaluation:

* `PowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `PowerSeries.aeval`: the evaluation map as an algebra morphism
* `PowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `PowerSeries.continuous_eval₂`: continuity of the evaluation
* `PowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

We refer to the documentation of `MvPowerSeries.eval₂` for more details.

-/

@[expose] public section
namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]
variable {φ : R ->+* S}

section

variable [TopologicalSpace R] [TopologicalSpace S]

/--
Definition of `HasEval` / `HasEval` 的定义

English:
abbreviation HasEval
  signature: (a : S)
  body: IsTopologicallyNilpotent a

中文:
缩写 HasEval
  签名: (a : S)
  定义体: IsTopologicallyNilpotent a

Depends on / 依赖: IsTopologicallyNilpotent
-/
abbrev HasEval (a : S) := IsTopologicallyNilpotent a

/--
theorem `hasEval_def` / 定理 `hasEval_def`

English:
theorem hasEval_def
  given: (a : S)
  statement: HasEval a ↔ IsTopologicallyNilpotent a
  proof: .rfl

中文:
定理 hasEval_def
  条件: (a : S)
  结论: HasEval a ↔ IsTopologicallyNilpotent a
  证明: .rfl

Depends on / 依赖: Ultrafilter, X.str
-/
theorem hasEval_def (a : S) : HasEval a ↔ IsTopologicallyNilpotent a := .rfl

/--
theorem `hasEval_iff` / 定理 `hasEval_iff`

English:
theorem hasEval_iff
  given: {a : S}
  proof: ⟨fun ha => ⟨fun _ => ha, by simp⟩, fun ha => ha.hpow default⟩

中文:
定理 hasEval_iff
  条件: {a : S}
  证明: ⟨fun ha => ⟨fun _ => ha, by simp⟩, fun ha => ha.hpow default⟩

Depends on / 依赖: ha.hpow
-/
theorem hasEval_iff {a : S} :
    HasEval a ↔ MvPowerSeries.HasEval (fun (_ : Unit) => a) :=
  ⟨fun ha => ⟨fun _ => ha, by simp⟩, fun ha => ha.hpow default⟩

/--
theorem `hasEval` / 定理 `hasEval`

English:
theorem hasEval
  given: {a : S} (ha : HasEval a)
  proof: hasEval_iff.mp ha

中文:
定理 hasEval
  条件: {a : S} (ha : HasEval a)
  证明: hasEval_iff.mp ha

Depends on / 依赖: X.str, hasEval_iff, hasEval_iff.mp, isCompact_iff_ultrafilter_le_nhds, le_nhds_iff
-/
theorem hasEval {a : S} (ha : HasEval a) :
    MvPowerSeries.HasEval (fun (_ : Unit) => a) := hasEval_iff.mp ha

/--
theorem `HasEval.mono` / 定理 `HasEval.mono`

English:
theorem HasEval.mono
  statement: {S : Type*} [CommRing S] {a : S}
  proof: by
  simp only [hasEval_iff] at ha ⊢
  exact ha.mono h

中文:
定理 HasEval.mono
  结论: {S : 类型} [CommRing S] {a : S}
  证明: by
  simp only [hasEval_iff] at ha ⊢
  exact ha.mono h
-/
theorem HasEval.mono {S : Type*} [CommRing S] {a : S}
    {t u : TopologicalSpace S} (h : t <= u) (ha : @HasEval _ _ t a) :
    @HasEval _ _ u a := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.mono h

/--
theorem `HasEval.zero` / 定理 `HasEval.zero`

English:
theorem HasEval.zero
  statement: HasEval (0 : S)
  proof: by
    rw [hasEval_iff]; exact MvPowerSeries.HasEval.zero

中文:
定理 HasEval.zero
  结论: HasEval (0 : S)
  证明: by
    rw [hasEval_iff]; exact MvPowerSeries.HasEval.zero
-/
theorem HasEval.zero : HasEval (0 : S) := by
    rw [hasEval_iff]; exact MvPowerSeries.HasEval.zero

/--
theorem `HasEval.add` / 定理 `HasEval.add`

English:
theorem HasEval.add
  statement: [ContinuousAdd S] [IsLinearTopology S S]
  proof: by
  simp only [hasEval_iff] at ha hb ⊢
  exact ha.add hb

中文:
定理 HasEval.add
  结论: [ContinuousAdd S] [IsLinearTopology S S]
  证明: by
  simp only [hasEval_iff] at ha hb ⊢
  exact ha.add hb
-/
theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
    {a b : S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) := by
  simp only [hasEval_iff] at ha hb ⊢
  exact ha.add hb

/--
theorem `HasEval.mul_left` / 定理 `HasEval.mul_left`

English:
theorem HasEval.mul_left
  statement: [IsLinearTopology S S]
  proof: by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_left _

中文:
定理 HasEval.mul_left
  结论: [IsLinearTopology S S]
  证明: by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_left _

Depends on / 依赖: str_eq_of_le_nhds, t2_iff_ultrafilter
-/
theorem HasEval.mul_left [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (c * x) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_left _

/--
theorem `HasEval.mul_right` / 定理 `HasEval.mul_right`

English:
theorem HasEval.mul_right
  statement: [IsLinearTopology S S]
  proof: by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_right _

中文:
定理 HasEval.mul_right
  结论: [IsLinearTopology S S]
  证明: by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_right _
-/
theorem HasEval.mul_right [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (x * c) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_right _

/--
theorem `HasEval.map` / 定理 `HasEval.map`

English:
theorem HasEval.map
  given: (hφ : Continuous φ) {a : R} (ha : HasEval a)
  proof: by
  simp only [hasEval_iff] at ha ⊢
  exact ha.map hφ

中文:
定理 HasEval.map
  条件: (hφ : Continuous φ) {a : R} (ha : HasEval a)
  证明: by
  simp only [hasEval_iff] at ha ⊢
  exact ha.map hφ
-/
theorem HasEval.map (hφ : Continuous φ) {a : R} (ha : HasEval a) :
    HasEval (φ a) := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.map hφ

/--
theorem `HasEval.X` / 定理 `HasEval.X`

English:
theorem HasEval.X
  proof: by
  rw [hasEval_iff]
  exact MvPowerSeries.HasEval.X

中文:
定理 HasEval.X
  证明: by
  rw [hasEval_iff]
  exact MvPowerSeries.HasEval.X
-/
protected theorem HasEval.X :
    HasEval (X : R⟦X⟧) := by
  rw [hasEval_iff]
  exact MvPowerSeries.HasEval.X


variable [IsTopologicalRing S] [IsLinearTopology S S]

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
@[simps]
/--
Definition of `hasEvalIdeal` / `hasEvalIdeal` 的定义

English:
definition hasEvalIdeal
  signature: : Ideal S where
  body: {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

中文:
定义 hasEvalIdeal
  签名: : Ideal S where
  定义体: {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

Depends on / 依赖: HasEval
-/
def hasEvalIdeal : Ideal S where
  carrier := {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_hasEvalIdeal_iff` / 定理 `mem_hasEvalIdeal_iff`

English:
theorem mem_hasEvalIdeal_iff
  given: {a : S}
  proof: by
  simp [hasEvalIdeal]

中文:
定理 mem_hasEvalIdeal_iff
  条件: {a : S}
  证明: by
  simp [hasEvalIdeal]

Depends on / 依赖: hasEvalIdeal
-/
theorem mem_hasEvalIdeal_iff {a : S} :
    a in hasEvalIdeal ↔ HasEval a := by
  simp [hasEvalIdeal]

end

variable (φ : R ->+* S) (a : S)

variable [UniformSpace R] [UniformSpace S]

/--
Definition of `eval₂` / `eval₂` 的定义

English:
definition eval₂
  signature: : PowerSeries R -> S
  body: MvPowerSeries.eval₂ φ (fun _ => a)

@[simp]

中文:
定义 eval₂
  签名: : PowerSeries R -> S
  定义体: MvPowerSeries.eval₂ φ (fun _ => a)

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.eval
-/
noncomputable def eval₂ : PowerSeries R -> S :=
  MvPowerSeries.eval₂ φ (fun _ => a)

@[simp]
/--
theorem `eval₂_coe` / 定理 `eval₂_coe`

English:
theorem eval₂_coe
  given: (f : Polynomial R)
  statement: eval₂ φ a f = f.eval₂ φ a
  proof: by
  rw [← (MvPolynomial.uniqueAlgEquiv R Unit).apply_symm_apply f]
  simp only [PowerSeries.eval₂, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  rw [← MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [MvPowerSeries.eval₂_coe]

@[simp]

中文:
定理 eval₂_coe
  条件: (f : Polynomial R)
  结论: eval₂ φ a f = f.eval₂ φ a
  证明: by
  rw [← (MvPolynomial.uniqueAlgEquiv R Unit).apply_symm_apply f]
  simp only [PowerSeries.eval₂, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  rw [← MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [MvPowerSeries.eval₂_coe]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, MvPolynomial.uniqueAlgEquiv, MvPowerSeries, MvPowerSeries.eval, PowerSeries, PowerSeries.eval, apply_symm_apply, toMvPowerSeries_pUnitAlgEquiv, uniqueAlgEquiv
-/
theorem eval₂_coe (f : Polynomial R) : eval₂ φ a f = f.eval₂ φ a := by
  rw [← (MvPolynomial.uniqueAlgEquiv R Unit).apply_symm_apply f]
  simp only [PowerSeries.eval₂, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  rw [← MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [MvPowerSeries.eval₂_coe]

@[simp]
/--
theorem `eval₂_C` / 定理 `eval₂_C`

English:
theorem eval₂_C
  given: (r : R)
  proof: by
  rw [← Polynomial.coe_C]; rw [eval₂_coe]; rw [Polynomial.eval₂_C]

@[simp]

中文:
定理 eval₂_C
  条件: (r : R)
  证明: by
  rw [← Polynomial.coe_C]; rw [eval₂_coe]; rw [Polynomial.eval₂_C]

@[simp]

Depends on / 依赖: Polynomial, Polynomial.coe_C, Polynomial.eval, coe_C
-/
theorem eval₂_C (r : R) :
    eval₂ φ a (C r) = φ r := by
  rw [← Polynomial.coe_C]; rw [eval₂_coe]; rw [Polynomial.eval₂_C]

@[simp]
/--
theorem `eval₂_X` / 定理 `eval₂_X`

English:
theorem eval₂_X
  proof: by
  rw [← Polynomial.coe_X]; rw [eval₂_coe]; rw [Polynomial.eval₂_X]

中文:
定理 eval₂_X
  证明: by
  rw [← Polynomial.coe_X]; rw [eval₂_coe]; rw [Polynomial.eval₂_X]

Depends on / 依赖: Polynomial, Polynomial.coe_X, Polynomial.eval, coe_X
-/
theorem eval₂_X :
    eval₂ φ a X = a := by
  rw [← Polynomial.coe_X]; rw [eval₂_coe]; rw [Polynomial.eval₂_X]

variable {φ a}

variable [IsUniformAddGroup R] [IsTopologicalSemiring R]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]

/--
Definition of `eval₂Hom` / `eval₂Hom` 的定义

English:
definition eval₂Hom
  signature: (hφ : Continuous φ) (ha : HasEval a)
  body: MvPowerSeries.eval₂Hom hφ (hasEval ha)

中文:
定义 eval₂Hom
  签名: (hφ : Continuous φ) (ha : HasEval a)
  定义体: MvPowerSeries.eval₂Hom hφ (hasEval ha)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.eval, hasEval
-/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    PowerSeries R ->+* S :=
  MvPowerSeries.eval₂Hom hφ (hasEval ha)

/--
theorem `coe_eval₂Hom` / 定理 `coe_eval₂Hom`

English:
theorem coe_eval₂Hom
  given: (hφ : Continuous φ) (ha : HasEval a)
  proof: MvPowerSeries.coe_eval₂Hom hφ (hasEval ha)

中文:
定理 coe_eval₂Hom
  条件: (hφ : Continuous φ) (ha : HasEval a)
  证明: MvPowerSeries.coe_eval₂Hom hφ (hasEval ha)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coe_eval, hasEval
-/
theorem coe_eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a :=
  MvPowerSeries.coe_eval₂Hom hφ (hasEval ha)

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
/--
theorem `uniformContinuous_eval₂` / 定理 `uniformContinuous_eval₂`

English:
theorem uniformContinuous_eval₂
  given: (hφ : Continuous φ) (ha : HasEval a)
  proof: MvPowerSeries.uniformContinuous_eval₂ hφ (hasEval ha)

中文:
定理 uniformContinuous_eval₂
  条件: (hφ : Continuous φ) (ha : HasEval a)
  证明: MvPowerSeries.uniformContinuous_eval₂ hφ (hasEval ha)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.uniformContinuous_eval, hasEval
-/
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (eval₂ φ a) :=
  MvPowerSeries.uniformContinuous_eval₂ hφ (hasEval ha)

/--
theorem `continuous_eval₂` / 定理 `continuous_eval₂`

English:
theorem continuous_eval₂
  given: (hφ : Continuous φ) (ha : HasEval a)
  proof: (uniformContinuous_eval₂ hφ ha).continuous

中文:
定理 continuous_eval₂
  条件: (hφ : Continuous φ) (ha : HasEval a)
  证明: (uniformContinuous_eval₂ hφ ha).continuous

Depends on / 依赖: continuous
-/
theorem continuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    Continuous (eval₂ φ a : PowerSeries R -> S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

/--
theorem `hasSum_eval₂` / 定理 `hasSum_eval₂`

English:
theorem hasSum_eval₂
  given: (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R)
  proof: by
  have := MvPowerSeries.hasSum_eval₂ hφ (hasEval ha) f
  simp only [PowerSeries.eval₂]
  rw [← (Finsupp.single_injective ()).hasSum_iff] at this
  · convert this; simp
  · intro d hd
    exact False.elim (hd ⟨d (), by ext; simp⟩)

中文:
定理 hasSum_eval₂
  条件: (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R)
  证明: by
  have := MvPowerSeries.hasSum_eval₂ hφ (hasEval ha) f
  simp only [PowerSeries.eval₂]
  rw [← (Finsupp.single_injective ()).hasSum_iff] at this
  · convert this; simp
  · intro d hd
    exact False.elim (hd ⟨d (), by ext; simp⟩)

Depends on / 依赖: False.elim, Finsupp, Finsupp.single_injective, MvPowerSeries, MvPowerSeries.hasSum_eval, PowerSeries, PowerSeries.eval, convert, hasEval, hasSum_iff, single_injective
-/
theorem hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R) :
    HasSum (fun (d : Nat) => φ (coeff d f) * a ^ d) (f.eval₂ φ a) := by
  have := MvPowerSeries.hasSum_eval₂ hφ (hasEval ha) f
  simp only [PowerSeries.eval₂]
  rw [← (Finsupp.single_injective ()).hasSum_iff] at this
  · convert this; simp
  · intro d hd
    exact False.elim (hd ⟨d (), by ext; simp⟩)

/--
theorem `eval₂_eq_tsum` / 定理 `eval₂_eq_tsum`

English:
theorem eval₂_eq_tsum
  given: (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R)
  proof: (hasSum_eval₂ hφ ha f).tsum_eq.symm

中文:
定理 eval₂_eq_tsum
  条件: (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R)
  证明: (hasSum_eval₂ hφ ha f).tsum_eq.symm

Depends on / 依赖: tsum_eq, tsum_eq.symm
-/
theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : HasEval a) (f : PowerSeries R) :
    PowerSeries.eval₂ φ a f =
      ∑' d : Nat, φ (coeff d f) * a ^ d :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

/--
theorem `eval₂_unique` / 定理 `eval₂_unique`

English:
theorem eval₂_unique
  statement: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  refine MvPowerSeries.eval₂_unique hφ (hasEval ha) hε (fun p => ?_)
  rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [h]; rw [← MvPolynomial.eval₂_uniqueAlgEquiv]

中文:
定理 eval₂_unique
  结论: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  refine MvPowerSeries.eval₂_unique hφ (hasEval ha) hε (fun p => ?_)
  rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [h]; rw [← MvPolynomial.eval₂_uniqueAlgEquiv]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, MvPowerSeries, MvPowerSeries.eval, hasEval, toMvPowerSeries_pUnitAlgEquiv
-/
theorem eval₂_unique (hφ : Continuous φ) (ha : HasEval a)
    {ε : PowerSeries R -> S} (hε : Continuous ε)
    (h : forall p : Polynomial R, ε p = Polynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  refine MvPowerSeries.eval₂_unique hφ (hasEval ha) hε (fun p => ?_)
  rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv]; rw [h]; rw [← MvPolynomial.eval₂_uniqueAlgEquiv]

/--
theorem `comp_eval₂` / 定理 `comp_eval₂`

English:
theorem comp_eval₂
  statement: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  refine eval₂_unique (by simp only [RingHom.coe_comp, hε.comp hφ]) (ha.map hε)
    (hε.comp (continuous_eval₂ hφ ha)) (fun p => ?_)
  simpa [Function.comp_apply, eval₂_coe] using p.hom_eval₂ φ ε a

中文:
定理 comp_eval₂
  结论: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  refine eval₂_unique (by simp only [RingHom.coe_comp, hε.comp hφ]) (ha.map hε)
    (hε.comp (continuous_eval₂ hφ ha)) (fun p => ?_)
  simpa [Function.comp_apply, eval₂_coe] using p.hom_eval₂ φ ε a

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, comp_apply, ha.map, p.hom_eval
-/
theorem comp_eval₂ (hφ : Continuous φ) (ha : HasEval a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T]
    {ε : S ->+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε a) := by
  refine eval₂_unique (by simp only [RingHom.coe_comp, hε.comp hφ]) (ha.map hε)
    (hε.comp (continuous_eval₂ hφ ha)) (fun p => ?_)
  simpa [Function.comp_apply, eval₂_coe] using p.hom_eval₂ φ ε a

variable [Algebra R S] [ContinuousSMul R S]

/--
Definition of `aeval` / `aeval` 的定义

English:
definition aeval
  signature: (ha : HasEval a)
  body: MvPowerSeries.aeval (hasEval ha)

中文:
定义 aeval
  签名: (ha : HasEval a)
  定义体: MvPowerSeries.aeval (hasEval ha)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.aeval, hasEval
-/
noncomputable def aeval (ha : HasEval a) :
    PowerSeries R ->ₐ[R] S :=
  MvPowerSeries.aeval (hasEval ha)

/--
theorem `coe_aeval` / 定理 `coe_aeval`

English:
theorem coe_aeval
  given: (ha : HasEval a)
  proof: MvPowerSeries.coe_aeval (hasEval ha)

中文:
定理 coe_aeval
  条件: (ha : HasEval a)
  证明: MvPowerSeries.coe_aeval (hasEval ha)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coe_aeval, coe_aeval, hasEval
-/
theorem coe_aeval (ha : HasEval a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a :=
  MvPowerSeries.coe_aeval (hasEval ha)

/--
theorem `continuous_aeval` / 定理 `continuous_aeval`

English:
theorem continuous_aeval
  given: (ha : HasEval a)
  proof: MvPowerSeries.continuous_aeval (hasEval ha)

@[simp]

中文:
定理 continuous_aeval
  条件: (ha : HasEval a)
  证明: MvPowerSeries.continuous_aeval (hasEval ha)

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.continuous_aeval, continuous_aeval, hasEval
-/
theorem continuous_aeval (ha : HasEval a) :
    Continuous (aeval ha : PowerSeries R -> S) :=
  MvPowerSeries.continuous_aeval (hasEval ha)

@[simp]
/--
theorem `aeval_coe` / 定理 `aeval_coe`

English:
theorem aeval_coe
  given: (ha : HasEval a) (p : Polynomial R)
  proof: by
  rw [coe_aeval]; rw [Polynomial.aeval_def]; rw [eval₂_coe]

中文:
定理 aeval_coe
  条件: (ha : HasEval a) (p : Polynomial R)
  证明: by
  rw [coe_aeval]; rw [Polynomial.aeval_def]; rw [eval₂_coe]

Depends on / 依赖: Polynomial, Polynomial.aeval_def, aeval_def, coe_aeval
-/
theorem aeval_coe (ha : HasEval a) (p : Polynomial R) :
    aeval ha (p : PowerSeries R) = Polynomial.aeval a p := by
  rw [coe_aeval]; rw [Polynomial.aeval_def]; rw [eval₂_coe]

/--
theorem `aeval_unique` / 定理 `aeval_unique`

English:
theorem aeval_unique
  given: {ε : PowerSeries R ->ₐ[R] S} (hε : Continuous ε)
  proof: MvPowerSeries.aeval_unique hε

中文:
定理 aeval_unique
  条件: {ε : PowerSeries R ->ₐ[R] S} (hε : Continuous ε)
  证明: MvPowerSeries.aeval_unique hε

Depends on / 依赖: MvPowerSeries, MvPowerSeries.aeval_unique, aeval_unique
-/
theorem aeval_unique {ε : PowerSeries R ->ₐ[R] S} (hε : Continuous ε) :
    aeval (HasEval.X.map hε) = ε :=
  MvPowerSeries.aeval_unique hε

/--
theorem `hasSum_aeval` / 定理 `hasSum_aeval`

English:
theorem hasSum_aeval
  given: (ha : HasEval a) (f : PowerSeries R)
  proof: by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

中文:
定理 hasSum_aeval
  条件: (ha : HasEval a) (f : PowerSeries R)
  证明: by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

Depends on / 依赖: algebraMap_smul, coe_aeval, continuous_algebraMap, simp_rw, smul_eq_mul
-/
theorem hasSum_aeval (ha : HasEval a) (f : PowerSeries R) :
    HasSum (fun d => coeff d f • a ^ d) (f.aeval ha) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

/--
theorem `aeval_eq_sum` / 定理 `aeval_eq_sum`

English:
theorem aeval_eq_sum
  given: (ha : HasEval a) (f : PowerSeries R)
  proof: (hasSum_aeval ha f).tsum_eq.symm

中文:
定理 aeval_eq_sum
  条件: (ha : HasEval a) (f : PowerSeries R)
  证明: (hasSum_aeval ha f).tsum_eq.symm

Depends on / 依赖: hasSum_aeval, tsum_eq, tsum_eq.symm
-/
theorem aeval_eq_sum (ha : HasEval a) (f : PowerSeries R) :
    aeval ha f = tsum fun d => coeff d f • a ^ d :=
  (hasSum_aeval ha f).tsum_eq.symm

/--
theorem `comp_aeval` / 定理 `comp_aeval`

English:
theorem comp_aeval
  statement: (ha : HasEval a)
  proof: MvPowerSeries.comp_aeval (hasEval ha) hε

中文:
定理 comp_aeval
  结论: (ha : HasEval a)
  证明: MvPowerSeries.comp_aeval (hasEval ha) hε

Depends on / 依赖: MvPowerSeries, MvPowerSeries.comp_aeval, comp_aeval, hasEval
-/
theorem comp_aeval (ha : HasEval a)
    {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S ->ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε) :=
  MvPowerSeries.comp_aeval (hasEval ha) hε

end PowerSeries
