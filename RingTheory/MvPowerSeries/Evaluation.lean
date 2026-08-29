/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.UniformRing

/-! # Evaluation of multivariate power series

Let `σ`, `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : σ → S`, and `f : MvPowerSeries σ R`,
`MvPowerSeries.eval₂ f φ a` is the evaluation of the multivariate power series `f` at `a`.
If `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` satisfies two conditions
bundled in `MvPowerSeries.HasEval a` :
  - for all `s : σ`, `a s` is topologically nilpotent,
    meaning that `(a s) ^ n` tends to 0 when `n` tends to infinity
  - when `a s` tends to zero for the filter of cofinite subsets of `σ`.

Under `Continuous φ` and `HasEval a`, the following lemmas furnish the properties of evaluation:

* `MvPowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `MvPowerSeries.aeval`: the evaluation map as an algebra morphism
* `MvPowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `MvPowerSeries.continuous_eval₂`: continuity of the evaluation
* `MvPowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

-/

@[expose] public section

namespace MvPowerSeries

open Topology

open Filter MvPolynomial RingHom Set TopologicalSpace UniformSpace

/- ## Necessary conditions -/

section

variable {σ : Type*}
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
variable {φ : R ->+* S}

-- We endow MvPowerSeries σ R with the Pi topology
open WithPiTopology

/-- Families at which power series can be consistently evaluated -/
@[mk_iff hasEval_def]
/--
Definition of `HasEval` / `HasEval` 的定义

English:
structure HasEval
  parameters: (a : σ -> S)
  axioms and operations (2):
    - hpow : forall s, IsTopologicallyNilpotent (a s)
    - tendsto_zero : Tendsto a cofinite (𝓝 0)

中文:
结构 HasEval
  参数: (a : σ -> S)
  公理与运算 (2 个):
    - hpow : 对任意 s, IsTopologicallyNilpotent (a s)
    - tendsto_zero : Tendsto a cofinite (𝓝 0)
-/
structure HasEval (a : σ -> S) : Prop where
  hpow : forall s, IsTopologicallyNilpotent (a s)
  tendsto_zero : Tendsto a cofinite (𝓝 0)

/--
theorem `HasEval.mono` / 定理 `HasEval.mono`

English:
theorem HasEval.mono
  statement: {S : Type*} [CommRing S] {a : σ -> S}
  proof: ⟨fun s => Filter.Tendsto.mono_right (@HasEval.hpow _ _ _ t a ha s) (nhds_mono h),
   Filter.Tendsto.mono_right (@HasEval.tendsto_zero σ _ _ t a ha) (nhds_mono h)⟩

中文:
定理 HasEval.mono
  结论: {S : 类型} [CommRing S] {a : σ -> S}
  证明: ⟨fun s => Filter.Tendsto.mono_right (@HasEval.hpow _ _ _ t a ha s) (nhds_mono h),
   Filter.Tendsto.mono_right (@HasEval.tendsto_zero σ _ _ t a ha) (nhds_mono h)⟩

Depends on / 依赖: Filter, Filter.Tendsto.mono_right, HasEval, HasEval.hpow, HasEval.tendsto_zero, Tendsto, mono_right, nhds_mono, tendsto_zero
-/
theorem HasEval.mono {S : Type*} [CommRing S] {a : σ -> S}
    {t u : TopologicalSpace S} (h : t <= u) (ha : @HasEval _ _ _ t a) :
    @HasEval _ _ _ u a :=
  ⟨fun s => Filter.Tendsto.mono_right (@HasEval.hpow _ _ _ t a ha s) (nhds_mono h),
   Filter.Tendsto.mono_right (@HasEval.tendsto_zero σ _ _ t a ha) (nhds_mono h)⟩

/--
theorem `HasEval.zero` / 定理 `HasEval.zero`

English:
theorem HasEval.zero
  statement: HasEval (0 : σ -> S) where
  proof: .zero
  tendsto_zero := tendsto_const_nhds

中文:
定理 HasEval.zero
  结论: HasEval (0 : σ -> S) where
  证明: .zero
  tendsto_zero := tendsto_const_nhds
-/
theorem HasEval.zero : HasEval (0 : σ -> S) where
  hpow _ := .zero
  tendsto_zero := tendsto_const_nhds

/--
theorem `HasEval.add` / 定理 `HasEval.add`

English:
theorem HasEval.add
  statement: [ContinuousAdd S] [IsLinearTopology S S]
  proof: (ha.hpow s).add (hb.hpow s)
  tendsto_zero := by rw [← add_zero 0]; exact ha.tendsto_zero.add hb.tendsto_zero

中文:
定理 HasEval.add
  结论: [ContinuousAdd S] [IsLinearTopology S S]
  证明: (ha.hpow s).add (hb.hpow s)
  tendsto_zero := by rw [← add_zero 0]; exact ha.tendsto_zero.add hb.tendsto_zero

Depends on / 依赖: ha.hpow, hb.hpow
-/
theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
    {a b : σ -> S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) where
  hpow s := (ha.hpow s).add (hb.hpow s)
  tendsto_zero := by rw [← add_zero 0]; exact ha.tendsto_zero.add hb.tendsto_zero

/--
theorem `HasEval.mul_left` / 定理 `HasEval.mul_left`

English:
theorem HasEval.mul_left
  statement: [IsLinearTopology S S]
  proof: (hx.hpow s).mul_left (c s)
  tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero

中文:
定理 HasEval.mul_left
  结论: [IsLinearTopology S S]
  证明: (hx.hpow s).mul_left (c s)
  tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero

Depends on / 依赖: hx.hpow, mul_left
-/
theorem HasEval.mul_left [IsLinearTopology S S]
    (c : σ -> S) {x : σ -> S} (hx : HasEval x) : HasEval (c * x) where
  hpow s := (hx.hpow s).mul_left (c s)
  tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero

/--
theorem `HasEval.mul_right` / 定理 `HasEval.mul_right`

English:
theorem HasEval.mul_right
  statement: [IsLinearTopology S S]
  proof: mul_comm x c ▸ HasEval.mul_left c hx

中文:
定理 HasEval.mul_right
  结论: [IsLinearTopology S S]
  证明: mul_comm x c ▸ HasEval.mul_left c hx

Depends on / 依赖: HasEval, HasEval.mul_left, mul_comm, mul_left
-/
theorem HasEval.mul_right [IsLinearTopology S S]
    (c : σ -> S) {x : σ -> S} (hx : HasEval x) : HasEval (x * c) :=
  mul_comm x c ▸ HasEval.mul_left c hx

/--
theorem `HasEval.map` / 定理 `HasEval.map`

English:
theorem HasEval.map
  given: (hφ : Continuous φ) {a : σ -> R} (ha : HasEval a)
  proof: (ha.hpow s).map hφ
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero

中文:
定理 HasEval.map
  条件: (hφ : Continuous φ) {a : σ -> R} (ha : HasEval a)
  证明: (ha.hpow s).map hφ
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero

Depends on / 依赖: ha.hpow
-/
theorem HasEval.map (hφ : Continuous φ) {a : σ -> R} (ha : HasEval a) :
    HasEval (fun s => φ (a s)) where
  hpow s := (ha.hpow s).map hφ
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero

/--
theorem `HasEval.X` / 定理 `HasEval.X`

English:
theorem HasEval.X
  proof: isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero

中文:
定理 HasEval.X
  证明: isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero
-/
protected theorem HasEval.X :
    HasEval (fun s => (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow s := isTopologicallyNilpotent_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero

variable [IsTopologicalRing S] [IsLinearTopology S S]

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
@[simps]
/--
Definition of `hasEvalIdeal` / `hasEvalIdeal` 的定义

English:
definition hasEvalIdeal
  signature: : Ideal (σ -> S) where
  body: {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

中文:
定义 hasEvalIdeal
  签名: : Ideal (σ -> S) where
  定义体: {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

Depends on / 依赖: HasEval
-/
def hasEvalIdeal : Ideal (σ -> S) where
  carrier := {a | HasEval a}
  add_mem' := HasEval.add
  zero_mem' := HasEval.zero
  smul_mem' := HasEval.mul_left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_hasEvalIdeal_iff` / 定理 `mem_hasEvalIdeal_iff`

English:
theorem mem_hasEvalIdeal_iff
  given: {a : σ -> S}
  proof: by
  simp [hasEvalIdeal]

中文:
定理 mem_hasEvalIdeal_iff
  条件: {a : σ -> S}
  证明: by
  simp [hasEvalIdeal]

Depends on / 依赖: hasEvalIdeal
-/
theorem mem_hasEvalIdeal_iff {a : σ -> S} :
    a in hasEvalIdeal ↔ HasEval a := by
  simp [hasEvalIdeal]

/--
theorem `HasEval.pow` / 定理 `HasEval.pow`

English:
theorem HasEval.pow
  given: (x : σ -> S) (ha : HasEval x) {p : Nat} (hp : 0 < p)
  proof: mem_hasEvalIdeal_iff.mp Ideal.pow_mem_of_mem hasEvalIdeal ha p hp

中文:
定理 HasEval.pow
  条件: (x : σ -> S) (ha : HasEval x) {p : 自然数} (hp : 0 < p)
  证明: mem_hasEvalIdeal_iff.mp Ideal.pow_mem_of_mem hasEvalIdeal ha p hp

Depends on / 依赖: Ideal.pow_mem_of_mem, hasEvalIdeal, mem_hasEvalIdeal_iff, mem_hasEvalIdeal_iff.mp, pow_mem_of_mem
-/
theorem HasEval.pow (x : σ -> S) (ha : HasEval x) {p : Nat} (hp : 0 < p) :
    HasEval (x ^ p) :=
mem_hasEvalIdeal_iff.mp Ideal.pow_mem_of_mem hasEvalIdeal ha p hp

end

/- ## Construction of an evaluation morphism for power series -/

section Evaluation

open WithPiTopology

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R]
variable {S : Type*} [CommRing S] [UniformSpace S]
variable {φ : R ->+* S}

-- We endow MvPowerSeries σ R with the product uniform structure
set_option backward.privateInPublic true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UniformSpace (MvPolynomial σ R)
  body: comap toMvPowerSeries inferInstance

中文:
实例 :
  签名: UniformSpace (MvPolynomial σ R)
  定义体: comap toMvPowerSeries inferInstance
-/
private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsUniformAddGroup
  signature: R] : IsUniformAddGroup (MvPolynomial σ R)
  body: IsUniformAddGroup.comap coeToMvPowerSeries.ringHom

中文:
实例 [IsUniformAddGroup
  签名: R] : IsUniformAddGroup (MvPolynomial σ R)
  定义体: IsUniformAddGroup.comap coeToMvPowerSeries.ringHom
-/
private instance [IsUniformAddGroup R] : IsUniformAddGroup (MvPolynomial σ R) :=
  IsUniformAddGroup.comap coeToMvPowerSeries.ringHom

/--
theorem `_root_.MvPolynomial.toMvPowerSeries_isUniformInducing` / 定理 `_root_.MvPolynomial.toMvPowerSeries_isUniformInducing`

English:
theorem _root_.MvPolynomial.toMvPowerSeries_isUniformInducing
  proof: (isUniformInducing_iff toMvPowerSeries).mpr rfl

中文:
定理 _root_.MvPolynomial.toMvPowerSeries_isUniformInducing
  证明: (isUniformInducing_iff toMvPowerSeries).mpr rfl
-/
theorem _root_.MvPolynomial.toMvPowerSeries_isUniformInducing :
    IsUniformInducing (toMvPowerSeries (σ := σ) (R := R)) :=
  (isUniformInducing_iff toMvPowerSeries).mpr rfl

/--
theorem `_root_.MvPolynomial.toMvPowerSeries_isDenseInducing` / 定理 `_root_.MvPolynomial.toMvPowerSeries_isDenseInducing`

English:
theorem _root_.MvPolynomial.toMvPowerSeries_isDenseInducing
  proof: toMvPowerSeries_isUniformInducing.isDenseInducing denseRange_toMvPowerSeries

中文:
定理 _root_.MvPolynomial.toMvPowerSeries_isDenseInducing
  证明: toMvPowerSeries_isUniformInducing.isDenseInducing denseRange_toMvPowerSeries
-/
theorem _root_.MvPolynomial.toMvPowerSeries_isDenseInducing :
    IsDenseInducing (toMvPowerSeries (σ := σ) (R := R)) :=
  toMvPowerSeries_isUniformInducing.isDenseInducing denseRange_toMvPowerSeries

variable {a : σ -> S}

/--
theorem `_root_.MvPolynomial.toMvPowerSeries_uniformContinuous` / 定理 `_root_.MvPolynomial.toMvPowerSeries_uniformContinuous`

English:
theorem _root_.MvPolynomial.toMvPowerSeries_uniformContinuous
  proof: by
  classical
  apply uniformContinuous_of_continuousAt_zero
  rw [ContinuousAt]; rw [map_zero]; rw [IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  let n : σ -> Nat := fun s => sInf {n : Nat | (a s) ^ n.succ in I}
  have hn_ne : forall s, Set.Nonempty {n : Nat | (a s) ^ n.succ in

中文:
定理 _root_.MvPolynomial.toMvPowerSeries_uniformContinuous
  证明: by
  classical
  apply uniformContinuous_of_continuousAt_zero
  rw [ContinuousAt]; rw [map_zero]; rw [IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  let n : σ -> Nat := fun s => sInf {n : Nat | (a s) ^ n.succ in I}
  have hn_ne : forall s, Set.Nonempty {n : Nat | (a s) ^ n.succ in

Depends on / 依赖: ContinuousAt, Finite, IsLinearTopology, IsLinearTopology.hasBasis_ideal.tendsto_right_iff, Nonempty, Set.Finite, Set.Nonempty, classical, cofinite, eventually_mem, exists_forall_of_atTop, filter_upwards, ha.hpow, hasBasis_ideal, hn_ne, le_succ, map_zero, n.le_succ, n.succ, n.support
-/
theorem _root_.MvPolynomial.toMvPowerSeries_uniformContinuous
    [IsUniformAddGroup R] [IsUniformAddGroup S] [IsLinearTopology S S]
    (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  classical
  apply uniformContinuous_of_continuousAt_zero
  rw [ContinuousAt]; rw [map_zero]; rw [IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  let n : σ -> Nat := fun s => sInf {n : Nat | (a s) ^ n.succ in I}
  have hn_ne : forall s, Set.Nonempty {n : Nat | (a s) ^ n.succ in I} := fun s => by
.exists_forall_of_atTop with ⟨n, hn⟩ .eventually_mem hI rcases ha.hpow s
    use n
    simpa using hn n.succ n.le_succ
  have hn : Set.Finite (n.support) := by
    change n =ᶠ[cofinite] 0
    filter_upwards [ha.tendsto_zero.eventually_mem hI] with s has
    simpa [n, Pi.zero_apply, Nat.sInf_eq_zero, or_iff_left (hn_ne s).ne_empty] using has
  let n₀ : σ ->₀ Nat := .ofSupportFinite n hn
  let D := Iic n₀
  have hD : Set.Finite D := finite_Iic _
  have : forall d in D, forallᶠ (p : MvPolynomial σ R) in 𝓝 0, φ (p.coeff d) in I := fun d hd => by
    have : Tendsto (φ ∘ coeff d ∘ toMvPowerSeries) (𝓝 0) (𝓝 0) :=
.tendsto' 0 0 (map_zero _) .comp continuous_induced_dom hφ.comp (continuous_coeff R d)
    filter_upwards [this.eventually_mem hI] with f hf
    simpa using hf
  rw [← hD.eventually_all] at this
  filter_upwards [this] with p hp
  rw [coe_eval₂Hom]; rw [SetLike.mem_coe]; rw [eval₂_eq]
  apply Ideal.sum_mem
  intro d _
  by_cases hd : d in D
  · exact Ideal.mul_mem_right _ _ (hp d hd)
  · apply Ideal.mul_mem_left
    simp only [mem_Iic, D, Finsupp.le_iff] at hd
    push Not at hd
    rcases hd with ⟨s, hs', hs⟩
    exact I.prod_mem hs' (I.pow_mem_of_pow_mem (Nat.sInf_mem (hn_ne s)) hs)

variable (φ a)
open scoped Classical in
/--
Definition of `eval₂` / `eval₂` 的定义

English:
definition eval₂
  signature: (f : MvPowerSeries σ R)
  body: if H : exists p : MvPolynomial σ R, p = f then (MvPolynomial.eval₂ φ a H.choose)
  else IsDenseInducing.extend toMvPowerSeries_isDenseInducing (MvPolynomial.eval₂ φ a) f

@[simp, norm_cast]

中文:
定义 eval₂
  签名: (f : MvPowerSeries σ R)
  定义体: if H : exists p : MvPolynomial σ R, p = f then (MvPolynomial.eval₂ φ a H.choose)
  else IsDenseInducing.extend toMvPowerSeries_isDenseInducing (MvPolynomial.eval₂ φ a) f

@[simp, norm_cast]

Depends on / 依赖: H.choose, IsDenseInducing, IsDenseInducing.extend, MvPolynomial, MvPolynomial.eval, extend, toMvPowerSeries_isDenseInducing
-/
noncomputable def eval₂ (f : MvPowerSeries σ R) : S :=
  if H : exists p : MvPolynomial σ R, p = f then (MvPolynomial.eval₂ φ a H.choose)
  else IsDenseInducing.extend toMvPowerSeries_isDenseInducing (MvPolynomial.eval₂ φ a) f

@[simp, norm_cast]
/--
theorem `eval₂_coe` / 定理 `eval₂_coe`

English:
theorem eval₂_coe
  given: (f : MvPolynomial σ R)
  proof: by
  have : exists p : MvPolynomial σ R, (p : MvPowerSeries σ R) = f := ⟨f, rfl⟩
  rw [eval₂]; rw [dif_pos this]
  congr
  rw [← MvPolynomial.coe_inj]; rw [this.choose_spec]

@[simp]

中文:
定理 eval₂_coe
  条件: (f : MvPolynomial σ R)
  证明: by
  have : exists p : MvPolynomial σ R, (p : MvPowerSeries σ R) = f := ⟨f, rfl⟩
  rw [eval₂]; rw [dif_pos this]
  congr
  rw [← MvPolynomial.coe_inj]; rw [this.choose_spec]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.coe_inj, MvPowerSeries, choose_spec, coe_inj, dif_pos, this.choose_spec
-/
theorem eval₂_coe (f : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a f = MvPolynomial.eval₂ φ a f := by
  have : exists p : MvPolynomial σ R, (p : MvPowerSeries σ R) = f := ⟨f, rfl⟩
  rw [eval₂]; rw [dif_pos this]
  congr
  rw [← MvPolynomial.coe_inj]; rw [this.choose_spec]

@[simp]
/--
theorem `eval₂_C` / 定理 `eval₂_C`

English:
theorem eval₂_C
  given: (r : R)
  statement: eval₂ φ a (C r) = φ r
  proof: by
  rw [← coe_C]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_C]

@[simp]

中文:
定理 eval₂_C
  条件: (r : R)
  结论: eval₂ φ a (C r) = φ r
  证明: by
  rw [← coe_C]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_C]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, coe_C
-/
theorem eval₂_C (r : R) : eval₂ φ a (C r) = φ r := by
  rw [← coe_C]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_C]

@[simp]
/--
theorem `eval₂_X` / 定理 `eval₂_X`

English:
theorem eval₂_X
  given: (s : σ)
  statement: eval₂ φ a (X s) = a s
  proof: by
  rw [← coe_X]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_X]

中文:
定理 eval₂_X
  条件: (s : σ)
  结论: eval₂ φ a (X s) = a s
  证明: by
  rw [← coe_X]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_X]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, coe_X
-/
theorem eval₂_X (s : σ) : eval₂ φ a (X s) = a s := by
  rw [← coe_X]; rw [eval₂_coe]; rw [MvPolynomial.eval₂_X]

variable [IsTopologicalSemiring R] [IsUniformAddGroup R]
    [IsUniformAddGroup S] [CompleteSpace S] [T2Space S]
    [IsTopologicalRing S] [IsLinearTopology S S]

variable {φ a}

/--
Definition of `eval₂Hom` / `eval₂Hom` 的定义

English:
definition eval₂Hom
  signature: (hφ : Continuous φ) (ha : HasEval a)
  body: IsDenseInducing.extendRingHom (i := coeToMvPowerSeries.ringHom)
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

中文:
定义 eval₂Hom
  签名: (hφ : Continuous φ) (ha : HasEval a)
  定义体: IsDenseInducing.extendRingHom (i := coeToMvPowerSeries.ringHom)
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

Depends on / 依赖: IsDenseInducing, IsDenseInducing.extendRingHom, coeToMvPowerSeries, coeToMvPowerSeries.ringHom, denseRange_toMvPowerSeries, extendRingHom, ringHom, toMvPowerSeries_isUniformInducing, toMvPowerSeries_uniformContinuous
-/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    MvPowerSeries σ R ->+* S :=
  IsDenseInducing.extendRingHom (i := coeToMvPowerSeries.ringHom)
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

/--
theorem `eval₂Hom_eq_extend` / 定理 `eval₂Hom_eq_extend`

English:
theorem eval₂Hom_eq_extend
  given: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  proof: rfl

中文:
定理 eval₂Hom_eq_extend
  条件: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  证明: rfl
-/
theorem eval₂Hom_eq_extend (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    eval₂Hom hφ ha f =
      toMvPowerSeries_isDenseInducing.extend (MvPolynomial.eval₂ φ a) f :=
  rfl

/--
theorem `coe_eval₂Hom` / 定理 `coe_eval₂Hom`

English:
theorem coe_eval₂Hom
  given: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  ext f
  simp only [eval₂Hom_eq_extend, eval₂]
  split_ifs with h
  · obtain ⟨p, rfl⟩ := h
    simpa [MvPolynomial.coe_eval₂Hom] using
      toMvPowerSeries_isDenseInducing.extend_eq
        (toMvPowerSeries_uniformContinuous hφ ha).continuous p
  · rw [← eval₂Hom_eq_extend hφ ha]

中文:
定理 coe_eval₂Hom
  条件: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  ext f
  simp only [eval₂Hom_eq_extend, eval₂]
  split_ifs with h
  · obtain ⟨p, rfl⟩ := h
    simpa [MvPolynomial.coe_eval₂Hom] using
      toMvPowerSeries_isDenseInducing.extend_eq
        (toMvPowerSeries_uniformContinuous hφ ha).continuous p
  · rw [← eval₂Hom_eq_extend hφ ha]

Depends on / 依赖: MvPolynomial, MvPolynomial.coe_eval, continuous, extend_eq, split_ifs, toMvPowerSeries_isDenseInducing, toMvPowerSeries_isDenseInducing.extend_eq, toMvPowerSeries_uniformContinuous
-/
theorem coe_eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a := by
  ext f
  simp only [eval₂Hom_eq_extend, eval₂]
  split_ifs with h
  · obtain ⟨p, rfl⟩ := h
    simpa [MvPolynomial.coe_eval₂Hom] using
      toMvPowerSeries_isDenseInducing.extend_eq
        (toMvPowerSeries_uniformContinuous hφ ha).continuous p
  · rw [← eval₂Hom_eq_extend hφ ha]

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
/--
theorem `uniformContinuous_eval₂` / 定理 `uniformContinuous_eval₂`

English:
theorem uniformContinuous_eval₂
  given: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

中文:
定理 uniformContinuous_eval₂
  条件: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

Depends on / 依赖: denseRange_toMvPowerSeries, toMvPowerSeries_isUniformInducing, toMvPowerSeries_uniformContinuous, uniformContinuous_uniformly_extend
-/
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (eval₂ φ a) := by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    toMvPowerSeries_isUniformInducing
    denseRange_toMvPowerSeries
    (toMvPowerSeries_uniformContinuous hφ ha)

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
    Continuous (eval₂ φ a : MvPowerSeries σ R -> S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

/--
theorem `hasSum_eval₂` / 定理 `hasSum_eval₂`

English:
theorem hasSum_eval₂
  given: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  proof: by
  rw [← coe_eval₂Hom hφ ha]; rw [eval₂Hom_eq_extend hφ ha]
  convert! (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
      eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha

中文:
定理 hasSum_eval₂
  条件: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  证明: by
  rw [← coe_eval₂Hom hφ ha]; rw [eval₂Hom_eq_extend hφ ha]
  convert! (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
      eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha

Depends on / 依赖: Function, Function.comp_apply, MvPolynomial, MvPolynomial.coe_monomial, coe_monomial, comp_apply, convert, hasSum_of_monomials_self
-/
theorem hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ ->₀ Nat) => φ (coeff d f) * (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.eval₂ φ a f) := by
  rw [← coe_eval₂Hom hφ ha]; rw [eval₂Hom_eq_extend hφ ha]
  convert! (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
      eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha

/--
theorem `eval₂_eq_tsum` / 定理 `eval₂_eq_tsum`

English:
theorem eval₂_eq_tsum
  given: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  proof: (hasSum_eval₂ hφ ha f).tsum_eq.symm

中文:
定理 eval₂_eq_tsum
  条件: (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R)
  证明: (hasSum_eval₂ hφ ha f).tsum_eq.symm

Depends on / 依赖: tsum_eq, tsum_eq.symm
-/
theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ φ a f =
      ∑' (d : σ ->₀ Nat), φ (coeff d f) * (d.prod fun s e => (a s) ^ e) :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

/--
theorem `eval₂_unique` / 定理 `eval₂_unique`

English:
theorem eval₂_unique
  statement: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  rw [← coe_eval₂Hom hφ ha]
  exact (toMvPowerSeries_isDenseInducing.extend_unique h hε).symm

中文:
定理 eval₂_unique
  结论: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  rw [← coe_eval₂Hom hφ ha]
  exact (toMvPowerSeries_isDenseInducing.extend_unique h hε).symm

Depends on / 依赖: extend_unique, toMvPowerSeries_isDenseInducing, toMvPowerSeries_isDenseInducing.extend_unique
-/
theorem eval₂_unique (hφ : Continuous φ) (ha : HasEval a)
    {ε : MvPowerSeries σ R -> S} (hε : Continuous ε)
    (h : forall p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  rw [← coe_eval₂Hom hφ ha]
  exact (toMvPowerSeries_isDenseInducing.extend_unique h hε).symm

/--
theorem `comp_eval₂` / 定理 `comp_eval₂`

English:
theorem comp_eval₂
  statement: (hφ : Continuous φ) (ha : HasEval a)
  proof: by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    rw [← MvPolynomial.coe_eval₂Hom]; rw [← comp_apply]; rw [MvPolynomial.comp_eval₂Hom]; rw [MvPolynomial.coe_eval₂Hom]
  · simp only [coe_comp, Con

中文:
定理 comp_eval₂
  结论: (hφ : Continuous φ) (ha : HasEval a)
  证明: by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    rw [← MvPolynomial.coe_eval₂Hom]; rw [← comp_apply]; rw [MvPolynomial.comp_eval₂Hom]; rw [MvPolynomial.coe_eval₂Hom]
  · simp only [coe_comp, Con

Depends on / 依赖: Continuous, Continuous.comp, Function, Function.comp_apply, MvPolynomial, MvPolynomial.coe_eval, MvPolynomial.comp_eval, coe_comp, comp_apply, ha.map
-/
theorem comp_eval₂ (hφ : Continuous φ) (ha : HasEval a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T]
    {ε : S ->+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε ∘ a) := by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    rw [← MvPolynomial.coe_eval₂Hom]; rw [← comp_apply]; rw [MvPolynomial.comp_eval₂Hom]; rw [MvPolynomial.coe_eval₂Hom]
  · simp only [coe_comp, Continuous.comp hε hφ]

variable [Algebra R S] [ContinuousSMul R S]

/--
Definition of `aeval` / `aeval` 的定义

English:
definition aeval
  signature: (ha : HasEval a)
  body: MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' r := by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap]; rw [coe_eval₂Hom]; rw [eval₂_C]

中文:
定义 aeval
  签名: (ha : HasEval a)
  定义体: MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' r := by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap]; rw [coe_eval₂Hom]; rw [eval₂_C]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.eval, continuous_algebraMap
-/
noncomputable def aeval (ha : HasEval a) : MvPowerSeries σ R ->ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' r := by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap]; rw [coe_eval₂Hom]; rw [eval₂_C]

/--
theorem `coe_aeval` / 定理 `coe_aeval`

English:
theorem coe_aeval
  given: (ha : HasEval a)
  proof: by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]

中文:
定理 coe_aeval
  条件: (ha : HasEval a)
  证明: by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]

Depends on / 依赖: AlgHom, AlgHom.coe_mk, coe_mk
-/
theorem coe_aeval (ha : HasEval a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a := by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]

/--
theorem `continuous_aeval` / 定理 `continuous_aeval`

English:
theorem continuous_aeval
  given: (ha : HasEval a)
  proof: by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

@[simp]

中文:
定理 continuous_aeval
  条件: (ha : HasEval a)
  证明: by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

@[simp]

Depends on / 依赖: coe_aeval, continuous_algebraMap
-/
theorem continuous_aeval (ha : HasEval a) :
    Continuous (aeval ha : MvPowerSeries σ R -> S) := by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

@[simp]
/--
theorem `aeval_coe` / 定理 `aeval_coe`

English:
theorem aeval_coe
  given: (ha : HasEval a) (p : MvPolynomial σ R)
  proof: by
  rw [coe_aeval]; rw [aeval_def]; rw [eval₂_coe]

中文:
定理 aeval_coe
  条件: (ha : HasEval a) (p : MvPolynomial σ R)
  证明: by
  rw [coe_aeval]; rw [aeval_def]; rw [eval₂_coe]

Depends on / 依赖: aeval_def, coe_aeval
-/
theorem aeval_coe (ha : HasEval a) (p : MvPolynomial σ R) :
    aeval ha (p : MvPowerSeries σ R) = p.aeval a := by
  rw [coe_aeval]; rw [aeval_def]; rw [eval₂_coe]

/--
theorem `aeval_unique` / 定理 `aeval_unique`

English:
theorem aeval_unique
  given: {ε : MvPowerSeries σ R ->ₐ[R] S} (hε : Continuous ε)
  proof: by
  apply DFunLike.ext'
  rw [coe_aeval]
  refine (eval₂_unique (continuous_algebraMap R S) (HasEval.X.map hε) hε ?_).symm
  intro p
  trans ε.comp (coeToMvPowerSeries.algHom R) p
  · simp
  conv_lhs => rw [← p.aeval_X_left_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]
  simp

中文:
定理 aeval_unique
  条件: {ε : MvPowerSeries σ R ->ₐ[R] S} (hε : Continuous ε)
  证明: by
  apply DFunLike.ext'
  rw [coe_aeval]
  refine (eval₂_unique (continuous_algebraMap R S) (HasEval.X.map hε) hε ?_).symm
  intro p
  trans ε.comp (coeToMvPowerSeries.algHom R) p
  · simp
  conv_lhs => rw [← p.aeval_X_left_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]
  simp

Depends on / 依赖: DFunLike, DFunLike.ext, HasEval, HasEval.X.map, MvPolynomial, MvPolynomial.aeval_def, MvPolynomial.comp_aeval_apply, aeval_X_left_apply, aeval_def, algHom, coeToMvPowerSeries, coeToMvPowerSeries.algHom, coe_aeval, comp_aeval_apply, continuous_algebraMap, conv_lhs, p.aeval_X_left_apply
-/
theorem aeval_unique {ε : MvPowerSeries σ R ->ₐ[R] S} (hε : Continuous ε) :
    aeval (HasEval.X.map hε) = ε := by
  apply DFunLike.ext'
  rw [coe_aeval]
  refine (eval₂_unique (continuous_algebraMap R S) (HasEval.X.map hε) hε ?_).symm
  intro p
  trans ε.comp (coeToMvPowerSeries.algHom R) p
  · simp
  conv_lhs => rw [← p.aeval_X_left_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]
  simp

/--
theorem `hasSum_aeval` / 定理 `hasSum_aeval`

English:
theorem hasSum_aeval
  given: (ha : HasEval a) (f : MvPowerSeries σ R)
  proof: by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

中文:
定理 hasSum_aeval
  条件: (ha : HasEval a) (f : MvPowerSeries σ R)
  证明: by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

Depends on / 依赖: algebraMap_smul, coe_aeval, continuous_algebraMap, simp_rw, smul_eq_mul
-/
theorem hasSum_aeval (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s) ^ e))
      (MvPowerSeries.aeval ha f) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

/--
theorem `aeval_eq_sum` / 定理 `aeval_eq_sum`

English:
theorem aeval_eq_sum
  given: (ha : HasEval a) (f : MvPowerSeries σ R)
  proof: (hasSum_aeval ha f).tsum_eq.symm

中文:
定理 aeval_eq_sum
  条件: (ha : HasEval a) (f : MvPowerSeries σ R)
  证明: (hasSum_aeval ha f).tsum_eq.symm

Depends on / 依赖: hasSum_aeval, tsum_eq, tsum_eq.symm
-/
theorem aeval_eq_sum (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.aeval ha f =
      tsum (fun (d : σ ->₀ Nat) => (coeff d f) • (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_aeval ha f).tsum_eq.symm

/--
theorem `comp_aeval` / 定理 `comp_aeval`

English:
theorem comp_aeval
  statement: (ha : HasEval a)
  proof: by
  apply DFunLike.ext'
  simp only [AlgHom.coe_comp, coe_aeval ha]
  rw [← RingHom.coe_coe]; rw [comp_eval₂ (continuous_algebraMap R S) ha (show Continuous (ε : S ->+* T) from hε)]; rw [coe_aeval]
  congr!
  simp only [AlgHom.comp_algebraMap_of_tower]

中文:
定理 comp_aeval
  结论: (ha : HasEval a)
  证明: by
  apply DFunLike.ext'
  simp only [AlgHom.coe_comp, coe_aeval ha]
  rw [← RingHom.coe_coe]; rw [comp_eval₂ (continuous_algebraMap R S) ha (show Continuous (ε : S ->+* T) from hε)]; rw [coe_aeval]
  congr!
  simp only [AlgHom.comp_algebraMap_of_tower]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, AlgHom.comp_algebraMap_of_tower, Continuous, DFunLike, DFunLike.ext, RingHom, RingHom.coe_coe, coe_aeval, coe_coe, coe_comp, comp_algebraMap_of_tower, continuous_algebraMap
-/
theorem comp_aeval (ha : HasEval a)
    {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S ->ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε) := by
  apply DFunLike.ext'
  simp only [AlgHom.coe_comp, coe_aeval ha]
  rw [← RingHom.coe_coe]; rw [comp_eval₂ (continuous_algebraMap R S) ha (show Continuous (ε : S ->+* T) from hε)]; rw [coe_aeval]
  congr!
  simp only [AlgHom.comp_algebraMap_of_tower]

end Evaluation

end MvPowerSeries
