/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Data.ENat.Lattice

/-! # Substitutions in multivariate power series

Here we define the substitution of power series into other power series.
We follow [Bourbaki, Algebra II, chap. 4, §4, n° 3][bourbaki1981]
who present substitution of power series as an application of evaluation.

For an `R`-algebra `S`, `f : MvPowerSeries σ R` and `a : σ → MvPowerSeries τ S`,
`MvPowerSeries.subst a f` is the substitution of `X s` by `a s` in `f`.
It is only well defined under one of the two following conditions:
  * `f` is a polynomial, in which case it is the classical evaluation;
  * or the condition `MvPowerSeries.HasSubst a` holds, which means:
    - For every `s`, the constant coefficient of `a s` is nilpotent;
    - For every `d : σ →₀ ℕ`, all but finitely many of the coefficients
      `(a s).coeff d` vanish.

In the other cases, it is defined as 0 (dummy value).

When `HasSubst a`, `MvPowerSeries.subst a` gives rise to an algebra homomorphism
`MvPowerSeries.substAlgHom ha : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S`.

We also define `MvPowerSeries.rescale` which rescales a multivariate
power series `f : MvPowerSeries σ R` by a map `a : σ → R`
and show its relation with substitution (under `CommRing R`).
To stay in line with `PowerSeries.rescale`, this is defined by hand
for commutative *semirings*.

## Implementation note

Evaluation of a power series at adequate elements has been defined
in `Mathlib/RingTheory/MvPowerSeries/Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having nilpotent constant coefficient
* Multivariate power series have a linear topology

The function `MvPowerSeries.subst` is defined using an explicit
invocation of the discrete uniformity (`⊥`).
If users need to enter the API, they can use `MvPowerSeries.subst_eq_eval₂`
and similar lemmas that hold for whatever uniformity on the space as soon
as it is discrete.

## TODO

* `MvPowerSeries.IsNilpotent_subst` asserts that the constant coefficient
  of a legit substitution is nilpotent; prove that the converse holds when
  the kernel of `algebraMap R S` is a nil ideal.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ : Type*}
  {A : Type*} [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

attribute [local instance] DiscreteTopology.instContinuousSMul

/-- Families of power series which can be substituted -/
@[mk_iff hasSubst_def]
/--
Definition of `HasSubst` / `HasSubst` 的定义

English:
structure HasSubst
  parameters: (a : σ -> MvPowerSeries τ S)
  axioms and operations (2):
    - const_coeff(s) : IsNilpotent (constantCoeff (a s))
    - coeff_zero(d) : {s | (a s).coeff d != 0}.Finite

中文:
结构 HasSubst
  参数: (a : σ -> MvPowerSeries τ S)
  公理与运算 (2 个):
    - const_coeff(s) : IsNilpotent (constantCoeff (a s))
    - coeff_zero(d) : {s | (a s).coeff d != 0}.Finite
-/
structure HasSubst (a : σ -> MvPowerSeries τ S) : Prop where
  const_coeff s : IsNilpotent (constantCoeff (a s))
  coeff_zero d : {s | (a s).coeff d != 0}.Finite

variable {a : σ -> MvPowerSeries τ S}

/--
lemma `coeff_zero_iff` / 引理 `coeff_zero_iff`

English:
lemma coeff_zero_iff
  given: [TopologicalSpace S] [DiscreteTopology S]
  proof: by
  simp [tendsto_iff_coeff_tendsto, coeff_zero, nhds_discrete]

中文:
引理 coeff_zero_iff
  条件: [TopologicalSpace S] [DiscreteTopology S]
  证明: by
  simp [tendsto_iff_coeff_tendsto, coeff_zero, nhds_discrete]

Depends on / 依赖: coeff_zero, nhds_discrete, tendsto_iff_coeff_tendsto
-/
lemma coeff_zero_iff [TopologicalSpace S] [DiscreteTopology S] :
    Filter.Tendsto a Filter.cofinite (nhds 0) ↔
      forall d : τ ->₀ Nat, {s | (a s).coeff d != 0}.Finite := by
  simp [tendsto_iff_coeff_tendsto, coeff_zero, nhds_discrete]

/--
lemma `hasSubst_iff_hasEval_of_discreteTopology` / 引理 `hasSubst_iff_hasEval_of_discreteTopology`

English:
lemma hasSubst_iff_hasEval_of_discreteTopology
  given: [TopologicalSpace S] [DiscreteTopology S]
  proof: by
  simp_rw [hasSubst_def, hasEval_def, coeff_zero_iff,
    isTopologicallyNilpotent_iff_constantCoeff_isNilpotent]

中文:
引理 hasSubst_iff_hasEval_of_discreteTopology
  条件: [TopologicalSpace S] [DiscreteTopology S]
  证明: by
  simp_rw [hasSubst_def, hasEval_def, coeff_zero_iff,
    isTopologicallyNilpotent_iff_constantCoeff_isNilpotent]

Depends on / 依赖: coeff_zero_iff, hasEval_def, hasSubst_def, isTopologicallyNilpotent_iff_constantCoeff_isNilpotent, simp_rw
-/
lemma hasSubst_iff_hasEval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] :
    HasSubst a ↔ HasEval a := by
  simp_rw [hasSubst_def, hasEval_def, coeff_zero_iff,
    isTopologicallyNilpotent_iff_constantCoeff_isNilpotent]

/--
theorem `HasSubst.hasEval` / 定理 `HasSubst.hasEval`

English:
theorem HasSubst.hasEval
  given: [TopologicalSpace S] (ha : HasSubst a)
  proof: HasEval.mono (instTopologicalSpace_mono τ bot_le)
  (@hasSubst_iff_hasEval_of_discreteTopology σ τ _ _ a ⊥ (@DiscreteTopology.mk S ⊥ rfl)).mp ha

中文:
定理 HasSubst.hasEval
  条件: [TopologicalSpace S] (ha : HasSubst a)
  证明: HasEval.mono (instTopologicalSpace_mono τ bot_le)
  (@hasSubst_iff_hasEval_of_discreteTopology σ τ _ _ a ⊥ (@DiscreteTopology.mk S ⊥ rfl)).mp ha

Depends on / 依赖: HasEval, HasEval.mono, bot_le, instTopologicalSpace_mono
-/
theorem HasSubst.hasEval [TopologicalSpace S] (ha : HasSubst a) :
HasEval a := HasEval.mono (instTopologicalSpace_mono τ bot_le)
  (@hasSubst_iff_hasEval_of_discreteTopology σ τ _ _ a ⊥ (@DiscreteTopology.mk S ⊥ rfl)).mp ha

/--
theorem `HasSubst.zero` / 定理 `HasSubst.zero`

English:
theorem HasSubst.zero
  statement: HasSubst (fun (_ : σ) => (0 : MvPowerSeries τ S))
  proof: by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using! HasEval.zero

中文:
定理 HasSubst.zero
  结论: HasSubst (fun (_ : σ) => (0 : MvPowerSeries τ S))
  证明: by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using! HasEval.zero

Depends on / 依赖: HasEval, HasEval.zero, UniformSpace, hasSubst_iff_hasEval_of_discreteTopology
-/
theorem HasSubst.zero : HasSubst (fun (_ : σ) => (0 : MvPowerSeries τ S)) := by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using! HasEval.zero

/--
theorem `HasSubst.add` / 定理 `HasSubst.add`

English:
theorem HasSubst.add
  given: {a b : σ -> MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b)
  proof: by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact ha.add hb

中文:
定理 HasSubst.add
  条件: {a b : σ -> MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b)
  证明: by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact ha.add hb

Depends on / 依赖: UniformSpace, ha.add, hasSubst_iff_hasEval_of_discreteTopology
-/
theorem HasSubst.add {a b : σ -> MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) := by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha hb ⊢
  exact ha.add hb

/--
theorem `HasSubst.mul_left` / 定理 `HasSubst.mul_left`

English:
theorem HasSubst.mul_left
  statement: (b : σ -> MvPowerSeries τ S)
  proof: by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact ha.mul_left b

中文:
定理 HasSubst.mul_left
  结论: (b : σ -> MvPowerSeries τ S)
  证明: by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact ha.mul_left b

Depends on / 依赖: UniformSpace, ha.mul_left, hasSubst_iff_hasEval_of_discreteTopology, mul_left
-/
theorem HasSubst.mul_left (b : σ -> MvPowerSeries τ S)
    {a : σ -> MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (b * a) := by
  let : UniformSpace S := ⊥
  rw [hasSubst_iff_hasEval_of_discreteTopology] at ha ⊢
  exact ha.mul_left b

/--
theorem `HasSubst.mul_right` / 定理 `HasSubst.mul_right`

English:
theorem HasSubst.mul_right
  statement: (b : σ -> MvPowerSeries τ S)
  proof: mul_comm a b ▸ ha.mul_left b

中文:
定理 HasSubst.mul_right
  结论: (b : σ -> MvPowerSeries τ S)
  证明: mul_comm a b ▸ ha.mul_left b

Depends on / 依赖: ha.mul_left, mul_comm, mul_left
-/
theorem HasSubst.mul_right (b : σ -> MvPowerSeries τ S)
    {a : σ -> MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (a * b) :=
  mul_comm a b ▸ ha.mul_left b

/--
theorem `HasSubst.smul` / 定理 `HasSubst.smul`

English:
theorem HasSubst.smul
  given: (r : MvPowerSeries τ S) {a : σ -> MvPowerSeries τ S} (ha : HasSubst a)
  proof: ha.mul_left _

中文:
定理 HasSubst.smul
  条件: (r : MvPowerSeries τ S) {a : σ -> MvPowerSeries τ S} (ha : HasSubst a)
  证明: ha.mul_left _

Depends on / 依赖: ha.mul_left, mul_left
-/
theorem HasSubst.smul (r : MvPowerSeries τ S) {a : σ -> MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := ha.mul_left _

/--
theorem `HasSubst.X` / 定理 `HasSubst.X`

English:
theorem HasSubst.X
  statement: HasSubst (fun (s : σ) => (X s : MvPowerSeries σ S))
  proof: by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.X

omit [Algebra R S] in

中文:
定理 HasSubst.X
  结论: HasSubst (fun (s : σ) => (X s : MvPowerSeries σ S))
  证明: by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.X

omit [Algebra R S] in
-/
protected theorem HasSubst.X : HasSubst (fun (s : σ) => (X s : MvPowerSeries σ S)) := by
  let : UniformSpace S := ⊥
  simpa [hasSubst_iff_hasEval_of_discreteTopology] using HasEval.X

omit [Algebra R S] in
/--
theorem `HasSubst.map` / 定理 `HasSubst.map`

English:
theorem HasSubst.map
  given: {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) (h : R ->+* S)
  proof: (ha.const_coeff s).map h
  coeff_zero d := (ha.coeff_zero d).subset (by grind [coeff_map])

中文:
定理 HasSubst.map
  条件: {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) (h : R ->+* S)
  证明: (ha.const_coeff s).map h
  coeff_zero d := (ha.coeff_zero d).subset (by grind [coeff_map])
-/
protected theorem HasSubst.map {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) (h : R ->+* S) :
    HasSubst fun i => (map h) (a i) where
  const_coeff s := (ha.const_coeff s).map h
  coeff_zero d := (ha.coeff_zero d).subset (by grind [coeff_map])

/--
theorem `HasSubst.smul_X` / 定理 `HasSubst.smul_X`

English:
theorem HasSubst.smul_X
  given: (a : σ -> R)
  proof: by
  convert! HasSubst.X.mul_left (fun s => algebraMap R (MvPowerSeries σ R) (a s))
  simp [funext_iff, algebra_compatible_smul (MvPowerSeries σ R)]

中文:
定理 HasSubst.smul_X
  条件: (a : σ -> R)
  证明: by
  convert! HasSubst.X.mul_left (fun s => algebraMap R (MvPowerSeries σ R) (a s))
  simp [funext_iff, algebra_compatible_smul (MvPowerSeries σ R)]

Depends on / 依赖: HasSubst, HasSubst.X.mul_left, MvPowerSeries, algebraMap, algebra_compatible_smul, convert, funext_iff, mul_left
-/
theorem HasSubst.smul_X (a : σ -> R) :
    HasSubst (a • X : σ -> MvPowerSeries σ R) := by
  convert! HasSubst.X.mul_left (fun s => algebraMap R (MvPowerSeries σ R) (a s))
  simp [funext_iff, algebra_compatible_smul (MvPowerSeries σ R)]

/--
Definition of `hasSubstIdeal` / `hasSubstIdeal` 的定义

English:
definition hasSubstIdeal
  signature: : Ideal (σ -> MvPowerSeries τ S)
  body: { carrier := Set.ofPred HasSubst
    add_mem' := HasSubst.add
    zero_mem' := HasSubst.zero
    smul_mem' := HasSubst.mul_left }

中文:
定义 hasSubstIdeal
  签名: : Ideal (σ -> MvPowerSeries τ S)
  定义体: { carrier := Set.ofPred HasSubst
    add_mem' := HasSubst.add
    zero_mem' := HasSubst.zero
    smul_mem' := HasSubst.mul_left }

Depends on / 依赖: HasSubst, HasSubst.add, HasSubst.mul_left, HasSubst.zero, Set.ofPred, add_mem, carrier, mul_left, ofPred, smul_mem, zero_mem
-/
noncomputable def hasSubstIdeal : Ideal (σ -> MvPowerSeries τ S) :=
  { carrier := Set.ofPred HasSubst
    add_mem' := HasSubst.add
    zero_mem' := HasSubst.zero
    smul_mem' := HasSubst.mul_left }

/--
theorem `hasSubst_of_constantCoeff_nilpotent` / 定理 `hasSubst_of_constantCoeff_nilpotent`

English:
theorem hasSubst_of_constantCoeff_nilpotent
  statement: [Finite σ]
  proof: ha
  coeff_zero _ := Set.toFinite _

中文:
定理 hasSubst_of_constantCoeff_nilpotent
  结论: [Finite σ]
  证明: ha
  coeff_zero _ := Set.toFinite _
-/
theorem hasSubst_of_constantCoeff_nilpotent [Finite σ]
    {a : σ -> MvPowerSeries τ S} (ha : forall s, IsNilpotent (constantCoeff (a s))) :
    HasSubst a where
  const_coeff := ha
  coeff_zero _ := Set.toFinite _

/--
theorem `hasSubst_of_constantCoeff_zero` / 定理 `hasSubst_of_constantCoeff_zero`

English:
theorem hasSubst_of_constantCoeff_zero
  statement: [Finite σ]
  proof: hasSubst_of_constantCoeff_nilpotent (fun s => by simp only [ha s, IsNilpotent.zero])

中文:
定理 hasSubst_of_constantCoeff_zero
  结论: [Finite σ]
  证明: hasSubst_of_constantCoeff_nilpotent (fun s => by simp only [ha s, IsNilpotent.zero])

Depends on / 依赖: IsNilpotent, IsNilpotent.zero, hasSubst_of_constantCoeff_nilpotent
-/
theorem hasSubst_of_constantCoeff_zero [Finite σ]
    {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s) = 0) :
    HasSubst a :=
  hasSubst_of_constantCoeff_nilpotent (fun s => by simp only [ha s, IsNilpotent.zero])

/--
lemma `HasSubst.X_X` / 引理 `HasSubst.X_X`

English:
lemma HasSubst.X_X
  given: {i j : σ}
  statement: HasSubst (S := R) ![X i, X j]
  proof: hasSubst_of_constantCoeff_zero (by simp)

中文:
引理 HasSubst.X_X
  条件: {i j : σ}
  结论: HasSubst (S := R) ![X i, X j]
  证明: hasSubst_of_constantCoeff_zero (by simp)
-/
lemma HasSubst.X_X {i j : σ} : HasSubst (S := R) ![X i, X j] :=
  hasSubst_of_constantCoeff_zero (by simp)

/--
lemma `HasSubst.X_zero` / 引理 `HasSubst.X_zero`

English:
lemma HasSubst.X_zero
  given: {i : σ}
  statement: HasSubst ![X i (R := R), 0]
  proof: hasSubst_of_constantCoeff_zero (by simp)

中文:
引理 HasSubst.X_zero
  条件: {i : σ}
  结论: HasSubst ![X i (R := R), 0]
  证明: hasSubst_of_constantCoeff_zero (by simp)
-/
lemma HasSubst.X_zero {i : σ} : HasSubst ![X i (R := R), 0] :=
  hasSubst_of_constantCoeff_zero (by simp)

/--
lemma `HasSubst.zero_X` / 引理 `HasSubst.zero_X`

English:
lemma HasSubst.zero_X
  given: {i : σ}
  statement: HasSubst ![0, X i (R := R)]
  proof: hasSubst_of_constantCoeff_zero (by simp)

中文:
引理 HasSubst.zero_X
  条件: {i : σ}
  结论: HasSubst ![0, X i (R := R)]
  证明: hasSubst_of_constantCoeff_zero (by simp)
-/
lemma HasSubst.zero_X {i : σ} : HasSubst ![0, X i (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)

/--
lemma `HasSubst.pow` / 引理 `HasSubst.pow`

English:
lemma HasSubst.pow
  given: {n : Nat} (hn : n != 0) {a : σ -> MvPowerSeries τ S} (h : HasSubst a)
  proof: hasSubstIdeal.pow_mem_of_mem h _ (by lia)

中文:
引理 HasSubst.pow
  条件: {n : 自然数} (hn : n != 0) {a : σ -> MvPowerSeries τ S} (h : HasSubst a)
  证明: hasSubstIdeal.pow_mem_of_mem h _ (by lia)
-/
protected lemma HasSubst.pow {n : Nat} (hn : n != 0) {a : σ -> MvPowerSeries τ S} (h : HasSubst a) :
    HasSubst (a ^ n) :=
  hasSubstIdeal.pow_mem_of_mem h _ (by lia)

/--
theorem `HasSubst.X_pow` / 定理 `HasSubst.X_pow`

English:
theorem HasSubst.X_pow
  given: {n : Nat} (hn : n != 0)
  proof: HasSubst.X.pow (by lia)

中文:
定理 HasSubst.X_pow
  条件: {n : 自然数} (hn : n != 0)
  证明: HasSubst.X.pow (by lia)
-/
protected theorem HasSubst.X_pow {n : Nat} (hn : n != 0) :
    HasSubst (fun (s : σ) => (X s : MvPowerSeries σ S) ^ n) :=
  HasSubst.X.pow (by lia)

/--
lemma `HasSubst.truncTotal` / 引理 `HasSubst.truncTotal`

English:
lemma HasSubst.truncTotal
  statement: {a : σ -> MvPowerSeries τ S} {x : σ -> Nat} [Finite τ]
  proof: by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]
    split_ifs <;> simp [ha.const_coeff i]
  coeff_zero d :=
    (ha.coeff_zero d).subset fun i => by contrapose; simp +contextual [coeff_truncTotal

中文:
引理 HasSubst.truncTotal
  结论: {a : σ -> MvPowerSeries τ S} {x : σ -> 自然数} [Finite τ]
  证明: by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]
    split_ifs <;> simp [ha.const_coeff i]
  coeff_zero d :=
    (ha.coeff_zero d).subset fun i => by contrapose; simp +contextual [coeff_truncTotal

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_coe, MvPolynomial.constantCoeff_eq, coeff_coe, coeff_truncTotal_eq_ite, coeff_zero, coeff_zero_eq_constantCoeff_apply, const_coeff, constantCoeff_eq, constantCoeff_truncTotal_eq_ite, contextual, contrapose, ha.coeff_zero, ha.const_coeff, split_ifs, subset
-/
lemma HasSubst.truncTotal {a : σ -> MvPowerSeries τ S} {x : σ -> Nat} [Finite τ]
    (ha : HasSubst a) : HasSubst (fun i => ((a i).truncTotal (x i)).toMvPowerSeries) where
  const_coeff i := by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]
    split_ifs <;> simp [ha.const_coeff i]
  coeff_zero d :=
    (ha.coeff_zero d).subset fun i => by contrapose; simp +contextual [coeff_truncTotal_eq_ite]

/--
Definition of `subst` / `subst` 的定义

English:
definition subst
  signature: (a : σ -> MvPowerSeries τ S) (f : MvPowerSeries σ R)
  body: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  eval₂ (algebraMap _ _) a f

中文:
定义 subst
  签名: (a : σ -> MvPowerSeries τ S) (f : MvPowerSeries σ R)
  定义体: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  eval₂ (algebraMap _ _) a f

Depends on / 依赖: UniformSpace, algebraMap
-/
noncomputable def subst (a : σ -> MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  eval₂ (algebraMap _ _) a f

/--
theorem `subst_eq_eval₂` / 定理 `subst_eq_eval₂`

English:
theorem subst_eq_eval₂
  proof: by
  ext; simp +instances [subst, DiscreteUniformity.eq_bot]

中文:
定理 subst_eq_eval₂
  证明: by
  ext; simp +instances [subst, DiscreteUniformity.eq_bot]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_bot, eq_bot, instances
-/
theorem subst_eq_eval₂
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    (subst : (σ -> MvPowerSeries τ S) -> (MvPowerSeries σ R) -> _) = eval₂ (algebraMap _ _) := by
  ext; simp +instances [subst, DiscreteUniformity.eq_bot]

/--
theorem `subst_coe` / 定理 `subst_coe`

English:
theorem subst_coe
  given: (p : MvPolynomial σ R)
  proof: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [subst_eq_eval₂]; rw [eval₂_coe]; rw [MvPolynomial.aeval_def]

中文:
定理 subst_coe
  条件: (p : MvPolynomial σ R)
  证明: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [subst_eq_eval₂]; rw [eval₂_coe]; rw [MvPolynomial.aeval_def]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, MvPolynomial.aeval_def, UniformSpace, aeval_def
-/
theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [subst_eq_eval₂]; rw [eval₂_coe]; rw [MvPolynomial.aeval_def]

variable {a : σ -> MvPowerSeries τ S}

/--
Definition of `substAlgHom` / `substAlgHom` 的定义

English:
definition substAlgHom
  signature: (ha : HasSubst a)
  body: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.aeval ha.hasEval

中文:
定义 substAlgHom
  签名: (ha : HasSubst a)
  定义体: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.aeval ha.hasEval

Depends on / 依赖: MvPowerSeries, MvPowerSeries.aeval, UniformSpace, ha.hasEval, hasEval
-/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.aeval ha.hasEval

/--
theorem `substAlgHom_eq_aeval` / 定理 `substAlgHom_eq_aeval`

English:
theorem substAlgHom_eq_aeval
  proof: by
  simp only [substAlgHom, coe_aeval ha.hasEval]
  convert! coe_aeval (R := R) (hasSubst_iff_hasEval_of_discreteTopology.mp ha) <;>
  exact DiscreteUniformity.eq_bot.symm

@[simp]

中文:
定理 substAlgHom_eq_aeval
  证明: by
  simp only [substAlgHom, coe_aeval ha.hasEval]
  convert! coe_aeval (R := R) (hasSubst_iff_hasEval_of_discreteTopology.mp ha) <;>
  exact DiscreteUniformity.eq_bot.symm

@[simp]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_bot.symm, coe_aeval, convert, eq_bot, ha.hasEval, hasEval, hasSubst_iff_hasEval_of_discreteTopology, hasSubst_iff_hasEval_of_discreteTopology.mp, substAlgHom
-/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : MvPowerSeries σ R -> MvPowerSeries τ S) = MvPowerSeries.aeval ha.hasEval := by
  simp only [substAlgHom, coe_aeval ha.hasEval]
  convert! coe_aeval (R := R) (hasSubst_iff_hasEval_of_discreteTopology.mp ha) <;>
  exact DiscreteUniformity.eq_bot.symm

@[simp]
/--
theorem `coe_substAlgHom` / 定理 `coe_substAlgHom`

English:
theorem coe_substAlgHom
  given: (ha : HasSubst a)
  proof: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [substAlgHom_eq_aeval]; rw [coe_aeval ha.hasEval]; rw [subst_eq_eval₂]

中文:
定理 coe_substAlgHom
  条件: (ha : HasSubst a)
  证明: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [substAlgHom_eq_aeval]; rw [coe_aeval ha.hasEval]; rw [subst_eq_eval₂]

Depends on / 依赖: UniformSpace, coe_aeval, ha.hasEval, hasEval, substAlgHom_eq_aeval
-/
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [substAlgHom_eq_aeval]; rw [coe_aeval ha.hasEval]; rw [subst_eq_eval₂]

/--
theorem `subst_self` / 定理 `subst_self`

English:
theorem subst_self
  statement: subst (MvPowerSeries.X : σ -> MvPowerSeries σ R) = id
  proof: by
  rw [← coe_substAlgHom HasSubst.X]
  let : UniformSpace R := ⊥
  ext1 f
  simp only [substAlgHom_eq_aeval]
  have := aeval_unique (ε := AlgHom.id R (MvPowerSeries σ R)) continuous_id
  rw [DFunLike.ext_iff] at this
  exact this f

@[simp]

中文:
定理 subst_self
  结论: subst (MvPowerSeries.X : σ -> MvPowerSeries σ R) = id
  证明: by
  rw [← coe_substAlgHom HasSubst.X]
  let : UniformSpace R := ⊥
  ext1 f
  simp only [substAlgHom_eq_aeval]
  have := aeval_unique (ε := AlgHom.id R (MvPowerSeries σ R)) continuous_id
  rw [DFunLike.ext_iff] at this
  exact this f

@[simp]

Depends on / 依赖: AlgHom, AlgHom.id, DFunLike, DFunLike.ext_iff, HasSubst, HasSubst.X, MvPowerSeries, UniformSpace, aeval_unique, coe_substAlgHom, continuous_id, ext_iff, substAlgHom_eq_aeval
-/
theorem subst_self : subst (MvPowerSeries.X : σ -> MvPowerSeries σ R) = id := by
  rw [← coe_substAlgHom HasSubst.X]
  let : UniformSpace R := ⊥
  ext1 f
  simp only [substAlgHom_eq_aeval]
  have := aeval_unique (ε := AlgHom.id R (MvPowerSeries σ R)) continuous_id
  rw [DFunLike.ext_iff] at this
  exact this f

@[simp]
/--
theorem `substAlgHom_apply` / 定理 `substAlgHom_apply`

English:
theorem substAlgHom_apply
  given: (ha : HasSubst a) (f : MvPowerSeries σ R)
  proof: by
  rw [coe_substAlgHom]

中文:
定理 substAlgHom_apply
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R)
  证明: by
  rw [coe_substAlgHom]

Depends on / 依赖: coe_substAlgHom
-/
theorem substAlgHom_apply (ha : HasSubst a) (f : MvPowerSeries σ R) :
    substAlgHom ha f = subst a f := by
  rw [coe_substAlgHom]

/--
theorem `subst_add` / 定理 `subst_add`

English:
theorem subst_add
  given: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  proof: by
  simp only [← substAlgHom_apply ha, map_add]

中文:
定理 subst_add
  条件: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  证明: by
  simp only [← substAlgHom_apply ha, map_add]

Depends on / 依赖: map_add, substAlgHom_apply
-/
theorem subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  simp only [← substAlgHom_apply ha, map_add]

/--
theorem `subst_sub` / 定理 `subst_sub`

English:
theorem subst_sub
  given: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  proof: by
  simp_rw [← substAlgHom_apply ha, map_sub]

中文:
定理 subst_sub
  条件: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  证明: by
  simp_rw [← substAlgHom_apply ha, map_sub]

Depends on / 依赖: map_sub, simp_rw, substAlgHom_apply
-/
theorem subst_sub (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f - g) = subst a f - subst a g := by
  simp_rw [← substAlgHom_apply ha, map_sub]

/--
theorem `subst_mul` / 定理 `subst_mul`

English:
theorem subst_mul
  given: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  proof: by
  simp only [← substAlgHom_apply ha, map_mul]

中文:
定理 subst_mul
  条件: (ha : HasSubst a) (f g : MvPowerSeries σ R)
  证明: by
  simp only [← substAlgHom_apply ha, map_mul]

Depends on / 依赖: map_mul, substAlgHom_apply
-/
theorem subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  simp only [← substAlgHom_apply ha, map_mul]

/--
theorem `subst_pow` / 定理 `subst_pow`

English:
theorem subst_pow
  given: (ha : HasSubst a) (f : MvPowerSeries σ R) (n : Nat)
  proof: by
  simp only [← substAlgHom_apply ha, map_pow]

中文:
定理 subst_pow
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R) (n : 自然数)
  证明: by
  simp only [← substAlgHom_apply ha, map_pow]

Depends on / 依赖: map_pow, substAlgHom_apply
-/
theorem subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : Nat) :
    subst a (f ^ n) = (subst a f) ^ n := by
  simp only [← substAlgHom_apply ha, map_pow]

/--
theorem `subst_smul` / 定理 `subst_smul`

English:
theorem subst_smul
  given: (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R)
  proof: by
  simp only [← substAlgHom_apply ha, AlgHom.map_smul_of_tower]

中文:
定理 subst_smul
  条件: (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R)
  证明: by
  simp only [← substAlgHom_apply ha, AlgHom.map_smul_of_tower]

Depends on / 依赖: AlgHom, AlgHom.map_smul_of_tower, map_smul_of_tower, substAlgHom_apply
-/
theorem subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  simp only [← substAlgHom_apply ha, AlgHom.map_smul_of_tower]

/--
theorem `substAlgHom_coe` / 定理 `substAlgHom_coe`

English:
theorem substAlgHom_coe
  given: (ha : HasSubst a) (p : MvPolynomial σ R)
  proof: by
  simp [substAlgHom]

中文:
定理 substAlgHom_coe
  条件: (ha : HasSubst a) (p : MvPolynomial σ R)
  证明: by
  simp [substAlgHom]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, substAlgHom
-/
theorem substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p := by
  simp [substAlgHom]

/--
theorem `substAlgHom_X` / 定理 `substAlgHom_X`

English:
theorem substAlgHom_X
  given: (ha : HasSubst a) (s : σ)
  proof: by
  rw [← MvPolynomial.coe_X]; rw [substAlgHom_coe ha]; rw [MvPolynomial.aeval_X]

中文:
定理 substAlgHom_X
  条件: (ha : HasSubst a) (s : σ)
  证明: by
  rw [← MvPolynomial.coe_X]; rw [substAlgHom_coe ha]; rw [MvPolynomial.aeval_X]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_X, MvPolynomial.coe_X, aeval_X, coe_X, substAlgHom_coe
-/
theorem substAlgHom_X (ha : HasSubst a) (s : σ) :
    substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X]; rw [substAlgHom_coe ha]; rw [MvPolynomial.aeval_X]

/--
theorem `substAlgHom_monomial` / 定理 `substAlgHom_monomial`

English:
theorem substAlgHom_monomial
  given: (ha : HasSubst a) (e : σ ->₀ Nat) (r : R)
  proof: by
  rw [← MvPolynomial.coe_monomial]; rw [substAlgHom_coe]; rw [MvPolynomial.aeval_monomial]

@[simp]

中文:
定理 substAlgHom_monomial
  条件: (ha : HasSubst a) (e : σ ->₀ 自然数) (r : R)
  证明: by
  rw [← MvPolynomial.coe_monomial]; rw [substAlgHom_coe]; rw [MvPolynomial.aeval_monomial]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval_monomial, MvPolynomial.coe_monomial, aeval_monomial, coe_monomial, substAlgHom_coe
-/
theorem substAlgHom_monomial (ha : HasSubst a) (e : σ ->₀ Nat) (r : R) :
    substAlgHom ha (monomial e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n => (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial]; rw [substAlgHom_coe]; rw [MvPolynomial.aeval_monomial]

@[simp]
/--
theorem `subst_C` / 定理 `subst_C`

English:
theorem subst_C
  given: (r : S)
  proof: by
  simp [subst, algebraMap_apply]

@[simp]

中文:
定理 subst_C
  条件: (r : S)
  证明: by
  simp [subst, algebraMap_apply]

@[simp]

Depends on / 依赖: algebraMap_apply
-/
theorem subst_C (r : S) :
    (C r).subst a = MvPowerSeries.C r := by
  simp [subst, algebraMap_apply]

@[simp]
/--
theorem `subst_X` / 定理 `subst_X`

English:
theorem subst_X
  given: (ha : HasSubst a) (s : σ)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

中文:
定理 subst_X
  条件: (ha : HasSubst a) (s : σ)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

Depends on / 依赖: coe_substAlgHom, substAlgHom_X
-/
theorem subst_X (ha : HasSubst a) (s : σ) :
    subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

/--
theorem `subst_monomial` / 定理 `subst_monomial`

English:
theorem subst_monomial
  given: (ha : HasSubst a) (e : σ ->₀ Nat) (r : R)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_monomial]

中文:
定理 subst_monomial
  条件: (ha : HasSubst a) (e : σ ->₀ 自然数) (r : R)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_monomial]

Depends on / 依赖: coe_substAlgHom, substAlgHom_monomial
-/
theorem subst_monomial (ha : HasSubst a) (e : σ ->₀ Nat) (r : R) :
    subst a (monomial e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n => (a s) ^ n)) := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_monomial]

/--
theorem `continuous_subst` / 定理 `continuous_subst`

English:
theorem continuous_subst
  statement: (ha : HasSubst a)
  proof: by
  rw [subst_eq_eval₂]
  exact continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

中文:
定理 continuous_subst
  结论: (ha : HasSubst a)
  证明: by
  rw [subst_eq_eval₂]
  exact continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

Depends on / 依赖: continuous_algebraMap, ha.hasEval, hasEval
-/
theorem continuous_subst (ha : HasSubst a)
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] :
    Continuous (subst a : MvPowerSeries σ R -> MvPowerSeries τ S) := by
  rw [subst_eq_eval₂]
  exact continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

/--
theorem `coeff_subst_finite` / 定理 `coeff_subst_finite`

English:
theorem coeff_subst_finite
  given: (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Nat)
  proof: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  Summable.hasFiniteSupport_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e)).summable

中文:
定理 coeff_subst_finite
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ 自然数)
  证明: letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  Summable.hasFiniteSupport_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e)).summable

Depends on / 依赖: Summable, Summable.hasFiniteSupport_of_discreteTopology, UniformSpace, continuous_coeff, ha.hasEval, hasEval, hasFiniteSupport_of_discreteTopology, hasSum_aeval, summable
-/
theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Nat) :
    (fun d => coeff d f • (coeff e (d.prod fun s e => (a s) ^ e))).HasFiniteSupport :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  Summable.hasFiniteSupport_of_discreteTopology _
    ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e)).summable

/--
theorem `coeff_subst` / 定理 `coeff_subst`

English:
theorem coeff_subst
  given: (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Nat)
  proof: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  have := ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e))
  simp [← coe_substAlgHom ha, substAlgHom, ← this.tsum_eq,
    tsum_eq_finsum (coeff_subst_finite ha f e)]

中文:
定理 coeff_subst
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ 自然数)
  证明: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  have := ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e))
  simp [← coe_substAlgHom ha, substAlgHom, ← this.tsum_eq,
    tsum_eq_finsum (coeff_subst_finite ha f e)]

Depends on / 依赖: UniformSpace, coe_substAlgHom, coeff_subst_finite, continuous_coeff, ha.hasEval, hasEval, hasSum_aeval, substAlgHom, this.tsum_eq, tsum_eq, tsum_eq_finsum
-/
theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ ->₀ Nat) :
    coeff e (subst a f) =
      finsum (fun d => coeff d f • (coeff e (d.prod fun s e => (a s) ^ e))) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  have := ((hasSum_aeval ha.hasEval f).map (coeff e) (continuous_coeff S e))
  simp [← coe_substAlgHom ha, substAlgHom, ← this.tsum_eq,
    tsum_eq_finsum (coeff_subst_finite ha f e)]

/--
theorem `constantCoeff_subst` / 定理 `constantCoeff_subst`

English:
theorem constantCoeff_subst
  given: (ha : HasSubst a) (f : MvPowerSeries σ R)
  proof: by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

中文:
定理 constantCoeff_subst
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R)
  证明: by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

Depends on / 依赖: coeff_subst, coeff_zero_eq_constantCoeff_apply
-/
theorem constantCoeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) =
      finsum (fun d => coeff d f • (constantCoeff (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

/--
theorem `constantCoeff_subst_eq_zero` / 定理 `constantCoeff_subst_eq_zero`

English:
theorem constantCoeff_subst_eq_zero
  statement: (ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0)
  proof: by
  rw [constantCoeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  · have : constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : exists i : σ, d i != 0 := by
        by_contra! hc
exact hd Finsupp.ext hc
      simpa [map_

中文:
定理 constantCoeff_subst_eq_zero
  结论: (ha : HasSubst a) (ha' : 对任意 i, (a i).constantCoeff = 0)
  证明: by
  rw [constantCoeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  · have : constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : exists i : σ, d i != 0 := by
        by_contra! hc
exact hd Finsupp.ext hc
      simpa [map_

Depends on / 依赖: Finset, Finset.prod_eq_zero, Finsupp, Finsupp.ext, constantCoeff, constantCoeff_subst, d.prod, finsum_eq_zero_of_forall_eq_zero, map_finsuppProd, prod_eq_zero, smul_zero, zero_pow
-/
theorem constantCoeff_subst_eq_zero (ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0)
    {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    MvPowerSeries.constantCoeff (subst a f) = 0 := by
  rw [constantCoeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro d
  by_cases hd : d = 0
  · simp [hd, hf]
  · have : constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      obtain ⟨i, hi⟩ : exists i : σ, d i != 0 := by
        by_contra! hc
exact hd Finsupp.ext hc
      simpa [map_finsuppProd, ha'] using!
        Finset.prod_eq_zero (i := i) (by simp [hi]) (by simp [zero_pow hi])
    rw [this]; rw [smul_zero]

/--
theorem `map_algebraMap_eq_subst_X` / 定理 `map_algebraMap_eq_subst_X`

English:
theorem map_algebraMap_eq_subst_X
  given: (f : MvPowerSeries σ R)
  proof: by
  ext e
  rw [coeff_map]; rw [coeff_subst HasSubst.X f e]; rw [finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq]; rw [coeff_monomial_ne hd.symm]; rw [sm

中文:
定理 map_algebraMap_eq_subst_X
  条件: (f : MvPowerSeries σ R)
  证明: by
  ext e
  rw [coeff_map]; rw [coeff_subst HasSubst.X f e]; rw [finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq]; rw [coeff_monomial_ne hd.symm]; rw [sm

Depends on / 依赖: HasSubst, HasSubst.X, MvPowerSeries, MvPowerSeries.monomial_one_eq, algebra_compatible_smul, coeff_map, coeff_monomial_ne, coeff_monomial_same, coeff_subst, finsum_eq_single, hd.symm, monomial_one_eq, mul_one, smul_eq_mul, smul_zero
-/
theorem map_algebraMap_eq_subst_X (f : MvPowerSeries σ R) :
    map (algebraMap R S) f = subst X f := by
  ext e
  rw [coeff_map]; rw [coeff_subst HasSubst.X f e]; rw [finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq]; rw [coeff_monomial_ne hd.symm]; rw [smul_zero]

omit [Algebra R S] in
/--
theorem `map_subst` / 定理 `map_subst`

English:
theorem map_subst
  statement: {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S}
  proof: by
  ext n
  have {r : R} : h r = h.toAddMonoidHom r := rfl
  rw [coeff_subst (ha.map h)]; rw [coeff_map]; rw [coeff_subst ha]; rw [this]; rw [AddMonoidHom.map_finsum _
    (coeff_subst_finite ha _ _)]; rw [finsum_congr]
  intro d
  simp [smul_eq_mul, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_

中文:
定理 map_subst
  结论: {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S}
  证明: by
  ext n
  have {r : R} : h r = h.toAddMonoidHom r := rfl
  rw [coeff_subst (ha.map h)]; rw [coeff_map]; rw [coeff_subst ha]; rw [this]; rw [AddMonoidHom.map_finsum _
    (coeff_subst_finite ha _ _)]; rw [finsum_congr]
  intro d
  simp [smul_eq_mul, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.map_finsum, Finsupp, Finsupp.prod, RingHom, RingHom.toAddMonoidHom_eq_coe, coe_coe, coeff_map, coeff_subst, coeff_subst_finite, finsum_congr, h.toAddMonoidHom, ha.map, map_finsum, map_mul, smul_eq_mul, toAddMonoidHom, toAddMonoidHom_eq_coe
-/
theorem map_subst {a : σ -> MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S}
    (f : MvPowerSeries σ R) :
    (f.subst a).map h = (f.map h).subst (fun i => (a i).map h) := by
  ext n
  have {r : R} : h r = h.toAddMonoidHom r := rfl
  rw [coeff_subst (ha.map h)]; rw [coeff_map]; rw [coeff_subst ha]; rw [this]; rw [AddMonoidHom.map_finsum _
    (coeff_subst_finite ha _ _)]; rw [finsum_congr]
  intro d
  simp [smul_eq_mul, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul,
    ← coeff_map, Finsupp.prod]

/--
lemma `subst_zero_eq_C_constantCoeff` / 引理 `subst_zero_eq_C_constantCoeff`

English:
lemma subst_zero_eq_C_constantCoeff
  given: {f : MvPowerSeries σ R}
  proof: by
  classical
  ext n
  rw [coeff_subst (by simp [hasSubst_def]), coeff_map, finsum_eq_single _ 0]
  · by_cases hn : n = 0
    · simp [hn, Algebra.algebraMap_eq_smul_one]
    simp [coeff_C_of_ne_zero hn, coeff_one, hn]
  intro d hd
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr

中文:
引理 subst_zero_eq_C_constantCoeff
  条件: {f : MvPowerSeries σ R}
  证明: by
  classical
  ext n
  rw [coeff_subst (by simp [hasSubst_def]), coeff_map, finsum_eq_single _ 0]
  · by_cases hn : n = 0
    · simp [hn, Algebra.algebraMap_eq_smul_one]
    simp [coeff_C_of_ne_zero hn, coeff_one, hn]
  intro d hd
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Finset, Finset.prod_eq_zero, Finsupp, Finsupp.prod, Nonempty, algebraMap_eq_smul_one, classical, coeff_C_of_ne_zero, coeff_map, coeff_one, coeff_subst, coeff_zero, d.mem_support_iff.mp, d.support.Nonempty, d.support_nonempty_iff.mpr, finsum_eq_single, hasSubst_def, mem_support_iff
-/
lemma subst_zero_eq_C_constantCoeff {f : MvPowerSeries σ R} :
    f.subst (0 : σ -> MvPowerSeries τ S) = (C f.constantCoeff).map (algebraMap R S) := by
  classical
  ext n
  rw [coeff_subst (by simp [hasSubst_def]), coeff_map, finsum_eq_single _ 0]
  · by_cases hn : n = 0
    · simp [hn, Algebra.algebraMap_eq_smul_one]
    simp [coeff_C_of_ne_zero hn, coeff_one, hn]
  intro d hd
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  simp [Finsupp.prod, Finset.prod_eq_zero hi, coeff_zero, zero_pow <| d.mem_support_iff.mp hi]

@[simp]
/--
lemma `subst_zero_of_constantCoeff_zero` / 引理 `subst_zero_of_constantCoeff_zero`

English:
lemma subst_zero_of_constantCoeff_zero
  given: {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0)
  proof: by
  simp [subst_zero_eq_C_constantCoeff, hf]

中文:
引理 subst_zero_of_constantCoeff_zero
  条件: {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0)
  证明: by
  simp [subst_zero_eq_C_constantCoeff, hf]

Depends on / 依赖: subst_zero_eq_C_constantCoeff
-/
lemma subst_zero_of_constantCoeff_zero {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) :
    f.subst (0 : σ -> MvPowerSeries τ S) = 0 := by
  simp [subst_zero_eq_C_constantCoeff, hf]

/--
lemma `HasSubst.cons_subst_zero_left` / 引理 `HasSubst.cons_subst_zero_left`

English:
lemma HasSubst.cons_subst_zero_left
  statement: {f : MvPowerSeries (Fin 2) R} (i j k : σ)
  proof: hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]

中文:
引理 HasSubst.cons_subst_zero_left
  结论: {f : MvPowerSeries (Fin 2) R} (i j k : σ)
  证明: hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]
-/
lemma HasSubst.cons_subst_zero_left {f : MvPowerSeries (Fin 2) R} (i j k : σ)
    (hF : constantCoeff f = 0) : HasSubst (![subst ![X i, X j] f, X k]) (S := R) :=
  hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]

/--
lemma `HasSubst.cons_subst_zero_right` / 引理 `HasSubst.cons_subst_zero_right`

English:
lemma HasSubst.cons_subst_zero_right
  statement: {f : MvPowerSeries (Fin 2) R} (i j k : σ)
  proof: hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]

中文:
引理 HasSubst.cons_subst_zero_right
  结论: {f : MvPowerSeries (Fin 2) R} (i j k : σ)
  证明: hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]
-/
lemma HasSubst.cons_subst_zero_right {f : MvPowerSeries (Fin 2) R} (i j k : σ)
    (hF : constantCoeff f = 0) : HasSubst ![X i, subst ![X j, X k] f] (S := R) :=
  hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp_all [constantCoeff_subst_eq_zero .X_X]

variable
    {T : Type*} [CommRing T]
    [UniformSpace T] [T2Space T] [CompleteSpace T]
    [IsUniformAddGroup T] [IsTopologicalRing T] [IsLinearTopology T T] [Algebra R T]
    {ε : MvPowerSeries τ S ->ₐ[R] T}

/--
theorem `comp_substAlgHom` / 定理 `comp_substAlgHom`

English:
theorem comp_substAlgHom
  proof: by
  ext f
  simp only [AlgHom.coe_comp, substAlgHom_eq_aeval ha]
  exact DFunLike.congr_fun (comp_aeval ha.hasEval hε) f

中文:
定理 comp_substAlgHom
  证明: by
  ext f
  simp only [AlgHom.coe_comp, substAlgHom_eq_aeval ha]
  exact DFunLike.congr_fun (comp_aeval ha.hasEval hε) f

Depends on / 依赖: AlgHom, AlgHom.coe_comp, DFunLike, DFunLike.congr_fun, coe_comp, comp_aeval, congr_fun, ha.hasEval, hasEval, substAlgHom_eq_aeval
-/
theorem comp_substAlgHom
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε.comp (substAlgHom ha) = aeval (ha.hasEval.map hε) := by
  ext f
  simp only [AlgHom.coe_comp, substAlgHom_eq_aeval ha]
  exact DFunLike.congr_fun (comp_aeval ha.hasEval hε) f

/--
theorem `comp_subst` / 定理 `comp_subst`

English:
theorem comp_subst
  statement: [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
  proof: by
  rw [← comp_substAlgHom ha hε]; rw [AlgHom.coe_comp]; rw [coe_substAlgHom]

中文:
定理 comp_subst
  结论: [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
  证明: by
  rw [← comp_substAlgHom ha hε]; rw [AlgHom.coe_comp]; rw [coe_substAlgHom]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, coe_comp, coe_substAlgHom, comp_substAlgHom, ha.hasEval.map, hasEval
-/
theorem comp_subst [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) :
    ε ∘ (subst a) = aeval (R := R) (ha.hasEval.map hε) := by
  rw [← comp_substAlgHom ha hε]; rw [AlgHom.coe_comp]; rw [coe_substAlgHom]

/--
theorem `comp_subst_apply` / 定理 `comp_subst_apply`

English:
theorem comp_subst_apply
  proof: congr_fun (comp_subst ha hε) f

中文:
定理 comp_subst_apply
  证明: congr_fun (comp_subst ha hε) f

Depends on / 依赖: ha.hasEval.map, hasEval
-/
theorem comp_subst_apply
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) (hε : Continuous ε) (f : MvPowerSeries σ R) :
    ε (subst a f) = aeval (R := R) (ha.hasEval.map hε) f :=
  congr_fun (comp_subst ha hε) f

variable [Algebra S T] [IsScalarTower R S T]

/--
theorem `eval₂_subst` / 定理 `eval₂_subst`

English:
theorem eval₂_subst
  proof: by
  let ε : MvPowerSeries τ S ->ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

中文:
定理 eval₂_subst
  证明: by
  let ε : MvPowerSeries τ S ->ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

Depends on / 依赖: AlgHom, AlgHom.coe_restrictScalars, AlgHom.toRingHom_eq_coe, Continuous, MvPowerSeries, RingHom, RingHom.coe_coe, coe_aeval, coe_coe, coe_restrictScalars, comp_subst_apply, continuous_aeval, restrictScalars, toRingHom_eq_coe
-/
theorem eval₂_subst
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) {b : τ -> T} (hb : HasEval b) (f : MvPowerSeries σ R) :
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s => eval₂ (algebraMap S T) b (a s)) f := by
  let ε : MvPowerSeries τ S ->ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

variable {υ : Type*}
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  {b : τ -> MvPowerSeries υ T}

/--
lemma `IsNilpotent_subst` / 引理 `IsNilpotent_subst`

English:
lemma IsNilpotent_subst
  statement: (ha : HasSubst a)
  proof: by
  classical
  rw [constantCoeff_subst ha]
  refine isNilpotent_finsum fun d => ?_
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simpa using IsNilpotent.map hf (algebraMap R S)
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.

中文:
引理 IsNilpotent_subst
  结论: (ha : HasSubst a)
  证明: by
  classical
  rw [constantCoeff_subst ha]
  refine isNilpotent_finsum fun d => ?_
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simpa using IsNilpotent.map hf (algebraMap R S)
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.

Depends on / 依赖: Commute, Commute.al, Commute.isNilpotent_mul_left, Finset, Finset.prod_erase_mul, Finsupp, Finsupp.prod, IsNilpotent, IsNilpotent.map, IsNilpotent.smul, Nonempty, algebraMap, algebraMap_smul, classical, constantCoeff_subst, d.support.Nonempty, d.support_nonempty_iff.mpr, isNilpotent_finsum, isNilpotent_mul_left, map_pow
-/
lemma IsNilpotent_subst (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent f.constantCoeff) :
    IsNilpotent (constantCoeff (f.subst a)) := by
  classical
  rw [constantCoeff_subst ha]
  refine isNilpotent_finsum fun d => ?_
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simpa using IsNilpotent.map hf (algebraMap R S)
  obtain ⟨i, hi⟩ : d.support.Nonempty := d.support_nonempty_iff.mpr hd
  rw [Finsupp.prod]; rw [map_prod]; rw [← Finset.prod_erase_mul _ _ hi]; rw [← algebraMap_smul S]; rw [smul_eq_mul]; rw [← mul_assoc]; rw [map_pow]
  exact Commute.isNilpotent_mul_left (Commute.all _ _)
 (IsNilpotent.pow_iff_pos (d.mem_support_iff.mp hi)).mpr (ha.const_coeff i)

/--
theorem `IsNilpotent_substAlgHom` / 定理 `IsNilpotent_substAlgHom`

English:
theorem IsNilpotent_substAlgHom
  statement: (ha : HasSubst a)
  proof: by
  simpa using IsNilpotent_subst ha hf

中文:
定理 IsNilpotent_substAlgHom
  结论: (ha : HasSubst a)
  证明: by
  simpa using IsNilpotent_subst ha hf

Depends on / 依赖: IsNilpotent_subst
-/
theorem IsNilpotent_substAlgHom (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) :
    IsNilpotent (constantCoeff (substAlgHom ha f)) := by
  simpa using IsNilpotent_subst ha hf

/--
theorem `HasSubst.comp` / 定理 `HasSubst.comp`

English:
theorem HasSubst.comp
  given: (ha : HasSubst a) (hb : HasSubst b)
  proof: IsNilpotent_substAlgHom hb (ha.const_coeff s)
  coeff_zero := by
    let : UniformSpace S := ⊥
    let : UniformSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simpa [← map_zero (substAlgHom (R := S) hb)] using! (continuous_subst hb).continuousAt

中文:
定理 HasSubst.comp
  条件: (ha : HasSubst a) (hb : HasSubst b)
  证明: IsNilpotent_substAlgHom hb (ha.const_coeff s)
  coeff_zero := by
    let : UniformSpace S := ⊥
    let : UniformSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simpa [← map_zero (substAlgHom (R := S) hb)] using! (continuous_subst hb).continuousAt

Depends on / 依赖: IsNilpotent_substAlgHom, const_coeff, ha.const_coeff
-/
theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s => substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_substAlgHom hb (ha.const_coeff s)
  coeff_zero := by
    let : UniformSpace S := ⊥
    let : UniformSpace T := ⊥
    rw [← coeff_zero_iff]
    apply Filter.Tendsto.comp _ (ha.hasEval.tendsto_zero)
    simpa [← map_zero (substAlgHom (R := S) hb)] using! (continuous_subst hb).continuousAt

/--
theorem `substAlgHom_comp_substAlgHom` / 定理 `substAlgHom_comp_substAlgHom`

English:
theorem substAlgHom_comp_substAlgHom
  given: (ha : HasSubst a) (hb : HasSubst b)
  proof: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace T := ⊥
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simpa [AlgHom.coe_restrictScalars'] using continuous_subst (R := S) hb

中文:
定理 substAlgHom_comp_substAlgHom
  条件: (ha : HasSubst a) (hb : HasSubst b)
  证明: by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace T := ⊥
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simpa [AlgHom.coe_restrictScalars'] using continuous_subst (R := S) hb

Depends on / 依赖: AlgHom, AlgHom.coe_restrictScalars, UniformSpace, coe_restrictScalars, comp_aeval, continuous_subst, ha.hasEval, hasEval, restrictScalars, substAlgHom
-/
theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace T := ⊥
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simpa [AlgHom.coe_restrictScalars'] using continuous_subst (R := S) hb

/--
theorem `substAlgHom_comp_substAlgHom_apply` / 定理 `substAlgHom_comp_substAlgHom_apply`

English:
theorem substAlgHom_comp_substAlgHom_apply
  statement: (ha : HasSubst a) (hb : HasSubst b)
  proof: DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

中文:
定理 substAlgHom_comp_substAlgHom_apply
  结论: (ha : HasSubst a) (hb : HasSubst b)
  证明: DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, substAlgHom_comp_substAlgHom
-/
theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b)
    (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

/--
theorem `subst_comp_subst` / 定理 `subst_comp_subst`

English:
theorem subst_comp_subst
  given: (ha : HasSubst a) (hb : HasSubst b)
  proof: by
  simpa [funext_iff, DFunLike.ext_iff] using substAlgHom_comp_substAlgHom (R := R) ha hb

中文:
定理 subst_comp_subst
  条件: (ha : HasSubst a) (hb : HasSubst b)
  证明: by
  simpa [funext_iff, DFunLike.ext_iff] using substAlgHom_comp_substAlgHom (R := R) ha hb

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, funext_iff, substAlgHom_comp_substAlgHom
-/
theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (fun s => subst b (a s)) := by
  simpa [funext_iff, DFunLike.ext_iff] using substAlgHom_comp_substAlgHom (R := R) ha hb

/--
theorem `subst_comp_subst_apply` / 定理 `subst_comp_subst_apply`

English:
theorem subst_comp_subst_apply
  given: (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R)
  proof: congr_fun (subst_comp_subst (R := R) ha hb) f

中文:
定理 subst_comp_subst_apply
  条件: (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R)
  证明: congr_fun (subst_comp_subst (R := R) ha hb) f

Depends on / 依赖: congr_fun, subst_comp_subst
-/
theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section

variable (w : τ -> Nat)

/--
theorem `le_weightedOrder_subst` / 定理 `le_weightedOrder_subst`

English:
theorem le_weightedOrder_subst
  given: (ha : HasSubst a) (f : MvPowerSeries σ R)
  proof: by
  apply MvPowerSeries.le_weightedOrder
  intro d hd
  rw [coeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hfx : f.coeff x = 0
  · simp [hfx]
  rw [coeff_eq_zero_of_lt_weightedOrder w]; rw [smul_zero]
  refine hd.trans_le (((biInf_le _ hfx).trans ?_).trans (le_weightedO

中文:
定理 le_weightedOrder_subst
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R)
  证明: by
  apply MvPowerSeries.le_weightedOrder
  intro d hd
  rw [coeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hfx : f.coeff x = 0
  · simp [hfx]
  rw [coeff_eq_zero_of_lt_weightedOrder w]; rw [smul_zero]
  refine hd.trans_le (((biInf_le _ hfx).trans ?_).trans (le_weightedO

Depends on / 依赖: Finset, Finset.sum_le_sum, Finsupp, Finsupp.sum, Finsupp.weight_apply, Function, Function.comp_apply, MvPowerSeries, MvPowerSeries.le_weightedOrder, biInf_le, coeff_eq_zero_of_lt_weightedOrder, coeff_subst, comp_apply, f.coeff, finsum_eq_zero_of_forall_eq_zero, hd.trans_le, le_weightedOrder, le_weightedOrder_pow, le_weightedOrder_prod, smul_zero
-/
theorem le_weightedOrder_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    ⨅ (d : σ ->₀ Nat) (_ : coeff d f != 0), d.weight (weightedOrder w ∘ a) <=
      (f.subst a).weightedOrder w := by
  apply MvPowerSeries.le_weightedOrder
  intro d hd
  rw [coeff_subst ha]; rw [finsum_eq_zero_of_forall_eq_zero]
  intro x
  by_cases hfx : f.coeff x = 0
  · simp [hfx]
  rw [coeff_eq_zero_of_lt_weightedOrder w]; rw [smul_zero]
  refine hd.trans_le (((biInf_le _ hfx).trans ?_).trans (le_weightedOrder_prod ..))
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply]
  exact Finset.sum_le_sum fun i hi => .trans (by simp) (le_weightedOrder_pow ..)

/--
theorem `le_weightedOrder_subst_of_forall_ne_zero` / 定理 `le_weightedOrder_subst_of_forall_ne_zero`

English:
theorem le_weightedOrder_subst_of_forall_ne_zero
  proof: by
  refine .trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  refine fun i hi => (weightedOrder_le _ hi).trans ?_
  simp [Finsupp.weight_apply, Finsupp.sum, (ne_zero_iff_weightedOrder_finite _).mp (ha0 _)]

中文:
定理 le_weightedOrder_subst_of_forall_ne_zero
  证明: by
  refine .trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  refine fun i hi => (weightedOrder_le _ hi).trans ?_
  simp [Finsupp.weight_apply, Finsupp.sum, (ne_zero_iff_weightedOrder_finite _).mp (ha0 _)]

Depends on / 依赖: Finsupp, Finsupp.sum, Finsupp.weight_apply, le_iInf_iff, le_weightedOrder_subst, ne_eq, ne_zero_iff_weightedOrder_finite, weight_apply, weightedOrder_le
-/
theorem le_weightedOrder_subst_of_forall_ne_zero
    (ha : HasSubst a) (ha0 : forall i, a i != 0) (f : MvPowerSeries σ R) :
    f.weightedOrder (ENat.toNat ∘ weightedOrder w ∘ a) <= (f.subst a).weightedOrder w := by
  refine .trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  refine fun i hi => (weightedOrder_le _ hi).trans ?_
  simp [Finsupp.weight_apply, Finsupp.sum, (ne_zero_iff_weightedOrder_finite _).mp (ha0 _)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `le_order_subst` / 定理 `le_order_subst`

English:
theorem le_order_subst
  given: (ha : HasSubst a) (f : MvPowerSeries σ R)
  proof: by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ ha _)
  simp only [ne_eq, le_iInf_iff]
  intro i hi
  trans (⨅ (i : σ), (order ∘ a) i) * ↑i.degree
  · refine mul_le_mul_right (order_le hi) _
  · simp only [Function.comp_apply, order, Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,

中文:
定理 le_order_subst
  条件: (ha : HasSubst a) (f : MvPowerSeries σ R)
  证明: by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ ha _)
  simp only [ne_eq, le_iInf_iff]
  intro i hi
  trans (⨅ (i : σ), (order ∘ a) i) * ↑i.degree
  · refine mul_le_mul_right (order_le hi) _
  · simp only [Function.comp_apply, order, Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_mk, Finset, Finset.mul_sum, Finset.sum_le_sum, Finsupp, Finsupp.degree, Finsupp.weight_apply, Function, Function.comp_apply, MvPowerSeries, MvPowerSeries.le_weightedOrder_subst, Nat.cast_sum, ZeroHom, ZeroHom.coe_mk, cast_sum, coe_mk, comp_apply, degree, i.degree
-/
theorem le_order_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    (⨅ i, (a i).order) * f.order <= (f.subst a).order := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ ha _)
  simp only [ne_eq, le_iInf_iff]
  intro i hi
  trans (⨅ (i : σ), (order ∘ a) i) * ↑i.degree
  · refine mul_le_mul_right (order_le hi) _
  · simp only [Function.comp_apply, order, Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Nat.cast_sum, Finset.mul_sum, Finsupp.weight_apply, nsmul_eq_mul]
    exact Finset.sum_le_sum fun j hj => by
      simp [mul_comm, mul_le_mul_right (iInf_le_iff.mpr fun _ a => a j)]

end

section truncTotal

open Finset

variable {f : MvPowerSeries σ R} [Finite τ] {x : σ -> Nat} {k : Nat}

/--
theorem `truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le` / 定理 `truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le`

English:
theorem truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
  statement: (ha : HasSubst a)
  proof: by
  classical
  ext d
  by_cases hd : d.degree < k
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, coeff_subst ha, coeff_subst, finsum_congr]
    · intro n
      simp_rw [Finsupp.prod, coeff_prod]
      congr! 3 with l hl i hi
      obtain ⟨hl₁, -⟩ := mem_finsuppAntidiag.mp hl
      have : (l

中文:
定理 truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
  结论: (ha : HasSubst a)
  证明: by
  classical
  ext d
  by_cases hd : d.degree < k
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, coeff_subst ha, coeff_subst, finsum_congr]
    · intro n
      simp_rw [Finsupp.prod, coeff_prod]
      congr! 3 with l hl i hi
      obtain ⟨hl₁, -⟩ := mem_finsuppAntidiag.mp hl
      have : (l

Depends on / 依赖: Finsupp, Finsupp.degree_mono, Finsupp.prod, classical, coeff_prod, coeff_subst, coeff_truncTotal, coeff_truncTotal_eq_zero, coeff_truncTotal_pow, d.degree, degree, degree_mono, finsum_congr, ha.truncTotal, mem_finsuppAntidiag, mem_finsuppAntidiag.mp, not_lt, not_lt.mp, simp_rw, single_le_sum_of_canonicallyOrdered
-/
theorem truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le (ha : HasSubst a)
    (hx : forall i, k <= x i) :
    (f.subst a).truncTotal k = (f.subst
      fun i => ((a i).truncTotal (x i)).toMvPowerSeries).truncTotal k := by
  classical
  ext d
  by_cases hd : d.degree < k
  · rw [coeff_truncTotal _ hd, coeff_truncTotal _ hd, coeff_subst ha, coeff_subst, finsum_congr]
    · intro n
      simp_rw [Finsupp.prod, coeff_prod]
      congr! 3 with l hl i hi
      obtain ⟨hl₁, -⟩ := mem_finsuppAntidiag.mp hl
      have : (l i).degree <= d.degree :=
        hl₁ ▸ Finsupp.degree_mono (single_le_sum_of_canonicallyOrdered hi)
      exact_mod_cast (coeff_truncTotal_pow _ (by nlinarith [hx i])).symm
    · exact ha.truncTotal
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `truncTotal_subst_eq_truncTotal_subst_sum` / 定理 `truncTotal_subst_eq_truncTotal_subst_sum`

English:
theorem truncTotal_subst_eq_truncTotal_subst_sum
  statement: (ha : HasSubst a)
  proof: by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    have h1 := coeff_subst_finite ha f d
    have h2 := coeff_subst_finite ha (∑ i in range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1]; rw [finsum_eq_sum _ h2]
    have : h2.toFinset subsete

中文:
定理 truncTotal_subst_eq_truncTotal_subst_sum
  结论: (ha : HasSubst a)
  证明: by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    have h1 := coeff_subst_finite ha f d
    have h2 := coeff_subst_finite ha (∑ i in range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1]; rw [finsum_eq_sum _ h2]
    have : h2.toFinset subsete

Depends on / 依赖: Finsupp, Finsupp.prod, coeff_homogeneousComponent, coeff_of_lt_, coeff_subst, coeff_subst_finite, coeff_truncTotal, contextual, contrapose, d.degree, degree, finsum_eq_sum, h1.toFinset, h2.toFinset, homogeneousComponent, n.degree, n.prod, simp_rw, subseteq, toFinset
-/
theorem truncTotal_subst_eq_truncTotal_subst_sum (ha : HasSubst a)
    (ha₁ : forall i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      ((∑ i in range k, (f.homogeneousComponent i)).subst a).truncTotal k := by
  ext d
  by_cases hd : d.degree < k
  · simp_rw [coeff_truncTotal _ hd, coeff_subst ha]
    have h1 := coeff_subst_finite ha f d
    have h2 := coeff_subst_finite ha (∑ i in range k, (homogeneousComponent i) f) d
    rw [finsum_eq_sum _ h1]; rw [finsum_eq_sum _ h2]
    have : h2.toFinset subseteq h1.toFinset := by simp +contextual [coeff_homogeneousComponent]
    have aux {n : σ ->₀ Nat} : coeff d (n.prod fun s e => a s ^ e) != 0 -> n.degree <= d.degree := by
      contrapose!
      intro hc
      rw [Finsupp.prod]
      refine coeff_of_lt_order (lt_of_lt_of_le (Nat.cast_lt.mpr hc)
        (.trans ?_ (le_order_prod _ n.support)))
      exact_mod_cast sum_le_sum fun i hi => le_order_pow_of_constantCoeff_eq_zero _ (ha₁ i)
    rw [← Finset.sum_subset this]
    · congr! 2 with n hn
      simp only [map_sum, coeff_homogeneousComponent, sum_ite_eq, mem_range, left_eq_ite_iff,
        not_lt]
      have : n.degree <= d.degree := by
        simp only [map_sum, Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hn
        exact aux (right_ne_zero_of_smul hn)
      grind
    · simp +contextual only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, map_sum,
        coeff_homogeneousComponent, sum_ite_eq, mem_range, ite_smul, zero_smul, ite_eq_right_iff,
        imp_false, not_lt, not_le]
      grind [right_ne_zero_of_smul]
  simp_rw [coeff_truncTotal_eq_zero _ (not_lt.mp hd)]

/--
theorem `truncTotal_subst_eq_truncTotal_sum_subst` / 定理 `truncTotal_subst_eq_truncTotal_sum_subst`

English:
theorem truncTotal_subst_eq_truncTotal_sum_subst
  statement: (ha : HasSubst a)
  proof: by
  rw [truncTotal_subst_eq_truncTotal_subst_sum ha ha₁]; rw [← substAlgHom_apply ha]; rw [map_sum]
  simp

中文:
定理 truncTotal_subst_eq_truncTotal_sum_subst
  结论: (ha : HasSubst a)
  证明: by
  rw [truncTotal_subst_eq_truncTotal_subst_sum ha ha₁]; rw [← substAlgHom_apply ha]; rw [map_sum]
  simp

Depends on / 依赖: map_sum, substAlgHom_apply, truncTotal_subst_eq_truncTotal_subst_sum
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst (ha : HasSubst a)
    (ha₁ : forall i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) =
      (∑ i in range k, (f.homogeneousComponent i).subst a).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_sum ha ha₁]; rw [← substAlgHom_apply ha]; rw [map_sum]
  simp

/--
theorem `truncTotal_subst_eq_truncTotal_truncTotal_subst` / 定理 `truncTotal_subst_eq_truncTotal_truncTotal_subst`

English:
theorem truncTotal_subst_eq_truncTotal_truncTotal_subst
  statement: [Finite σ]
  proof: by
  rw [truncTotal_subst_eq_truncTotal_subst_sum (hasSubst_of_constantCoeff_zero h) h]; rw [truncTotal_eq_sum]

中文:
定理 truncTotal_subst_eq_truncTotal_truncTotal_subst
  结论: [Finite σ]
  证明: by
  rw [truncTotal_subst_eq_truncTotal_subst_sum (hasSubst_of_constantCoeff_zero h) h]; rw [truncTotal_eq_sum]

Depends on / 依赖: hasSubst_of_constantCoeff_zero, truncTotal_eq_sum, truncTotal_subst_eq_truncTotal_subst_sum
-/
theorem truncTotal_subst_eq_truncTotal_truncTotal_subst [Finite σ]
    (h : forall i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst a).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_sum (hasSubst_of_constantCoeff_zero h) h]; rw [truncTotal_eq_sum]

/--
theorem `truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le` / 定理 `truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le`

English:
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
  statement: (ha : HasSubst a)
  proof: by
  rw [truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha hx]
  exact truncTotal_subst_eq_truncTotal_sum_subst ha.truncTotal fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]; rw [

中文:
定理 truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
  结论: (ha : HasSubst a)
  证明: by
  rw [truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha hx]
  exact truncTotal_subst_eq_truncTotal_sum_subst ha.truncTotal fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]; rw [

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_coe, MvPolynomial.constantCoeff_eq, coeff_coe, coeff_zero_eq_constantCoeff_apply, constantCoeff_eq, constantCoeff_truncTotal_eq_ite, ha.truncTotal, ite_self, truncTotal, truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le, truncTotal_subst_eq_truncTotal_sum_subst
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le (ha : HasSubst a)
    (h : forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i) :
    truncTotal k (f.subst a) = (∑ i in range k, (f.homogeneousComponent i).subst
      (fun i => ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha hx]
  exact truncTotal_subst_eq_truncTotal_sum_subst ha.truncTotal fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]; rw [MvPolynomial.coeff_coe]; rw [← MvPolynomial.constantCoeff_eq]; rw [constantCoeff_truncTotal_eq_ite]; rw [h i]; rw [ite_self]

/--
theorem `truncTotal_subst_of_le` / 定理 `truncTotal_subst_of_le`

English:
theorem truncTotal_subst_of_le
  given: [Finite σ] (h : forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i)
  proof: by
  rw [truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero h) h hx]; rw [truncTotal_eq_sum]; rw [← substAlgHom_apply
      (hasSubst_of_constantCoeff_zero h).truncTotal]; rw [map_sum]
  simp

中文:
定理 truncTotal_subst_of_le
  条件: [Finite σ] (h : 对任意 i, (a i).constantCoeff = 0) (hx : 对任意 i, k <= x i)
  证明: by
  rw [truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero h) h hx]; rw [truncTotal_eq_sum]; rw [← substAlgHom_apply
      (hasSubst_of_constantCoeff_zero h).truncTotal]; rw [map_sum]
  simp

Depends on / 依赖: hasSubst_of_constantCoeff_zero, map_sum, substAlgHom_apply, truncTotal, truncTotal_eq_sum, truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
-/
theorem truncTotal_subst_of_le [Finite σ] (h : forall i, (a i).constantCoeff = 0) (hx : forall i, k <= x i) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i => ((a i).truncTotal (x i)).toMvPowerSeries)).truncTotal k := by
  rw [truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
      (hasSubst_of_constantCoeff_zero h) h hx]; rw [truncTotal_eq_sum]; rw [← substAlgHom_apply
      (hasSubst_of_constantCoeff_zero h).truncTotal]; rw [map_sum]
  simp

/--
theorem `truncTotal_subst` / 定理 `truncTotal_subst`

English:
theorem truncTotal_subst
  given: [Finite σ] (h : forall i, (a i).constantCoeff = 0)
  proof: truncTotal_subst_of_le h fun _ => le_refl k

中文:
定理 truncTotal_subst
  条件: [Finite σ] (h : 对任意 i, (a i).constantCoeff = 0)
  证明: truncTotal_subst_of_le h fun _ => le_refl k

Depends on / 依赖: le_refl, truncTotal_subst_of_le
-/
theorem truncTotal_subst [Finite σ] (h : forall i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = ((f.truncTotal k).toMvPowerSeries.subst
      (fun i => ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_of_le h fun _ => le_refl k

/--
theorem `truncTotal_subst_eq_truncTotal_sum_subst_truncTotal` / 定理 `truncTotal_subst_eq_truncTotal_sum_subst_truncTotal`

English:
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal
  statement: (ha : HasSubst a)
  proof: truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le ha h fun _ => le_refl k

中文:
定理 truncTotal_subst_eq_truncTotal_sum_subst_truncTotal
  结论: (ha : HasSubst a)
  证明: truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le ha h fun _ => le_refl k

Depends on / 依赖: le_refl, truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le
-/
theorem truncTotal_subst_eq_truncTotal_sum_subst_truncTotal (ha : HasSubst a)
    (h : forall i, (a i).constantCoeff = 0) :
    truncTotal k (f.subst a) = (∑ i in range k, (f.homogeneousComponent i).subst
      (fun i => ((a i).truncTotal k).toMvPowerSeries)).truncTotal k :=
  truncTotal_subst_eq_truncTotal_sum_subst_truncTotal_of_le ha h fun _ => le_refl k

end truncTotal

section rescale

section CommSemiring

variable {R : Type*} [CommSemiring R]

-- To match the `PowerSeries.rescale` API which holds for `CommSemiring`,
-- we redo it by hand.

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `rescale` / `rescale` 的定义

English:
definition rescale
  signature: (a : σ -> R)
  body: fun n => (n.prod fun s m => a s ^ m) * f.coeff n
  map_zero' := by
    ext
    simp [map_zero, coeff_apply]
  map_one' := by
    ext1 n
    classical
    simp only [coeff_one, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h, coeff_apply]
    · simp only [coeff_apply, ite_eq_right_iff]

中文:
定义 rescale
  签名: (a : σ -> R)
  定义体: fun n => (n.prod fun s m => a s ^ m) * f.coeff n
  map_zero' := by
    ext
    simp [map_zero, coeff_apply]
  map_one' := by
    ext1 n
    classical
    simp only [coeff_one, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h, coeff_apply]
    · simp only [coeff_apply, ite_eq_right_iff]

Depends on / 依赖: f.coeff, n.prod
-/
noncomputable def rescale (a : σ -> R) : MvPowerSeries σ R ->+* MvPowerSeries σ R where
  toFun f := fun n => (n.prod fun s m => a s ^ m) * f.coeff n
  map_zero' := by
    ext
    simp [map_zero, coeff_apply]
  map_one' := by
    ext1 n
    classical
    simp only [coeff_one, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h, coeff_apply]
    · simp only [coeff_apply, ite_eq_right_iff]
      exact fun a_1 => False.elim (h a_1)
  map_add' := by
    intros
    ext
    exact mul_add _ _ _
  map_mul' f g := by
    ext n
    classical
    rw [coeff_apply]; rw [coeff_mul]; rw [coeff_mul]; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_antidiagonal] at hx
    rw [← hx]
    simp only [coeff_apply]
    rw [Finsupp.prod_of_support_subset _ Finsupp.support_add]; rw [Finsupp.prod_of_support_subset x.1 Finset.subset_union_left]; rw [Finsupp.prod_of_support_subset x.2 Finset.subset_union_right]
    · simp only [← mul_assoc]
      congr 1
      rw [mul_assoc]; rw [mul_comm (f x.1)]; rw [← mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      simp [pow_add]
    all_goals {simp}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `coeff_rescale` / 定理 `coeff_rescale`

English:
theorem coeff_rescale
  given: (f : MvPowerSeries σ R) (a : σ -> R) (n : σ ->₀ Nat)
  proof: by
  simp [rescale, coeff_apply]

中文:
定理 coeff_rescale
  条件: (f : MvPowerSeries σ R) (a : σ -> R) (n : σ ->₀ 自然数)
  证明: by
  simp [rescale, coeff_apply]

Depends on / 依赖: coeff_apply, rescale
-/
theorem coeff_rescale (f : MvPowerSeries σ R) (a : σ -> R) (n : σ ->₀ Nat) :
    coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * f.coeff n := by
  simp [rescale, coeff_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `rescale_zero` / 定理 `rescale_zero`

English:
theorem rescale_zero
  proof: by
  classical
  ext x n
  simp only [rescale, Pi.zero_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    RingHom.coe_comp, Function.comp_apply, coeff_C]
  split_ifs with h
  · simp [h, coeff_apply, ← @coeff_zero_eq_constantCoeff_apply, coeff_apply]
  · simp only [coeff_apply]
    convert! 

中文:
定理 rescale_zero
  证明: by
  classical
  ext x n
  simp only [rescale, Pi.zero_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    RingHom.coe_comp, Function.comp_apply, coeff_C]
  split_ifs with h
  · simp [h, coeff_apply, ← @coeff_zero_eq_constantCoeff_apply, coeff_apply]
  · simp only [coeff_apply]
    convert! 

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Finset, Finset.prod_eq_zero, Finsupp, Finsupp.coe_zero, Finsupp.prod, Function, Function.comp_apply, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, Pi.zero_apply, RingHom, RingHom.coe_comp, RingHom.coe_mk, classical, coe_comp, coe_mk
-/
theorem rescale_zero :
    (rescale 0 : MvPowerSeries σ R ->+* MvPowerSeries σ R) = C.comp constantCoeff := by
  classical
  ext x n
  simp only [rescale, Pi.zero_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    RingHom.coe_comp, Function.comp_apply, coeff_C]
  split_ifs with h
  · simp [h, coeff_apply, ← @coeff_zero_eq_constantCoeff_apply, coeff_apply]
  · simp only [coeff_apply]
    convert! zero_mul _
    simp only [DFunLike.ext_iff, not_forall, Finsupp.coe_zero, Pi.zero_apply] at h
    obtain ⟨s, h⟩ := h
    simp only [Finsupp.prod]
    apply Finset.prod_eq_zero (i := s) _ (zero_pow h)
    simpa using h

/--
theorem `rescale_zero_apply` / 定理 `rescale_zero_apply`

English:
theorem rescale_zero_apply
  given: (f : MvPowerSeries σ R)
  proof: by simp

@[simp]

中文:
定理 rescale_zero_apply
  条件: (f : MvPowerSeries σ R)
  证明: by simp

@[simp]
-/
theorem rescale_zero_apply (f : MvPowerSeries σ R) :
    rescale 0 f = C (constantCoeff f) := by simp

@[simp]
/--
theorem `rescale_one` / 定理 `rescale_one`

English:
theorem rescale_one
  statement: rescale 1 = RingHom.id (MvPowerSeries σ R)
  proof: by
  ext f n
  simp [coeff_rescale, Finsupp.prod]

中文:
定理 rescale_one
  结论: rescale 1 = RingHom.id (MvPowerSeries σ R)
  证明: by
  ext f n
  simp [coeff_rescale, Finsupp.prod]

Depends on / 依赖: Finsupp, Finsupp.prod, coeff_rescale
-/
theorem rescale_one : rescale 1 = RingHom.id (MvPowerSeries σ R) := by
  ext f n
  simp [coeff_rescale, Finsupp.prod]

/--
theorem `rescale_rescale` / 定理 `rescale_rescale`

English:
theorem rescale_rescale
  given: (f : MvPowerSeries σ R) (a b : σ -> R)
  proof: by
  ext n
  simp [← mul_assoc, mul_pow, mul_comm]

中文:
定理 rescale_rescale
  条件: (f : MvPowerSeries σ R) (a b : σ -> R)
  证明: by
  ext n
  simp [← mul_assoc, mul_pow, mul_comm]

Depends on / 依赖: mul_assoc, mul_comm, mul_pow
-/
theorem rescale_rescale (f : MvPowerSeries σ R) (a b : σ -> R) :
    rescale b (rescale a f) = rescale (a * b) f := by
  ext n
  simp [← mul_assoc, mul_pow, mul_comm]

/--
theorem `rescale_mul` / 定理 `rescale_mul`

English:
theorem rescale_mul
  given: (a b : σ -> R)
  statement: rescale (a * b) = (rescale b).comp (rescale a)
  proof: by
  ext
  simp [← rescale_rescale]

中文:
定理 rescale_mul
  条件: (a b : σ -> R)
  结论: rescale (a * b) = (rescale b).comp (rescale a)
  证明: by
  ext
  simp [← rescale_rescale]

Depends on / 依赖: rescale_rescale
-/
theorem rescale_mul (a b : σ -> R) : rescale (a * b) = (rescale b).comp (rescale a) := by
  ext
  simp [← rescale_rescale]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `rescale_homogeneous_eq_smul` / 引理 `rescale_homogeneous_eq_smul`

English:
lemma rescale_homogeneous_eq_smul
  statement: {n : Nat} {r : R} {f : MvPowerSeries σ R}
  proof: by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul, Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : e in f.support
  · rw [← hf e he, Finsupp.degree_apply]
  · simp only [Function.mem_support, ne_eq, not_not] at he
    simp [he, mul_zero, c

中文:
引理 rescale_homogeneous_eq_smul
  结论: {n : 自然数} {r : R} {f : MvPowerSeries σ R}
  证明: by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul, Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : e in f.support
  · rw [← hf e he, Finsupp.degree_apply]
  · simp only [Function.mem_support, ne_eq, not_not] at he
    simp [he, mul_zero, c

Depends on / 依赖: Finset, Finset.prod_pow_eq_pow_sum, Finsupp, Finsupp.degree_apply, Finsupp.prod, Function, Function.const_apply, Function.mem_support, MvPowerSeries, MvPowerSeries.coeff_rescale, coeff_apply, coeff_rescale, const_apply, degree_apply, f.support, map_smul, mem_support, mul_zero, ne_eq, not_not
-/
lemma rescale_homogeneous_eq_smul {n : Nat} {r : R} {f : MvPowerSeries σ R}
    (hf : forall d in f.support, d.degree = n) :
    MvPowerSeries.rescale (Function.const σ r) f = r ^ n • f := by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul, Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : e in f.support
  · rw [← hf e he, Finsupp.degree_apply]
  · simp only [Function.mem_support, ne_eq, not_not] at he
    simp [he, mul_zero, coeff_apply]

/--
Definition of `rescaleMonoidHom` / `rescaleMonoidHom` 的定义

English:
definition rescaleMonoidHom
  signature: :
  body: rescale
  map_one' := rescale_one
  map_mul' a b := by ext; simp [mul_comm, rescale_rescale]

中文:
定义 rescaleMonoidHom
  签名: :
  定义体: rescale
  map_one' := rescale_one
  map_mul' a b := by ext; simp [mul_comm, rescale_rescale]

Depends on / 依赖: IsUniformGroup, IsUniformGroup.of_compactSpace, UniformSpace, of_compactSpace, rescale
-/
noncomputable def rescaleMonoidHom :
    (σ -> R) ->* MvPowerSeries σ R ->+* MvPowerSeries σ R where
  toFun := rescale
  map_one' := rescale_one
  map_mul' a b := by ext; simp [mul_comm, rescale_rescale]

end CommSemiring

section CommRing

/--
theorem `rescale_eq_subst` / 定理 `rescale_eq_subst`

English:
theorem rescale_eq_subst
  given: (a : σ -> R) (f : MvPowerSeries σ R)
  proof: by
  classical
  ext n
  rw [coeff_rescale]
  rw [coeff_subst (HasSubst.smul_X a)]; rw [finsum_eq_sum _ (coeff_subst_finite (HasSubst.smul_X a) f n)]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [Finset.sum_eq_single n _ _]
  · simp [mul_comm, ← monomial_eq]
  · intro b hb hbn
    rw [← monomial_e

中文:
定理 rescale_eq_subst
  条件: (a : σ -> R) (f : MvPowerSeries σ R)
  证明: by
  classical
  ext n
  rw [coeff_rescale]
  rw [coeff_subst (HasSubst.smul_X a)]; rw [finsum_eq_sum _ (coeff_subst_finite (HasSubst.smul_X a) f n)]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [Finset.sum_eq_single n _ _]
  · simp [mul_comm, ← monomial_eq]
  · intro b hb hbn
    rw [← monomial_e

Depends on / 依赖: Finset, Finset.sum_eq_single, HasSubst, HasSubst.smul_X, Ne.symm, Pi.smul_apply, classical, coeff_monomial, coeff_rescale, coeff_subst, coeff_subst_finite, finsum_eq_sum, if_neg, monomial_eq, mul_comm, mul_zero, smul_X, smul_apply, smul_eq_mul, sum_eq_single
-/
theorem rescale_eq_subst (a : σ -> R) (f : MvPowerSeries σ R) :
    rescale a f = subst (a • X) f := by
  classical
  ext n
  rw [coeff_rescale]
  rw [coeff_subst (HasSubst.smul_X a)]; rw [finsum_eq_sum _ (coeff_subst_finite (HasSubst.smul_X a) f n)]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [Finset.sum_eq_single n _ _]
  · simp [mul_comm, ← monomial_eq]
  · intro b hb hbn
    rw [← monomial_eq]; rw [coeff_monomial]; rw [if_neg (Ne.symm hbn)]; rw [mul_zero]
  · intro hn
    simpa using hn

/--
Definition of `rescaleAlgHom` / `rescaleAlgHom` 的定义

English:
definition rescaleAlgHom
  signature: (a : σ -> R)
  body: substAlgHom (HasSubst.smul_X a)

中文:
定义 rescaleAlgHom
  签名: (a : σ -> R)
  定义体: substAlgHom (HasSubst.smul_X a)

Depends on / 依赖: HasSubst, HasSubst.smul_X, smul_X, substAlgHom
-/
noncomputable def rescaleAlgHom (a : σ -> R) :
    MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.smul_X a)

/--
theorem `rescaleAlgHom_apply` / 定理 `rescaleAlgHom_apply`

English:
theorem rescaleAlgHom_apply
  given: (a : σ -> R) (f : MvPowerSeries σ R)
  proof: by
  simp [rescaleAlgHom, rescale_eq_subst]

中文:
定理 rescaleAlgHom_apply
  条件: (a : σ -> R) (f : MvPowerSeries σ R)
  证明: by
  simp [rescaleAlgHom, rescale_eq_subst]

Depends on / 依赖: rescaleAlgHom, rescale_eq_subst
-/
theorem rescaleAlgHom_apply (a : σ -> R) (f : MvPowerSeries σ R) :
    rescaleAlgHom a f = rescale a f := by
  simp [rescaleAlgHom, rescale_eq_subst]

/--
theorem `rescaleAlgHom_mul` / 定理 `rescaleAlgHom_mul`

English:
theorem rescaleAlgHom_mul
  given: (a b : σ -> R)
  proof: by
  ext1 f
  simp [rescaleAlgHom_apply, rescale_rescale]

中文:
定理 rescaleAlgHom_mul
  条件: (a b : σ -> R)
  证明: by
  ext1 f
  simp [rescaleAlgHom_apply, rescale_rescale]

Depends on / 依赖: rescaleAlgHom_apply, rescale_rescale
-/
theorem rescaleAlgHom_mul (a b : σ -> R) :
    rescaleAlgHom (a * b) = (rescaleAlgHom b).comp (rescaleAlgHom a) := by
  ext1 f
  simp [rescaleAlgHom_apply, rescale_rescale]

/--
theorem `rescaleAlgHom_one` / 定理 `rescaleAlgHom_one`

English:
theorem rescaleAlgHom_one
  proof: by
  ext1 f
  simp [rescaleAlgHom, subst_self]

中文:
定理 rescaleAlgHom_one
  证明: by
  ext1 f
  simp [rescaleAlgHom, subst_self]

Depends on / 依赖: rescaleAlgHom, subst_self
-/
theorem rescaleAlgHom_one :
    rescaleAlgHom 1 = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 f
  simp [rescaleAlgHom, subst_self]

end CommRing

end rescale

section

variable {x : Nat -> MvPowerSeries σ R}
  [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/--
lemma `subst_tsum` / 引理 `subst_tsum`

English:
lemma subst_tsum
  given: (hx : Summable x) (ha : HasSubst a)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _ <| continuous_aeval _]

中文:
引理 subst_tsum
  条件: (hx : Summable x) (ha : HasSubst a)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _ <| continuous_aeval _]

Depends on / 依赖: coe_substAlgHom, continuous_aeval, hx.map_tsum, map_tsum, substAlgHom_eq_aeval
-/
lemma subst_tsum (hx : Summable x) (ha : HasSubst a) :
    (∑' i, x i).subst a = ∑' i, ((x i).subst a) := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _ <| continuous_aeval _]

/--
lemma `summable_subst` / 引理 `summable_subst`

English:
lemma summable_subst
  given: (hx : Summable x) (ha : HasSubst a)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
exact hx.map _ continuous_aeval ha.hasEval

中文:
引理 summable_subst
  条件: (hx : Summable x) (ha : HasSubst a)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
exact hx.map _ continuous_aeval ha.hasEval

Depends on / 依赖: coe_substAlgHom, continuous_aeval, ha.hasEval, hasEval, hx.map, substAlgHom_eq_aeval
-/
lemma summable_subst (hx : Summable x) (ha : HasSubst a) :
    Summable fun i => (x i).subst a := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
exact hx.map _ continuous_aeval ha.hasEval

end

end MvPowerSeries
