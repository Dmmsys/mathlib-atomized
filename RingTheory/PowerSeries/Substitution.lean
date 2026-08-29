/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

Because of the special API for `PowerSeries`, some results for `MvPowerSeries`
do not immediately apply and a “primed” version is provided here.

-/

@[expose] public section

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/--
Definition of `HasSubst` / `HasSubst` 的定义

English:
abbreviation HasSubst
  signature: (a : MvPowerSeries τ S)
  body: IsNilpotent (MvPowerSeries.constantCoeff a)

中文:
缩写 有Subst
  签名: (a : MvPowerSeries τ S)
  定义体: IsNilpotent (MvPowerSeries.constantCoeff a)

Depends on / 依赖: IsNilpotent, MvPowerSeries, MvPowerSeries.constantCoeff, constantCoeff
-/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff a)

/--
theorem `hasSubst_iff` / 定理 `hasSubst_iff`

English:
theorem hasSubst_iff
  given: {a : MvPowerSeries τ S}
  proof: ⟨fun ha => MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha => (ha.const_coeff ())⟩

中文:
定理 hasSubst_iff
  条件: {a : MvPowerSeries τ S}
  证明: ⟨fun ha => MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha => (ha.const_coeff ())⟩

Depends on / 依赖: Function, Function.const, MvPowerSeries, MvPowerSeries.hasSubst_of_constantCoeff_nilpotent, const_coeff, ha.const_coeff, hasSubst_of_constantCoeff_nilpotent
-/
theorem hasSubst_iff {a : MvPowerSeries τ S} :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha => MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha => (ha.const_coeff ())⟩

/--
theorem `HasSubst.const` / 定理 `HasSubst.const`

English:
theorem HasSubst.const
  given: {a : MvPowerSeries τ S} (ha : HasSubst a)
  proof: hasSubst_iff.mp ha

中文:
定理 有Subst.const
  条件: {a : MvPowerSeries τ S} (ha : 有Subst a)
  证明: hasSubst_iff.mp ha

Depends on / 依赖: hasSubst_iff, hasSubst_iff.mp
-/
theorem HasSubst.const {a : MvPowerSeries τ S} (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () => a) :=
  hasSubst_iff.mp ha

/--
theorem `hasSubst_iff_hasEval_of_discreteTopology` / 定理 `hasSubst_iff_hasEval_of_discreteTopology`

English:
theorem hasSubst_iff_hasEval_of_discreteTopology
  proof: by
  rw [hasSubst_iff]; rw [MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology]; rw [hasEval_iff]; rw [Function.const_def]

中文:
定理 hasSubst_iff_hasEval_of_discreteTopology
  证明: by
  rw [hasSubst_iff]; rw [MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology]; rw [hasEval_iff]; rw [Function.const_def]

Depends on / 依赖: Function, Function.const_def, MvPowerSeries, MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology, const_def, hasEval_iff, hasSubst_iff, hasSubst_iff_hasEval_of_discreteTopology
-/
theorem hasSubst_iff_hasEval_of_discreteTopology
    [TopologicalSpace S] [DiscreteTopology S] {a : MvPowerSeries τ S} :
    HasSubst a ↔ PowerSeries.HasEval a := by
  rw [hasSubst_iff]; rw [MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology]; rw [hasEval_iff]; rw [Function.const_def]

/--
theorem `HasSubst.hasEval` / 定理 `HasSubst.hasEval`

English:
theorem HasSubst.hasEval
  given: [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a)
  proof: isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha

中文:
定理 有Subst.hasEval
  条件: [拓扑空间 S] {a : MvPowerSeries τ S} (ha : 有Subst a)
  证明: isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha
-/
theorem HasSubst.hasEval [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasEval a := isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha

/--
theorem `HasSubst.of_constantCoeff_zero` / 定理 `HasSubst.of_constantCoeff_zero`

English:
theorem HasSubst.of_constantCoeff_zero
  statement: {a : MvPowerSeries τ S}
  proof: by
  simp [HasSubst, ha]

中文:
定理 有Subst.of_constantCoeff_zero
  结论: {a : MvPowerSeries τ S}
  证明: by
  simp [HasSubst, ha]

Depends on / 依赖: HasSubst
-/
theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) : HasSubst a := by
  simp [HasSubst, ha]

/--
theorem `HasSubst.of_constantCoeff_zero'` / 定理 `HasSubst.of_constantCoeff_zero'`

English:
theorem HasSubst.of_constantCoeff_zero'
  statement: {a : PowerSeries S}
  proof: HasSubst.of_constantCoeff_zero ha

中文:
定理 有Subst.of_constantCoeff_zero'
  结论: {a : 幂级数 S}
  证明: HasSubst.of_constantCoeff_zero ha

Depends on / 依赖: HasSubst, HasSubst.of_constantCoeff_zero, of_constantCoeff_zero
-/
theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff a = 0) : HasSubst a :=
  HasSubst.of_constantCoeff_zero ha

/--
theorem `HasSubst.X` / 定理 `HasSubst.X`

English:
theorem HasSubst.X
  given: (t : τ)
  proof: by
  simp [HasSubst]

中文:
定理 有Subst.X
  条件: (t : τ)
  证明: by
  simp [HasSubst]
-/
protected theorem HasSubst.X (t : τ) :
    HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

/--
theorem `HasSubst.X'` / 定理 `HasSubst.X'`

English:
theorem HasSubst.X'
  statement: HasSubst (X : R⟦X⟧)
  proof: HasSubst.X _

中文:
定理 有Subst.X'
  结论: 有Subst (X : R⟦X⟧)
  证明: HasSubst.X _
-/
protected theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X _

/--
theorem `HasSubst.X_pow` / 定理 `HasSubst.X_pow`

English:
theorem HasSubst.X_pow
  given: {n : Nat} (hn : n != 0)
  statement: HasSubst (X ^ n : R⟦X⟧)
  proof: HasSubst.of_constantCoeff_zero' (by simp [hn])

中文:
定理 有Subst.X_pow
  条件: {n : 自然数} (hn : n != 0)
  结论: 有Subst (X ^ n : R⟦X⟧)
  证明: HasSubst.of_constantCoeff_zero' (by simp [hn])
-/
protected theorem HasSubst.X_pow {n : Nat} (hn : n != 0) : HasSubst (X ^ n : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])

/--
theorem `HasSubst.monomial` / 定理 `HasSubst.monomial`

English:
theorem HasSubst.monomial
  given: {n : τ ->₀ Nat} (hn : n != 0) (s : S)
  proof: by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff]; rw [MvPowerSeries.coeff_monomial]; rw [if_neg hn.symm]

中文:
定理 有Subst.monomial
  条件: {n : τ ->₀ 自然数} (hn : n != 0) (s : S)
  证明: by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff]; rw [MvPowerSeries.coeff_monomial]; rw [if_neg hn.symm]
-/
protected theorem HasSubst.monomial {n : τ ->₀ Nat} (hn : n != 0) (s : S) :
    HasSubst (MvPowerSeries.monomial n s) := by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff]; rw [MvPowerSeries.coeff_monomial]; rw [if_neg hn.symm]

/--
theorem `HasSubst.monomial'` / 定理 `HasSubst.monomial'`

English:
theorem HasSubst.monomial'
  given: {n : Nat} (hn : n != 0) (s : S)
  proof: HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s

中文:
定理 有Subst.monomial'
  条件: {n : 自然数} (hn : n != 0) (s : S)
  证明: HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s
-/
protected theorem HasSubst.monomial' {n : Nat} (hn : n != 0) (s : S) :
    HasSubst (monomial n s) :=
  HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s

/--
theorem `HasSubst.zero` / 定理 `HasSubst.zero`

English:
theorem HasSubst.zero
  statement: HasSubst (0 : MvPowerSeries τ R)
  proof: by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

中文:
定理 有Subst.zero
  结论: 有Subst (0 : MvPowerSeries τ R)
  证明: by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero
-/
theorem HasSubst.zero : HasSubst (0 : MvPowerSeries τ R) := by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

/--
theorem `HasSubst.zero'` / 定理 `HasSubst.zero'`

English:
theorem HasSubst.zero'
  statement: HasSubst (0 : PowerSeries R)
  proof: PowerSeries.HasSubst.zero

中文:
定理 有Subst.zero'
  结论: 有Subst (0 : 幂级数 R)
  证明: PowerSeries.HasSubst.zero

Depends on / 依赖: HasSubst, PowerSeries, PowerSeries.HasSubst.zero
-/
theorem HasSubst.zero' : HasSubst (0 : PowerSeries R) :=
  PowerSeries.HasSubst.zero

variable {f g : MvPowerSeries τ R}

/--
theorem `HasSubst.add` / 定理 `HasSubst.add`

English:
theorem HasSubst.add
  given: (hf : HasSubst f) (hg : HasSubst g)
  proof: (Commute.all _ _).isNilpotent_add hf hg

中文:
定理 有Subst.add
  条件: (hf : 有Subst f) (hg : 有Subst g)
  证明: (Commute.all _ _).isNilpotent_add hf hg
-/
theorem HasSubst.add (hf : HasSubst f) (hg : HasSubst g) :
    HasSubst (f + g) :=
  (Commute.all _ _).isNilpotent_add hf hg


/--
theorem `HasSubst.mul_left` / 定理 `HasSubst.mul_left`

English:
theorem HasSubst.mul_left
  given: (hf : HasSubst f)
  proof: by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf

中文:
定理 有Subst.mul_left
  条件: (hf : 有Subst f)
  证明: by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf
-/
theorem HasSubst.mul_left (hf : HasSubst f) :
    HasSubst (f * g) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf

/--
theorem `HasSubst.mul_right` / 定理 `HasSubst.mul_right`

English:
theorem HasSubst.mul_right
  given: (hf : HasSubst f)
  proof: by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf

中文:
定理 有Subst.mul_right
  条件: (hf : 有Subst f)
  证明: by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf
-/
theorem HasSubst.mul_right (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf

/--
theorem `HasSubst.smul` / 定理 `HasSubst.smul`

English:
theorem HasSubst.smul
  given: (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a)
  proof: ha.mul_right

中文:
定理 有Subst.smul
  条件: (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : 有Subst a)
  证明: ha.mul_right
-/
theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) :=
  ha.mul_right

/--
Definition of `HasSubst.ideal` / `HasSubst.ideal` 的定义

English:
definition HasSubst.ideal
  signature: : Ideal (MvPowerSeries τ S) where
  body: Set.ofPred HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

中文:
定义 有Subst.ideal
  签名: : 理想 (MvPowerSeries τ S) where
  定义体: Set.ofPred HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

Depends on / 依赖: HasSubst, Set.ofPred, ofPred
-/
noncomputable def HasSubst.ideal : Ideal (MvPowerSeries τ S) where
  carrier := Set.ofPred HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

/--
theorem `HasSubst.smul'` / 定理 `HasSubst.smul'`

English:
theorem HasSubst.smul'
  given: (a : A) (hf : HasSubst f)
  proof: by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

中文:
定理 有Subst.smul'
  条件: (a : A) (hf : 有Subst f)
  证明: by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

Depends on / 依赖: HasSubst, IsNilpotent, IsNilpotent.smul, MvPowerSeries, MvPowerSeries.constantCoeff_smul, constantCoeff_smul
-/
theorem HasSubst.smul' (a : A) (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _

/--
theorem `HasSubst.smul_X` / 定理 `HasSubst.smul_X`

English:
theorem HasSubst.smul_X
  given: (a : A) (t : τ)
  proof: (HasSubst.X t).smul' _

中文:
定理 有Subst.smul_X
  条件: (a : A) (t : τ)
  证明: (HasSubst.X t).smul' _
-/
theorem HasSubst.smul_X (a : A) (t : τ) :
    HasSubst (a • (MvPowerSeries.X t) : MvPowerSeries τ R) :=
  (HasSubst.X t).smul' _

/--
theorem `HasSubst.smul_X'` / 定理 `HasSubst.smul_X'`

English:
theorem HasSubst.smul_X'
  given: (a : A)
  statement: HasSubst (a • X : R⟦X⟧)
  proof: HasSubst.X'.smul' _

中文:
定理 有Subst.smul_X'
  条件: (a : A)
  结论: 有Subst (a • X : R⟦X⟧)
  证明: HasSubst.X'.smul' _

Depends on / 依赖: HasSubst, HasSubst.X
-/
theorem HasSubst.smul_X' (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X'.smul' _

/--
lemma `HasSubst.eventually_coeff_pow_eq_zero` / 引理 `HasSubst.eventually_coeff_pow_eq_zero`

English:
lemma HasSubst.eventually_coeff_pow_eq_zero
  given: {f : A⟦X⟧} (hf : HasSubst f) (n : Nat)
  proof: by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' =>
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by r

中文:
引理 有Subst.eventually_coeff_pow_eq_zero
  条件: {f : A⟦X⟧} (hf : 有Subst f) (n : 自然数)
  证明: by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' =>
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by r

Depends on / 依赖: Filter, Filter.Ici_mem_atTop, Filter.eventually_of_mem, Ici_mem_atTop, Nat.cast_lt, Set.mem_Ici.mp, _root_, _root_.le_add_right, cast_lt, coeff_of_lt_order, eventually_of_mem, le_add_right, le_iff_exists_add, le_iff_exists_add.mp, le_order_pow_of_constantCoeff_eq_zero, le_rfl, map_pow, mem_Ici, order_mul_ge, pow_add
-/
lemma HasSubst.eventually_coeff_pow_eq_zero {f : A⟦X⟧} (hf : HasSubst f) (n : Nat) :
    forallᶠ m in .atTop, forall n' <= n, coeff n' (f ^ m) = 0 := by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' =>
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by rwa [map_pow]), ← _root_.le_add_right le_rfl, Nat.cast_lt]
  lia

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

/--
Definition of `subst` / `subst` 的定义

English:
definition subst
  signature: (a : MvPowerSeries τ S) (f : PowerSeries R)
  body: MvPowerSeries.subst (fun _ => a) f

中文:
定义 subst
  签名: (a : MvPowerSeries τ S) (f : 幂级数 R)
  定义体: MvPowerSeries.subst (fun _ => a) f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.subst, SecondCountableTopology, TotallyDisconnectedSpace
-/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ => a) f

/--
lemma `subst_def` / 引理 `subst_def`

English:
lemma subst_def
  given: (a : MvPowerSeries τ S) (f : PowerSeries R)
  proof: rfl

中文:
引理 subst_def
  条件: (a : MvPowerSeries τ S) (f : 幂级数 R)
  证明: rfl
-/
lemma subst_def (a : MvPowerSeries τ S) (f : PowerSeries R) :
    subst a f = MvPowerSeries.subst (fun _ => a) f := rfl

/--
lemma `subst_X_comp_const` / 引理 `subst_X_comp_const`

English:
lemma subst_X_comp_const
  given: {f : R⟦X⟧} {i : τ}
  proof: rfl

中文:
引理 subst_X_comp_const
  条件: {f : R⟦X⟧} {i : τ}
  证明: rfl

Depends on / 依赖: f.subst
-/
lemma subst_X_comp_const {f : R⟦X⟧} {i : τ} :
    .subst (.X (R := R) ∘ fun _ => i) f = f.subst (.X i) := rfl

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

/--
Definition of `substAlgHom` / `substAlgHom` 的定义

English:
definition substAlgHom
  signature: (ha : HasSubst a)
  body: MvPowerSeries.substAlgHom ha.const

中文:
定义 substAlgHom
  签名: (ha : 有Subst a)
  定义体: MvPowerSeries.substAlgHom ha.const

Depends on / 依赖: MvPowerSeries, MvPowerSeries.substAlgHom, X.prop, ha.const, substAlgHom
-/
noncomputable def substAlgHom (ha : HasSubst a) :
    PowerSeries R ->ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

/--
theorem `coe_substAlgHom` / 定理 `coe_substAlgHom`

English:
theorem coe_substAlgHom
  given: (ha : HasSubst a)
  proof: MvPowerSeries.coe_substAlgHom ha.const

中文:
定理 coe_substAlgHom
  条件: (ha : 有Subst a)
  证明: MvPowerSeries.coe_substAlgHom ha.const

Depends on / 依赖: X.prop
-/
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

attribute [local instance] DiscreteTopology.instContinuousSMul in
/--
theorem `substAlgHom_eq_aeval` / 定理 `substAlgHom_eq_aeval`

English:
theorem substAlgHom_eq_aeval
  proof: by
  ext1 f
  simpa [substAlgHom] using! congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f

中文:
定理 substAlgHom_eq_aeval
  证明: by
  ext1 f
  simpa [substAlgHom] using! congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.substAlgHom_eq_aeval, congr_fun, ha.const, substAlgHom, substAlgHom_eq_aeval
-/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : R⟦X⟧ ->ₐ[R] MvPowerSeries τ S) = PowerSeries.aeval ha.hasEval := by
  ext1 f
  simpa [substAlgHom] using! congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f

/--
theorem `subst_add` / 定理 `subst_add`

English:
theorem subst_add
  given: (ha : HasSubst a) (f g : PowerSeries R)
  proof: by
  rw [← coe_substAlgHom ha]; rw [map_add]

中文:
定理 subst_add
  条件: (ha : 有Subst a) (f g : 幂级数 R)
  证明: by
  rw [← coe_substAlgHom ha]; rw [map_add]

Depends on / 依赖: coe_substAlgHom, map_add
-/
theorem subst_add (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha]; rw [map_add]

/--
theorem `subst_sub` / 定理 `subst_sub`

English:
theorem subst_sub
  given: (ha : HasSubst a) (f g : PowerSeries R)
  proof: by
  rw [← coe_substAlgHom ha]; rw [map_sub]

中文:
定理 subst_sub
  条件: (ha : 有Subst a) (f g : 幂级数 R)
  证明: by
  rw [← coe_substAlgHom ha]; rw [map_sub]

Depends on / 依赖: coe_substAlgHom, map_sub
-/
theorem subst_sub (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha]; rw [map_sub]

/--
lemma `subst_zero_eq_C_constantCoeff` / 引理 `subst_zero_eq_C_constantCoeff`

English:
lemma subst_zero_eq_C_constantCoeff
  given: {f : PowerSeries R}
  proof: MvPowerSeries.subst_zero_eq_C_constantCoeff

@[simp]

中文:
引理 subst_zero_eq_C_constantCoeff
  条件: {f : 幂级数 R}
  证明: MvPowerSeries.subst_zero_eq_C_constantCoeff

@[simp]

Depends on / 依赖: algebraMap
-/
lemma subst_zero_eq_C_constantCoeff {f : PowerSeries R} :
    f.subst 0 = (MvPowerSeries.C f.constantCoeff (σ := τ)).map (algebraMap R S) :=
  MvPowerSeries.subst_zero_eq_C_constantCoeff

@[simp]
/--
theorem `subst_zero_of_constantCoeff_zero` / 定理 `subst_zero_of_constantCoeff_zero`

English:
theorem subst_zero_of_constantCoeff_zero
  given: {f : PowerSeries R} (hf : f.constantCoeff = 0)
  proof: MvPowerSeries.subst_zero_of_constantCoeff_zero hf

中文:
定理 subst_zero_of_constantCoeff_zero
  条件: {f : 幂级数 R} (hf : f.constantCoeff = 0)
  证明: MvPowerSeries.subst_zero_of_constantCoeff_zero hf

Depends on / 依赖: MvPowerSeries, MvPowerSeries.subst_zero_of_constantCoeff_zero, subst_zero_of_constantCoeff_zero
-/
theorem subst_zero_of_constantCoeff_zero {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    subst (0 : MvPowerSeries τ S) f = 0 :=
  MvPowerSeries.subst_zero_of_constantCoeff_zero hf

/--
theorem `subst_pow` / 定理 `subst_pow`

English:
theorem subst_pow
  given: (ha : HasSubst a) (f : PowerSeries R) (n : Nat)
  proof: by
  rw [← coe_substAlgHom ha]; rw [map_pow]

中文:
定理 subst_pow
  条件: (ha : 有Subst a) (f : 幂级数 R) (n : 自然数)
  证明: by
  rw [← coe_substAlgHom ha]; rw [map_pow]

Depends on / 依赖: coe_substAlgHom, map_pow
-/
theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : Nat) :
    subst a (f ^ n) = (subst a f) ^ n := by
  rw [← coe_substAlgHom ha]; rw [map_pow]

/--
theorem `subst_mul` / 定理 `subst_mul`

English:
theorem subst_mul
  given: (ha : HasSubst a) (f g : PowerSeries R)
  proof: by
  rw [← coe_substAlgHom ha]; rw [map_mul]

中文:
定理 subst_mul
  条件: (ha : 有Subst a) (f g : 幂级数 R)
  证明: by
  rw [← coe_substAlgHom ha]; rw [map_mul]

Depends on / 依赖: FintypeCat, FintypeCat.toLightProfiniteFullyFaithful.faithful, coe_substAlgHom, faithful, map_mul, toLightProfiniteFullyFaithful
-/
theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha]; rw [map_mul]

/--
theorem `subst_smul` / 定理 `subst_smul`

English:
theorem subst_smul
  statement: [Algebra A S] [IsScalarTower A R S]
  proof: by
  rw [← coe_substAlgHom ha]; rw [AlgHom.map_smul_of_tower]

中文:
定理 subst_smul
  结论: [代数 A S] [标量塔 A R S]
  证明: by
  rw [← coe_substAlgHom ha]; rw [AlgHom.map_smul_of_tower]

Depends on / 依赖: AlgHom, AlgHom.map_smul_of_tower, coe_substAlgHom, map_smul_of_tower
-/
theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha]; rw [AlgHom.map_smul_of_tower]

/--
theorem `coeff_subst_finite` / 定理 `coeff_subst_finite`

English:
theorem coeff_subst_finite
  given: (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat)
  proof: by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image]; rw [← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

中文:
定理 coeff_subst_finite
  条件: (ha : 有Subst a) (f : 幂级数 R) (e : τ ->₀ 自然数)
  证明: by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image]; rw [← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

Depends on / 依赖: Equiv.eq_comp_symm, Equiv.preimage_eq_iff_eq_image, Finite, Finsupp, Finsupp.uniqueLinearEquiv, Function, Function.HasFiniteSupport, Function.support_comp_eq_preimage, HasFiniteSupport, MvPowerSeries, MvPowerSeries.coeff_subst_finite, coeff_subst_finite, congr_arg, convert, eq_comp_symm, ha.const, preimage_eq_iff_eq_image, support_comp_eq_preimage, toEquiv, uniqueLinearEquiv
-/
theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat) :
    (fun (d : Nat) => coeff d f • MvPowerSeries.coeff e (a ^ d)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image]; rw [← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]

/--
theorem `coeff_subst_finite'` / 定理 `coeff_subst_finite'`

English:
theorem coeff_subst_finite'
  given: (hb : HasSubst b) (f : PowerSeries R) (e : Nat)
  proof: coeff_subst_finite hb f _

中文:
定理 coeff_subst_finite'
  条件: (hb : 有Subst b) (f : 幂级数 R) (e : 自然数)
  证明: coeff_subst_finite hb f _

Depends on / 依赖: Finite, coeff_subst_finite
-/
theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : Nat) :
    (fun (d : Nat) => coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport :=
  coeff_subst_finite hb f _

/--
theorem `coeff_subst` / 定理 `coeff_subst`

English:
theorem coeff_subst
  given: (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat)
  proof: by
  rw [subst]; rw [MvPowerSeries.coeff_subst ha.const f e]; rw [← finsum_comp_equiv
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.symm]
  apply finsum_congr
  intro
  congr
  simp

中文:
定理 coeff_subst
  条件: (ha : 有Subst a) (f : 幂级数 R) (e : τ ->₀ 自然数)
  证明: by
  rw [subst]; rw [MvPowerSeries.coeff_subst ha.const f e]; rw [← finsum_comp_equiv
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.symm]
  apply finsum_congr
  intro
  congr
  simp

Depends on / 依赖: F.obj, Finsupp, Finsupp.uniqueLinearEquiv, MvPowerSeries, MvPowerSeries.coeff_subst, Subtype, Subtype.totallyDisconnectedSpace, TotallyDisconnectedSpace, coeff_subst, finsum_comp_equiv, finsum_congr, ha.const, toEquiv, toEquiv.symm, totallyDisconnectedSpace, uniqueLinearEquiv
-/
theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat) :
    MvPowerSeries.coeff e (subst a f) =
      finsum (fun (d : Nat) =>
        coeff d f • (MvPowerSeries.coeff e (a ^ d))) := by
  rw [subst]; rw [MvPowerSeries.coeff_subst ha.const f e]; rw [← finsum_comp_equiv
    (Finsupp.uniqueLinearEquiv Nat Nat ()).toEquiv.symm]
  apply finsum_congr
  intro
  congr
  simp

/--
theorem `coeff_subst'` / 定理 `coeff_subst'`

English:
theorem coeff_subst'
  given: {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : Nat)
  proof: by
  simp [PowerSeries.coeff, coeff_subst hb]

中文:
定理 coeff_subst'
  条件: {b : S⟦X⟧} (hb : 有Subst b) (f : R⟦X⟧) (e : 自然数)
  证明: by
  simp [PowerSeries.coeff, coeff_subst hb]

Depends on / 依赖: PowerSeries, PowerSeries.coeff, coeff_subst
-/
theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : Nat) :
    coeff e (f.subst b) =
      finsum (fun (d : Nat) =>
        coeff d f • PowerSeries.coeff e (b ^ d)) := by
  simp [PowerSeries.coeff, coeff_subst hb]

/--
theorem `constantCoeff_subst` / 定理 `constantCoeff_subst`

English:
theorem constantCoeff_subst
  given: (ha : HasSubst a) (f : PowerSeries R)
  proof: by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

@[simp]

中文:
定理 constantCoeff_subst
  条件: (ha : 有Subst a) (f : 幂级数 R)
  证明: by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

@[simp]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst, coeff_zero_eq_constantCoeff_apply
-/
theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (subst a f) =
      finsum (fun d => coeff d f • MvPowerSeries.constantCoeff (a ^ d)) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

@[simp]
/--
theorem `coeff_subst_X_pow` / 定理 `coeff_subst_X_pow`

English:
theorem coeff_subst_X_pow
  given: {k : Nat} (hk : k != 0) (f : PowerSeries R) (n : Nat)
  proof: by
  split_ifs with h
  · rw [coeff_subst' (.X_pow hk), finsum_eq_single _ (n / k), ← pow_mul, Nat.mul_div_cancel' h,
      coeff_X_pow_self, Algebra.algebraMap_eq_smul_one]
    intro j hj
    rw [← pow_mul]; rw [coeff_X_pow]; rw [if_neg]; rw [smul_zero]
    contrapose hj
    rw [hj]; rw [Nat.mul_di

中文:
定理 coeff_subst_X_pow
  条件: {k : 自然数} (hk : k != 0) (f : 幂级数 R) (n : 自然数)
  证明: by
  split_ifs with h
  · rw [coeff_subst' (.X_pow hk), finsum_eq_single _ (n / k), ← pow_mul, Nat.mul_div_cancel' h,
      coeff_X_pow_self, Algebra.algebraMap_eq_smul_one]
    intro j hj
    rw [← pow_mul]; rw [coeff_X_pow]; rw [if_neg]; rw [smul_zero]
    contrapose hj
    rw [hj]; rw [Nat.mul_di

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, Nat.mul_div_cancel, Nat.mul_div_cancel_left, X_pow, algebraMap_eq_smul_one, coeff_X_pow, coeff_X_pow_self, coeff_subst, contrapose, finsum_eq_single, finsum_eq_zero_of_forall_eq_zero, hk.pos, if_neg, mul_div_cancel, mul_div_cancel_left, pow_mul, smul_zero, split_ifs
-/
theorem coeff_subst_X_pow {k : Nat} (hk : k != 0) (f : PowerSeries R) (n : Nat) :
    coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebraMap R S (coeff (n / k) f)) 0 := by
  split_ifs with h
  · rw [coeff_subst' (.X_pow hk), finsum_eq_single _ (n / k), ← pow_mul, Nat.mul_div_cancel' h,
      coeff_X_pow_self, Algebra.algebraMap_eq_smul_one]
    intro j hj
    rw [← pow_mul]; rw [coeff_X_pow]; rw [if_neg]; rw [smul_zero]
    contrapose hj
    rw [hj]; rw [Nat.mul_div_cancel_left j hk.pos]
  · rw [coeff_subst' (.X_pow hk), finsum_eq_zero_of_forall_eq_zero]
    intro j
    rw [← pow_mul]; rw [coeff_X_pow]; rw [if_neg]; rw [smul_zero]
    contrapose h
    use j

@[simp]
/--
theorem `constantCoeff_subst_X_pow` / 定理 `constantCoeff_subst_X_pow`

English:
theorem constantCoeff_subst_X_pow
  given: {k : Nat} (hk : k != 0) (f : PowerSeries R)
  proof: by
  rw [← coeff_zero_eq_constantCoeff]; rw [coeff_subst_X_pow hk]; rw [if_pos (dvd_zero k)]; rw [Nat.zero_div]; rw [coeff_zero_eq_constantCoeff]

中文:
定理 constantCoeff_subst_X_pow
  条件: {k : 自然数} (hk : k != 0) (f : 幂级数 R)
  证明: by
  rw [← coeff_zero_eq_constantCoeff]; rw [coeff_subst_X_pow hk]; rw [if_pos (dvd_zero k)]; rw [Nat.zero_div]; rw [coeff_zero_eq_constantCoeff]

Depends on / 依赖: Nat.zero_div, coeff_subst_X_pow, coeff_zero_eq_constantCoeff, dvd_zero, if_pos, zero_div
-/
theorem constantCoeff_subst_X_pow {k : Nat} (hk : k != 0) (f : PowerSeries R) :
    constantCoeff (subst (X ^ k) f) = algebraMap R S f.constantCoeff := by
  rw [← coeff_zero_eq_constantCoeff]; rw [coeff_subst_X_pow hk]; rw [if_pos (dvd_zero k)]; rw [Nat.zero_div]; rw [coeff_zero_eq_constantCoeff]

/--
theorem `constantCoeff_subst_eq_zero` / 定理 `constantCoeff_subst_eq_zero`

English:
theorem constantCoeff_subst_eq_zero
  statement: (ha : a.constantCoeff = 0) (f : PowerSeries R)
  proof: by
  have := MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_iff.mp <| HasSubst.of_constantCoeff_zero ha) (fun _ => ha) hf
  simpa [hasSubst_iff]

中文:
定理 constantCoeff_subst_eq_zero
  结论: (ha : a.constantCoeff = 0) (f : 幂级数 R)
  证明: by
  have := MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_iff.mp <| HasSubst.of_constantCoeff_zero ha) (fun _ => ha) hf
  simpa [hasSubst_iff]

Depends on / 依赖: HasSubst, HasSubst.of_constantCoeff_zero, MvPowerSeries, MvPowerSeries.constantCoeff_subst_eq_zero, constantCoeff_subst_eq_zero, hasSubst_iff, hasSubst_iff.mp, of_constantCoeff_zero
-/
theorem constantCoeff_subst_eq_zero (ha : a.constantCoeff = 0) (f : PowerSeries R)
    (hf : f.constantCoeff = 0) : MvPowerSeries.constantCoeff (subst a f) = 0 := by
  have := MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_iff.mp <| HasSubst.of_constantCoeff_zero ha) (fun _ => ha) hf
  simpa [hasSubst_iff]

/--
theorem `map_algebraMap_eq_subst_X` / 定理 `map_algebraMap_eq_subst_X`

English:
theorem map_algebraMap_eq_subst_X
  given: (f : R⟦X⟧)
  proof: MvPowerSeries.map_algebraMap_eq_subst_X f

中文:
定理 map_algebraMap_eq_subst_X
  条件: (f : R⟦X⟧)
  证明: MvPowerSeries.map_algebraMap_eq_subst_X f

Depends on / 依赖: MvPowerSeries, MvPowerSeries.map_algebraMap_eq_subst_X, map_algebraMap_eq_subst_X
-/
theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

/--
lemma `coeff_subst_single` / 引理 `coeff_subst_single`

English:
lemma coeff_subst_single
  given: {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ ->₀ Nat)
  proof: by
  rw [coeff_subst (HasSubst.X s)]; rw [finsum_eq_single _ (e s)] <;>
  grind [MvPowerSeries.coeff_X_pow, smul_eq_mul]

@[simp]

中文:
引理 coeff_subst_single
  条件: {σ : 类型} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ ->₀ 自然数)
  证明: by
  rw [coeff_subst (HasSubst.X s)]; rw [finsum_eq_single _ (e s)] <;>
  grind [MvPowerSeries.coeff_X_pow, smul_eq_mul]

@[simp]

Depends on / 依赖: HasSubst, HasSubst.X, MvPowerSeries, MvPowerSeries.coeff_X_pow, coeff_X_pow, coeff_subst, finsum_eq_single, smul_eq_mul
-/
lemma coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ ->₀ Nat) :
    MvPowerSeries.coeff e (subst (MvPowerSeries.X s) f) =
      if e = Finsupp.single s (e s) then coeff (e s) f else 0 := by
  rw [coeff_subst (HasSubst.X s)]; rw [finsum_eq_single _ (e s)] <;>
  grind [MvPowerSeries.coeff_X_pow, smul_eq_mul]

@[simp]
/--
theorem `X_subst` / 定理 `X_subst`

English:
theorem X_subst
  given: (f : R⟦X⟧)
  statement: f.subst (X : R⟦X⟧) = f
  proof: by
  rw [← map_algebraMap_eq_subst_X (S := R)]; rw [Algebra.algebraMap_self]
  exact congr_fun map_id f

中文:
定理 X_subst
  条件: (f : R⟦X⟧)
  结论: f.subst (X : R⟦X⟧) = f
  证明: by
  rw [← map_algebraMap_eq_subst_X (S := R)]; rw [Algebra.algebraMap_self]
  exact congr_fun map_id f

Depends on / 依赖: Algebra, Algebra.algebraMap_self, algebraMap_self, congr_fun, map_algebraMap_eq_subst_X, map_id
-/
theorem X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := by
  rw [← map_algebraMap_eq_subst_X (S := R)]; rw [Algebra.algebraMap_self]
  exact congr_fun map_id f

/--
theorem `_root_.Polynomial.toPowerSeries_toMvPowerSeries` / 定理 `_root_.Polynomial.toPowerSeries_toMvPowerSeries`

English:
theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries
  given: (p : Polynomial R)
  statement: (p : PowerSeries R) =
  proof: Polynomial.pUnitAlgEquiv_symm_toPowerSeries

中文:
定理 _root_.多项式.toPowerSeries_toMvPowerSeries
  条件: (p : 多项式 R)
  结论: (p : 幂级数 R) =
  证明: Polynomial.pUnitAlgEquiv_symm_toPowerSeries

Depends on / 依赖: Polynomial, Polynomial.pUnitAlgEquiv_symm_toPowerSeries, pUnitAlgEquiv_symm_toPowerSeries
-/
theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) : (p : PowerSeries R) =
    ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) :=
  Polynomial.pUnitAlgEquiv_symm_toPowerSeries

/--
theorem `substAlgHom_coe` / 定理 `substAlgHom_coe`

English:
theorem substAlgHom_coe
  given: (ha : HasSubst a) (p : Polynomial R)
  proof: by
  rw [p.toPowerSeries_toMvPowerSeries]; rw [substAlgHom]; rw [MvPowerSeries.coe_substAlgHom]; rw [MvPowerSeries.subst_coe]; rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp

中文:
定理 substAlgHom_coe
  条件: (ha : 有Subst a) (p : 多项式 R)
  证明: by
  rw [p.toPowerSeries_toMvPowerSeries]; rw [substAlgHom]; rw [MvPowerSeries.coe_substAlgHom]; rw [MvPowerSeries.subst_coe]; rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.congr_fun, MvPowerSeries, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_coe, Polynomial, Polynomial.algHom_ext, algHom_ext, coe_substAlgHom, comp_apply, congr_fun, p.toPowerSeries_toMvPowerSeries, substAlgHom, subst_coe, toPowerSeries_toMvPowerSeries
-/
theorem substAlgHom_coe (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries]; rw [substAlgHom]; rw [MvPowerSeries.coe_substAlgHom]; rw [MvPowerSeries.subst_coe]; rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp

/--
theorem `substAlgHom_X` / 定理 `substAlgHom_X`

English:
theorem substAlgHom_X
  given: (ha : HasSubst a)
  proof: by
  rw [← Polynomial.coe_X]; rw [substAlgHom_coe]; rw [Polynomial.aeval_X]

中文:
定理 substAlgHom_X
  条件: (ha : 有Subst a)
  证明: by
  rw [← Polynomial.coe_X]; rw [substAlgHom_coe]; rw [Polynomial.aeval_X]

Depends on / 依赖: Polynomial, Polynomial.aeval_X, Polynomial.coe_X, aeval_X, coe_X, substAlgHom_coe
-/
theorem substAlgHom_X (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X]; rw [substAlgHom_coe]; rw [Polynomial.aeval_X]

/--
theorem `subst_coe` / 定理 `subst_coe`

English:
theorem subst_coe
  given: (ha : HasSubst a) (p : Polynomial R)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_coe]

@[simp]

中文:
定理 subst_coe
  条件: (ha : 有Subst a) (p : 多项式 R)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_coe]

@[simp]

Depends on / 依赖: coe_substAlgHom, substAlgHom_coe
-/
theorem subst_coe (ha : HasSubst a) (p : Polynomial R) :
    subst a (p : PowerSeries R) = (Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_coe]

@[simp]
/--
theorem `subst_C` / 定理 `subst_C`

English:
theorem subst_C
  given: (r : S)
  statement: (C r).subst a = MvPowerSeries.C r
  proof: MvPowerSeries.subst_C _

中文:
定理 subst_C
  条件: (r : S)
  结论: (C r).subst a = MvPowerSeries.C r
  证明: MvPowerSeries.subst_C _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.subst_C, subst_C
-/
theorem subst_C (r : S) : (C r).subst a = MvPowerSeries.C r := MvPowerSeries.subst_C _

/--
theorem `subst_X` / 定理 `subst_X`

English:
theorem subst_X
  given: (ha : HasSubst a)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

omit [Algebra R S] in

中文:
定理 subst_X
  条件: (ha : 有Subst a)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

omit [Algebra R S] in

Depends on / 依赖: coe_substAlgHom, substAlgHom_X
-/
theorem subst_X (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_X]

omit [Algebra R S] in
/--
theorem `map_subst` / 定理 `map_subst`

English:
theorem map_subst
  given: {a : MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S} (f : PowerSeries R)
  proof: MvPowerSeries.map_subst (HasSubst.const ha) f

中文:
定理 map_subst
  条件: {a : MvPowerSeries τ R} (ha : 有Subst a) {h : R ->+* S} (f : 幂级数 R)
  证明: MvPowerSeries.map_subst (HasSubst.const ha) f

Depends on / 依赖: HasSubst, HasSubst.const, MvPowerSeries, MvPowerSeries.map_subst, map_subst
-/
theorem map_subst {a : MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S} (f : PowerSeries R) :
    (f.subst a).map h = (f.map h).subst (a.map h) :=
  MvPowerSeries.map_subst (HasSubst.const ha) f

section

/--
theorem `le_weightedOrder_subst` / 定理 `le_weightedOrder_subst`

English:
theorem le_weightedOrder_subst
  given: (w : τ -> Nat) (ha : HasSubst a) (f : PowerSeries R)
  proof: by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert! hi; a

中文:
定理 le_weightedOrder_subst
  条件: (w : τ -> 自然数) (ha : 有Subst a) (f : 幂级数 R)
  证明: by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert! hi; a

Depends on / 依赖: Finsupp, Finsupp.sum_fintype, Finsupp.weight_apply, Function, Function.comp_const, MvPowerSeries, MvPowerSeries.le_weightedOrder_subst, MvPowerSeries.weightedOrder, PowerSeries, PowerSeries.coeff, PowerSeries.hasSubst_iff.mp, comp_const, convert, f.order_le, hasSubst_iff, le_iInf_iff, le_weightedOrder_subst, mul_le_mul_left, ne_eq, order_le
-/
theorem le_weightedOrder_subst (w : τ -> Nat) (ha : HasSubst a) (f : PowerSeries R) :
    f.order * a.weightedOrder w <= (f.subst a).weightedOrder w := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert! hi; aesop)) _
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype]

/--
theorem `le_order_subst` / 定理 `le_order_subst`

English:
theorem le_order_subst
  given: (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries R)
  proof: by
  refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  simp [order_eq_order]

中文:
定理 le_order_subst
  条件: (a : MvPowerSeries τ S) (ha : 有Subst a) (f : 幂级数 R)
  证明: by
  refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  simp [order_eq_order]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.le_order_subst, PowerSeries, PowerSeries.hasSubst_iff.mp, hasSubst_iff, inducedFunctor, le_order_subst, order_eq_order
-/
theorem le_order_subst (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries R) :
    a.order * f.order <= (f.subst a).order := by
  refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  simp [order_eq_order]

/--
theorem `le_order_subst_left` / 定理 `le_order_subst_left`

English:
theorem le_order_subst_left
  statement: {f : MvPowerSeries τ R} {φ : PowerSeries R}
  proof: .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

中文:
定理 le_order_subst_left
  结论: {f : MvPowerSeries τ R} {φ : 幂级数 R}
  证明: .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

Depends on / 依赖: Clopens, ENat.self_le_mul_left, HasSubst, HasSubst.of_constantCoeff_zero, PowerSeries, PowerSeries.le_order_subst, TopologicalSpace, TopologicalSpace.Clopens.countable_iff_secondCountable, countable_iff_secondCountable, f.order_ne_zero_iff_constCoeff_eq_zero.mpr, infer_instance, le_order_subst, of_constantCoeff_zero, order_ne_zero_iff_constCoeff_eq_zero, self_le_mul_left
-/
theorem le_order_subst_left {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) : φ.order <= (φ.subst f).order :=
  .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

/--
theorem `le_order_subst_right` / 定理 `le_order_subst_right`

English:
theorem le_order_subst_right
  statement: {f : MvPowerSeries τ R} {φ : PowerSeries R}
  proof: .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

中文:
定理 le_order_subst_right
  结论: {f : MvPowerSeries τ R} {φ : 幂级数 R}
  证明: .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

Depends on / 依赖: ENat.self_le_mul_right, HasSubst, HasSubst.of_constantCoeff_zero, PowerSeries, PowerSeries.le_order_subst, le_order_subst, of_constantCoeff_zero, order_ne_zero_iff_constCoeff_eq_zero, order_ne_zero_iff_constCoeff_eq_zero.mpr, self_le_mul_right
-/
theorem le_order_subst_right {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) (hφ : φ.constantCoeff = 0) : f.order <= (φ.subst f).order :=
  .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)

/--
theorem `le_order_subst_left'` / 定理 `le_order_subst_left'`

English:
theorem le_order_subst_left'
  given: {f φ : PowerSeries R} (hf : f.constantCoeff = 0)
  proof: by
  conv_rhs => rw [order_eq_order]
  exact le_order_subst_left hf

中文:
定理 le_order_subst_left'
  条件: {f φ : 幂级数 R} (hf : f.constantCoeff = 0)
  证明: by
  conv_rhs => rw [order_eq_order]
  exact le_order_subst_left hf

Depends on / 依赖: conv_rhs, le_order_subst_left, order_eq_order
-/
theorem le_order_subst_left' {f φ : PowerSeries R} (hf : f.constantCoeff = 0) :
    φ.order <= PowerSeries.order (φ.subst f) := by
  conv_rhs => rw [order_eq_order]
  exact le_order_subst_left hf

/--
theorem `le_order_subst_right'` / 定理 `le_order_subst_right'`

English:
theorem le_order_subst_right'
  statement: {f φ : PowerSeries R} (hf : f.constantCoeff = 0)
  proof: by
  simp_rw [order_eq_order]
  exact le_order_subst_right hf hφ

中文:
定理 le_order_subst_right'
  结论: {f φ : 幂级数 R} (hf : f.constantCoeff = 0)
  证明: by
  simp_rw [order_eq_order]
  exact le_order_subst_right hf hφ

Depends on / 依赖: le_order_subst_right, order_eq_order, simp_rw
-/
theorem le_order_subst_right' {f φ : PowerSeries R} (hf : f.constantCoeff = 0)
    (hφ : φ.constantCoeff = 0) : f.order <= PowerSeries.order (φ.subst f) := by
  simp_rw [order_eq_order]
  exact le_order_subst_right hf hφ

end

/--
theorem `HasSubst.comp` / 定理 `HasSubst.comp`

English:
theorem HasSubst.comp
  proof: MvPowerSeries.IsNilpotent_substAlgHom hb.const ha

中文:
定理 有Subst.comp
  证明: MvPowerSeries.IsNilpotent_substAlgHom hb.const ha

Depends on / 依赖: Clopens, Countable, Countable.of_equiv, Finite, Finite.of_injective, Finite.to_countable, FintypeCat, FintypeCat.toProfinite, Function, Function.Surjective.countable, LocallyConstant, LocallyConstant.coe_injective, LocallyConstant.equivClopens, Pi.finite, S.cone.pt, S.diagram, Surjective, TopologicalSpace, TopologicalSpace.Clopens.countable_iff_secondCountable, coe_injective
-/
theorem HasSubst.comp
    {a : PowerSeries S} (ha : HasSubst a) {b : MvPowerSeries υ T} (hb : HasSubst b) :
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_substAlgHom hb.const ha

variable {a : PowerSeries S} {b : MvPowerSeries υ T} {a' : MvPowerSeries τ S}
  {b' : τ -> MvPowerSeries υ T} [IsScalarTower R S T]

/--
theorem `substAlgHom_comp_substAlgHom` / 定理 `substAlgHom_comp_substAlgHom`

English:
theorem substAlgHom_comp_substAlgHom
  given: (ha : HasSubst a) (hb : HasSubst b)
  proof: MvPowerSeries.substAlgHom_comp_substAlgHom _ _

中文:
定理 substAlgHom_comp_substAlgHom
  条件: (ha : 有Subst a) (hb : 有Subst b)
  证明: MvPowerSeries.substAlgHom_comp_substAlgHom _ _

Depends on / 依赖: MvPowerSeries, MvPowerSeries.substAlgHom_comp_substAlgHom, substAlgHom_comp_substAlgHom
-/
theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

/--
theorem `substAlgHom_comp_substAlgHom_apply` / 定理 `substAlgHom_comp_substAlgHom_apply`

English:
theorem substAlgHom_comp_substAlgHom_apply
  given: (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R)
  proof: DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

中文:
定理 substAlgHom_comp_substAlgHom_apply
  条件: (ha : 有Subst a) (hb : 有Subst b) (f : 幂级数 R)
  证明: DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, substAlgHom_comp_substAlgHom
-/
theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

/--
theorem `subst_comp_subst` / 定理 `subst_comp_subst`

English:
theorem subst_comp_subst
  given: (ha : HasSubst a) (hb : HasSubst b)
  proof: by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb

中文:
定理 subst_comp_subst
  条件: (ha : 有Subst a) (hb : 有Subst b)
  证明: by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb

Depends on / 依赖: DFunLike, DFunLike.ext_iff, coe_substAlgHom, ext_iff, funext_iff, substAlgHom_comp_substAlgHom
-/
theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb

/--
theorem `subst_comp_subst_apply` / 定理 `subst_comp_subst_apply`

English:
theorem subst_comp_subst_apply
  given: (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R)
  proof: congr_fun (subst_comp_subst ha hb) f

中文:
定理 subst_comp_subst_apply
  条件: (ha : 有Subst a) (hb : 有Subst b) (f : 幂级数 R)
  证明: congr_fun (subst_comp_subst ha hb) f

Depends on / 依赖: congr_fun, subst_comp_subst
-/
theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst ha hb) f

/--
lemma `rescale_eq` / 引理 `rescale_eq`

English:
lemma rescale_eq
  given: (r : R) (f : PowerSeries R)
  proof: by
  ext n
  rw [coeff_rescale]; rw [coeff]; rw [MvPowerSeries.coeff_rescale]
  simp [pow_zero, Finsupp.prod_single_index]

@[deprecated (since := "2026-02-27")] alias _root_.MvPowerSeries.rescaleUnit := rescale_eq

中文:
引理 rescale_eq
  条件: (r : R) (f : 幂级数 R)
  证明: by
  ext n
  rw [coeff_rescale]; rw [coeff]; rw [MvPowerSeries.coeff_rescale]
  simp [pow_zero, Finsupp.prod_single_index]

@[deprecated (since := "2026-02-27")] alias _root_.MvPowerSeries.rescaleUnit := rescale_eq

Depends on / 依赖: Finsupp, Finsupp.prod_single_index, MvPowerSeries, MvPowerSeries.coeff_rescale, coeff_rescale, pow_zero, prod_single_index
-/
lemma rescale_eq (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ => r) f := by
  ext n
  rw [coeff_rescale]; rw [coeff]; rw [MvPowerSeries.coeff_rescale]
  simp [pow_zero, Finsupp.prod_single_index]

@[deprecated (since := "2026-02-27")] alias _root_.MvPowerSeries.rescaleUnit := rescale_eq

/--
lemma `rescale_eq_subst` / 引理 `rescale_eq_subst`

English:
lemma rescale_eq_subst
  given: (r : R) (f : PowerSeries R)
  proof: by
  rw [rescale_eq]; rw [MvPowerSeries.rescale_eq_subst]; rw [X]; rw [subst]; rw [Pi.smul_def']

中文:
引理 rescale_eq_subst
  条件: (r : R) (f : 幂级数 R)
  证明: by
  rw [rescale_eq]; rw [MvPowerSeries.rescale_eq_subst]; rw [X]; rw [subst]; rw [Pi.smul_def']

Depends on / 依赖: Category, InducedCategory, LightDiagram, MvPowerSeries, MvPowerSeries.rescale_eq_subst, Pi.smul_def, rescale_eq, rescale_eq_subst, smul_def, toProfinite
-/
lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq]; rw [MvPowerSeries.rescale_eq_subst]; rw [X]; rw [subst]; rw [Pi.smul_def']

/--
Definition of `rescaleAlgHom` / `rescaleAlgHom` 的定义

English:
abbreviation rescaleAlgHom
  signature: (r : R)
  body: MvPowerSeries.rescaleAlgHom (fun _ => r)

中文:
缩写 rescaleAlgHom
  签名: (r : R)
  定义体: MvPowerSeries.rescaleAlgHom (fun _ => r)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.rescaleAlgHom, Skeleton, Skeleton.equivalence.functor, X.diagram, diagram, equivalence, functor, isLimit, limit.isLimit, rescaleAlgHom
-/
noncomputable abbrev rescaleAlgHom (r : R) : R⟦X⟧ ->ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom (fun _ => r)

/--
theorem `coe_rescaleAlgHom` / 定理 `coe_rescaleAlgHom`

English:
theorem coe_rescaleAlgHom
  given: (r : R)
  statement: rescaleAlgHom r = rescale r
  proof: by
  ext f
  rw [rescale_eq]; rw [RingHom.coe_coe]; rw [MvPowerSeries.rescaleAlgHom_apply]

中文:
定理 coe_rescaleAlgHom
  条件: (r : R)
  结论: rescaleAlgHom r = rescale r
  证明: by
  ext f
  rw [rescale_eq]; rw [RingHom.coe_coe]; rw [MvPowerSeries.rescaleAlgHom_apply]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.rescaleAlgHom_apply, RingHom, RingHom.coe_coe, coe_coe, rescaleAlgHom_apply, rescale_eq
-/
theorem coe_rescaleAlgHom (r : R) : rescaleAlgHom r = rescale r := by
  ext f
  rw [rescale_eq]; rw [RingHom.coe_coe]; rw [MvPowerSeries.rescaleAlgHom_apply]

/--
lemma `subst_rescale_of_degree_eq_one` / 引理 `subst_rescale_of_degree_eq_one`

English:
lemma subst_rescale_of_degree_eq_one
  statement: (a : R) {σ : Type*} (p : MvPowerSeries σ R)
  proof: by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; rw [MvPowerSeries.coeff_apply]
    have : (p 0 != 0) -> (0 : σ ->₀ Nat).degree = 1 := hp_lin 0
    grind
  rw [rescale_eq_subst]; rw [MvPowerSeries.rescale

中文:
引理 subst_rescale_of_degree_eq_one
  结论: (a : R) {σ : 类型} (p : MvPowerSeries σ R)
  证明: by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; rw [MvPowerSeries.coeff_apply]
    have : (p 0 != 0) -> (0 : σ ->₀ Nat).degree = 1 := hp_lin 0
    grind
  rw [rescale_eq_subst]; rw [MvPowerSeries.rescale

Depends on / 依赖: HasSubst, HasSubst.of_constantCoeff_zero, HasSubst.smul_X, InducedCategory, InducedCategory.homMk, MvPowerSeries, MvPowerSeries.HasSubst.smul_X, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.ext_iff, MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply, PowerSeries, PowerSeries.HasSubst, coeff_apply, coeff_zero_eq_constantCoeff_apply, degree, ext_iff, f.hom, hp.const
-/
lemma subst_rescale_of_degree_eq_one (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : forall d in Function.support p, d.degree = 1) (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; rw [MvPowerSeries.coeff_apply]
    have : (p 0 != 0) -> (0 : σ ->₀ Nat).degree = 1 := hp_lin 0
    grind
  rw [rescale_eq_subst]; rw [MvPowerSeries.rescale_eq_subst]; rw [subst_comp_subst_apply (HasSubst.smul_X' a) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.HasSubst.smul_X _)]; rw [MvPowerSeries.ext_iff]
  intro _
  rw [subst_smul hp]; rw [← Polynomial.coe_X]; rw [subst_coe hp]; rw [Polynomial.aeval_X]; rw [← MvPowerSeries.rescale_eq_subst]; rw [MvPowerSeries.rescale_homogeneous_eq_smul hp_lin]; rw [subst]; rw [pow_one]

section substInv

section Invertible

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (coeff 1 P)]

open PowerSeries

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the construction of a power series `Q` such that `P(Q(X)) = X`. -/
noncomputable
/--
Definition of `substInvFun` / `substInvFun` 的定义

English:
definition substInvFun
  signature: : Nat -> R

中文:
定义 substInvFun
  签名: : 自然数 -> R

Depends on / 依赖: Functor, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Limits, Limits.lim.mapIso, Skeleton, Skeleton.equivalence.counitIso, Skeleton.equivalence.inverse, Y.diagram, Y.isLimit, conePointUniqueUpToIso, counitIso, diagram, equivalence, inverse, isLimit, isoWhiskerLeft, isoWhiskerRight, lightDiagramToProfinite, lightDiagramToProfinite.preimageIso
-/
def substInvFun : Nat -> R
  | 0 => 0
  | 1 => ⅟(P.coeff 1)
  | n + 1 => - ⅟(P.coeff 1) *
      (coeff (n + 1) (P.subst (∑ i : Fin (n + 1), C (substInvFun i.1) * X ^ i.1)))

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the power series `Q` such that `P(Q(X)) = X`. See `PowerSeries.subst_substInv_right`.

See also `PowerSeries.substInvOfIsUnit` for a variant using `IsUnit`. -/
noncomputable
/--
Definition of `substInv` / `substInv` 的定义

English:
definition substInv
  signature: : PowerSeries R
  body: .mk (substInvFun P)

include hP in

中文:
定义 substInv
  签名: : 幂级数 R
  定义体: .mk (substInvFun P)

include hP in

Depends on / 依赖: substInvFun
-/
def substInv : PowerSeries R := .mk (substInvFun P)

include hP in
/--
lemma `coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X` / 引理 `coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X`

English:
lemma coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X
  given: (n : Nat)
  proof: by
  obtain (_ | _ | n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · rw [map_sub, coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_ | _ | _) _ 

中文:
引理 coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X
  条件: (n : 自然数)
  证明: by
  obtain (_ | _ | n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · rw [map_sub, coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_ | _ | _) _ 

Depends on / 依赖: Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, HasSubst, LightDiagram, LightDiagram.equivSmall, coeff_mul_X_pow, coeff_subst, contextual, equivSmall, finsum_eq_single, generalize, map_sub, mul_pow, substInvFu, substInvFun, sum_univ_castSucc, val_castSucc, val_last, zero_pow_eq
-/
lemma coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X (n : Nat) :
    coeff n (P.subst (∑ i : Fin (n + 1), C (substInvFun P i.1) * X ^ i.1) - X) = 0 := by
  obtain (_ | _ | n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · rw [map_sub, coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_ | _ | _) _ <;> simp_all [substInvFun, mul_pow, coeff_mul_X_pow']
    · simp [HasSubst, X, substInvFun]
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, map_sub, substInvFun]
    generalize hB : ∑ i : Fin (n + 2), C (substInvFun P i) * X ^ i.1 = B
    have hB' : B.constantCoeff = 0 := by simp [← hB, zero_pow_eq, substInvFun]
    simp only [neg_mul, map_neg, map_mul, coeff_X, Nat.add_eq_right, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, sub_zero]
    rw [coeff_subst']
    · simp only [smul_eq_mul, ← map_mul]
      generalize hk : ⅟(P.coeff 1) * coeff (n + 1 + 1) (subst B P) = k
      trans ∑ᶠ d, P.coeff d * (coeff (n + 1 + 1) (B ^ d) - if d = 1 then k else 0)
      · refine finsum_congr fun i => ?_
        · congr 1
          obtain (_ | _ | i) := i
          · simp
          · simp [← sub_eq_add_neg]
          · simp only [add_assoc, Nat.reduceAdd]
            rw [add_comm B]; rw [add_pow]; rw [map_sum]; rw [Finset.sum_eq_single (a := 0)]
            · simp
            · rintro (_ | _ | j) hj hj'
              · simp at hj'
              · simp [mul_comm (C k), hB', mul_assoc, coeff_X_pow_mul']
              · rw [← neg_mul, mul_pow, ← pow_mul, mul_comm (_ ^ _)]
                simp [mul_assoc, coeff_X_pow_mul']
            · simp
      · simp_rw [mul_sub]
        rw [finsum_sub_distrib]
        · simp only [mul_ite, mul_zero]
          nth_rw 2 [finsum_eq_single (a := 1)]
          · simp only [↓reduceIte, ← hk, mul_invOf_cancel_left', sub_eq_zero]
            rw [coeff_subst']
            · rfl
            · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']
          · simp +contextual
        · refine .subset (Set.finite_Iio (n + 3)) fun i => ?_
          obtain ⟨B, rfl⟩ : X ∣ B := by rwa [X_dvd_iff]
          simp +contextual [mul_pow, coeff_X_pow_mul', Nat.lt_succ_iff]
        · exact .subset (Set.finite_singleton 1) (fun _ => by simp +contextual)
    · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']

include hP in
/--
lemma `subst_substInv_right` / 引理 `subst_substInv_right`

English:
lemma subst_substInv_right
  proof: by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub]; rw [sub_eq_zero] at this
  rw [← this]; rw [coeff_subst']; rw [coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), C (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInv

中文:
引理 subst_substInv_right
  证明: by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub]; rw [sub_eq_zero] at this
  rw [← this]; rw [coeff_subst']; rw [coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), C (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInv

Depends on / 依赖: Fin.ext_iff, Finset, Finset.sum_eq_single, X_pow_dvd_iff, coeff_X_pow, coeff_subst, coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X, contextual, eq_comm, ext_iff, generalize, map_sub, sub_dvd_pow_sub_pow, sub_eq_zero, substInvFun, sum_eq_single, this.trans
-/
lemma subst_substInv_right :
    P.subst (substInv P) = X := by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub]; rw [sub_eq_zero] at this
  rw [← this]; rw [coeff_subst']; rw [coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), C (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInvFun P) - B := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp +contextual [← hB, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
        Fin.ext_iff, @eq_comm _ m]
    obtain ⟨Q, hQ⟩ := this.trans (sub_dvd_pow_sub_pow _ _ m)
    simp [substInv, sub_eq_iff_eq_add.mp hQ, coeff_X_pow_mul']
  · simp [HasSubst, X, zero_pow_eq, C, substInvFun]
  · simp [HasSubst, ← constantCoeff.eq_def, substInvFun, substInv]

@[simp]
/--
lemma `constantCoeff_substInv` / 引理 `constantCoeff_substInv`

English:
lemma constantCoeff_substInv
  statement: P.substInv.constantCoeff = 0
  proof: by
  simp [substInv, substInvFun]

中文:
引理 constantCoeff_substInv
  结论: P.substInv.constantCoeff = 0
  证明: by
  simp [substInv, substInvFun]

Depends on / 依赖: substInv, substInvFun
-/
lemma constantCoeff_substInv : P.substInv.constantCoeff = 0 := by
  simp [substInv, substInvFun]

/--
lemma `HasSubst.substInv` / 引理 `HasSubst.substInv`

English:
lemma HasSubst.substInv
  statement: HasSubst P.substInv
  proof: by simp [HasSubst, ← constantCoeff.eq_def]

@[deprecated (since := "2026-04-27")]
alias hasSubst_substInv := HasSubst.substInv

@[simp]

中文:
引理 有Subst.substInv
  结论: 有Subst P.substInv
  证明: by simp [HasSubst, ← constantCoeff.eq_def]

@[deprecated (since := "2026-04-27")]
alias hasSubst_substInv := HasSubst.substInv

@[simp]

Depends on / 依赖: HasSubst, constantCoeff, constantCoeff.eq_def, eq_def
-/
lemma HasSubst.substInv : HasSubst P.substInv := by simp [HasSubst, ← constantCoeff.eq_def]

@[deprecated (since := "2026-04-27")]
alias hasSubst_substInv := HasSubst.substInv

@[simp]
/--
lemma `coeff_one_substInv` / 引理 `coeff_one_substInv`

English:
lemma coeff_one_substInv
  statement: P.substInv.coeff 1 = ⅟(P.coeff 1)
  proof: by
  simp [substInv, substInvFun]

include hP in

中文:
引理 coeff_one_substInv
  结论: P.substInv.coeff 1 = ⅟(P.coeff 1)
  证明: by
  simp [substInv, substInvFun]

include hP in

Depends on / 依赖: substInv, substInvFun
-/
lemma coeff_one_substInv : P.substInv.coeff 1 = ⅟(P.coeff 1) := by
  simp [substInv, substInvFun]

include hP in
/--
lemma `subst_substInv_left` / 引理 `subst_substInv_left`

English:
lemma subst_substInv_left
  statement: P.substInv.subst P = X
  proof: by
  have : Invertible (P.substInv.coeff 1) := by simpa using invertibleInvOf
  let Q := P.substInv.substInv
  have hQ : HasSubst Q := HasSubst.substInv P.substInv
  have eq_aux : P.substInv.subst Q = X := subst_substInv_right P.substInv P.constantCoeff_substInv
  suffices h : Q = P from by simp_rw 

中文:
引理 subst_substInv_left
  结论: P.substInv.subst P = X
  证明: by
  have : Invertible (P.substInv.coeff 1) := by simpa using invertibleInvOf
  let Q := P.substInv.substInv
  have hQ : HasSubst Q := HasSubst.substInv P.substInv
  have eq_aux : P.substInv.subst Q = X := subst_substInv_right P.substInv P.constantCoeff_substInv
  suffices h : Q = P from by simp_rw 

Depends on / 依赖: HasSubst, HasSubst.substInv, Invertible, P.constantCoeff_substInv, P.subst, P.substInv, P.substInv.coeff, P.substInv.subst, P.substInv.substInv, PowerSeries, PowerSeries.subst, constantCoeff_substInv, eq_aux, invertibleInvOf, simp_rw, substInv, subst_X, subst_comp_subst_apply, subst_substInv_right
-/
lemma subst_substInv_left : P.substInv.subst P = X := by
  have : Invertible (P.substInv.coeff 1) := by simpa using invertibleInvOf
  let Q := P.substInv.substInv
  have hQ : HasSubst Q := HasSubst.substInv P.substInv
  have eq_aux : P.substInv.subst Q = X := subst_substInv_right P.substInv P.constantCoeff_substInv
  suffices h : Q = P from by simp_rw [← h, eq_aux]
  calc
    _ = PowerSeries.subst Q (P.subst P.substInv) := by
      rw [subst_substInv_right _ hP]; rw [subst_X hQ]
    _ = P := by
      simp [subst_comp_subst_apply (HasSubst.substInv P) hQ, eq_aux]

end Invertible

section IsUnit

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) (hP' : IsUnit (P.coeff 1))

/-- Given a power series `P = u • X + O(X²)` with `u` is an unit in ring `R`,
this is the power series `Q` such that `P(Q(X)) = X`.
See `PowerSeries.subst_substInvOfIsUnit_right`.

See also `PowerSeries.substInv` for a variant using `Invertible`. -/
noncomputable
/--
Definition of `substInvOfIsUnit` / `substInvOfIsUnit` 的定义

English:
definition substInvOfIsUnit
  signature: : PowerSeries R
  body: letI := hP'.invertible
  substInv P

中文:
定义 substInvOfIsUnit
  签名: : 幂级数 R
  定义体: letI := hP'.invertible
  substInv P

Depends on / 依赖: invertible, substInv
-/
def substInvOfIsUnit : PowerSeries R :=
  letI := hP'.invertible
  substInv P

/--
lemma `substInvOfIsUnit_eq_substInv` / 引理 `substInvOfIsUnit_eq_substInv`

English:
lemma substInvOfIsUnit_eq_substInv
  proof: hP'.invertible
    P.substInvOfIsUnit hP' = P.substInv := rfl

@[simp]

中文:
引理 substInvOfIsUnit_eq_substInv
  证明: hP'.invertible
    P.substInvOfIsUnit hP' = P.substInv := rfl

@[simp]

Depends on / 依赖: invertible
-/
lemma substInvOfIsUnit_eq_substInv :
    letI := hP'.invertible
    P.substInvOfIsUnit hP' = P.substInv := rfl

@[simp]
/--
lemma `constantCoeff_substInvOfIsUnit` / 引理 `constantCoeff_substInvOfIsUnit`

English:
lemma constantCoeff_substInvOfIsUnit
  statement: (P.substInvOfIsUnit hP').constantCoeff = 0
  proof: by
  simp [substInvOfIsUnit_eq_substInv]

中文:
引理 constantCoeff_substInvOfIsUnit
  结论: (P.substInvOfIsUnit hP').constantCoeff = 0
  证明: by
  simp [substInvOfIsUnit_eq_substInv]

Depends on / 依赖: substInvOfIsUnit_eq_substInv
-/
lemma constantCoeff_substInvOfIsUnit : (P.substInvOfIsUnit hP').constantCoeff = 0 := by
  simp [substInvOfIsUnit_eq_substInv]

/--
lemma `HasSubst.substInvOfIsUnit` / 引理 `HasSubst.substInvOfIsUnit`

English:
lemma HasSubst.substInvOfIsUnit
  statement: HasSubst (P.substInvOfIsUnit hP')
  proof: by
  simp [HasSubst, ← constantCoeff.eq_def]

@[simp]

中文:
引理 有Subst.substInvOfIsUnit
  结论: 有Subst (P.substInvOfIsUnit hP')
  证明: by
  simp [HasSubst, ← constantCoeff.eq_def]

@[simp]

Depends on / 依赖: HasSubst, constantCoeff, constantCoeff.eq_def, eq_def
-/
lemma HasSubst.substInvOfIsUnit : HasSubst (P.substInvOfIsUnit hP') := by
  simp [HasSubst, ← constantCoeff.eq_def]

@[simp]
/--
lemma `coeff_one_substInvOfIsUnit` / 引理 `coeff_one_substInvOfIsUnit`

English:
lemma coeff_one_substInvOfIsUnit
  statement: (P.substInvOfIsUnit hP').coeff 1 = hP'.unit⁻¹
  proof: by
  let := hP'.invertible
  rw [substInvOfIsUnit_eq_substInv]; rw [coeff_one_substInv]
  exact Units.mul_eq_one_iff_eq_inv.mp Invertible.invOf_mul_self

include hP in

中文:
引理 coeff_one_substInvOfIsUnit
  结论: (P.substInvOfIsUnit hP').coeff 1 = hP'.unit⁻¹
  证明: by
  let := hP'.invertible
  rw [substInvOfIsUnit_eq_substInv]; rw [coeff_one_substInv]
  exact Units.mul_eq_one_iff_eq_inv.mp Invertible.invOf_mul_self

include hP in

Depends on / 依赖: Invertible, Invertible.invOf_mul_self, Units.mul_eq_one_iff_eq_inv.mp, coeff_one_substInv, invOf_mul_self, invertible, mul_eq_one_iff_eq_inv, substInvOfIsUnit_eq_substInv
-/
lemma coeff_one_substInvOfIsUnit : (P.substInvOfIsUnit hP').coeff 1 = hP'.unit⁻¹ := by
  let := hP'.invertible
  rw [substInvOfIsUnit_eq_substInv]; rw [coeff_one_substInv]
  exact Units.mul_eq_one_iff_eq_inv.mp Invertible.invOf_mul_self

include hP in
/--
lemma `subst_substInvOfIsUnit_right` / 引理 `subst_substInvOfIsUnit_right`

English:
lemma subst_substInvOfIsUnit_right
  statement: P.subst (substInvOfIsUnit P hP') = X
  proof: by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_right hP]

include hP in

中文:
引理 subst_substInvOfIsUnit_right
  结论: P.subst (substInvOfIsUnit P hP') = X
  证明: by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_right hP]

include hP in

Depends on / 依赖: P.substInvOfIsUnit_eq_substInv, P.subst_substInv_right, invertible, substInvOfIsUnit_eq_substInv, subst_substInv_right
-/
lemma subst_substInvOfIsUnit_right : P.subst (substInvOfIsUnit P hP') = X := by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_right hP]

include hP in
/--
lemma `subst_substInvOfIsUnit_left` / 引理 `subst_substInvOfIsUnit_left`

English:
lemma subst_substInvOfIsUnit_left
  statement: (P.substInvOfIsUnit hP').subst P = X
  proof: by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_left hP]

中文:
引理 subst_substInvOfIsUnit_left
  结论: (P.substInvOfIsUnit hP').subst P = X
  证明: by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_left hP]

Depends on / 依赖: P.substInvOfIsUnit_eq_substInv, P.subst_substInv_left, invertible, substInvOfIsUnit_eq_substInv, subst_substInv_left
-/
lemma subst_substInvOfIsUnit_left : (P.substInvOfIsUnit hP').subst P = X := by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP']; rw [P.subst_substInv_left hP]

end IsUnit

end substInv

section

attribute [local instance] DiscreteTopology.instContinuousSMul

variable {x : Nat -> PowerSeries R} {a : MvPowerSeries τ S}
  [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/--
lemma `subst_tsum` / 引理 `subst_tsum`

English:
lemma subst_tsum
  given: (hx : Summable x) (ha : HasSubst a)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _]
  exact continuous_aeval _

中文:
引理 subst_tsum
  条件: (hx : Summable x) (ha : 有Subst a)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _]
  exact continuous_aeval _

Depends on / 依赖: coe_substAlgHom, continuous_aeval, hx.map_tsum, map_tsum, substAlgHom_eq_aeval
-/
lemma subst_tsum (hx : Summable x) (ha : HasSubst a) :
    (∑' i, x i).subst a = ∑' i, ((x i).subst a) := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]; rw [hx.map_tsum _]
  exact continuous_aeval _

/--
lemma `summable_subst` / 引理 `summable_subst`

English:
lemma summable_subst
  given: (hx : Summable x) (ha : HasSubst a)
  proof: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
  exact hx.map _ (continuous_aeval _)

中文:
引理 summable_subst
  条件: (hx : Summable x) (ha : 有Subst a)
  证明: by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
  exact hx.map _ (continuous_aeval _)

Depends on / 依赖: coe_substAlgHom, continuous_aeval, hx.map, substAlgHom_eq_aeval
-/
lemma summable_subst (hx : Summable x) (ha : HasSubst a) :
    Summable fun i => (x i).subst a := by
  rw [← coe_substAlgHom ha]; rw [substAlgHom_eq_aeval ha]
  exact hx.map _ (continuous_aeval _)

end

section Bivariate

open Finset Finsupp Nat

name_power_vars X₀, X₁ over R

/--
lemma `coeff_subst_X_zero_add_X_one` / 引理 `coeff_subst_X_zero_add_X_one`

English:
lemma coeff_subst_X_zero_add_X_one
  given: (f : R⟦X⟧) (e : Fin 2 ->₀ Nat)
  proof: by
  rw [PowerSeries.subst]; rw [MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp_rw [Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
  

中文:
引理 coeff_subst_X_zero_add_X_one
  条件: (f : R⟦X⟧) (e : 有限集 2 ->₀ 自然数)
  证明: by
  rw [PowerSeries.subst]; rw [MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp_rw [Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
  

Depends on / 依赖: Finsupp, Finsupp.prod_pow, MvPolynomial, MvPolynomial.coe_X, MvPolynomial.coe_add, MvPolynomial.coe_pow, MvPolynomial.coeff_add_pow, MvPolynomial.coeff_coe, MvPowerSeries, MvPowerSeries.coeff_subst, MvPowerSeries.hasSubst_of_constantCoeff_zero, PUnit.default_eq_unit, PowerSeries, PowerSeries.subst, cast_ite, coe_X, coe_add, coe_pow, coeff_add_pow, coeff_coe
-/
lemma coeff_subst_X_zero_add_X_one (f : R⟦X⟧) (e : Fin 2 ->₀ Nat) :
    MvPowerSeries.coeff e (subst (X₀ + X₁) f) =
      (e 0 + e 1).choose (e 0) * coeff (e 0 + e 1) f := by
  rw [PowerSeries.subst]; rw [MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp_rw [Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  rw [finsum_eq_single _ (single () (e 0 + e 1))]; rw [mul_comm]
  · simp [MvPolynomial.coeff_add_pow, coeff]
  · simp only [MvPolynomial.coeff_add_pow, mem_antidiagonal, cast_ite]
    grind

/--
lemma `coeff_subst_X_zero_subst_mul_X_one` / 引理 `coeff_subst_X_zero_subst_mul_X_one`

English:
lemma coeff_subst_X_zero_subst_mul_X_one
  given: (f : R⟦X⟧) (e : Fin 2 ->₀ Nat)
  proof: by
  rw [MvPowerSeries.coeff_mul]; rw [Finset.sum_eq_single (single 0 (e 0)]; rw [single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq

中文:
引理 coeff_subst_X_zero_subst_mul_X_one
  条件: (f : R⟦X⟧) (e : 有限集 2 ->₀ 自然数)
  证明: by
  rw [MvPowerSeries.coeff_mul]; rw [Finset.sum_eq_single (single 0 (e 0)]; rw [single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq

Depends on / 依赖: Fin.isValue, Finset, Finset.sum_eq_single, MvPowerSeries, MvPowerSeries.coeff_mul, Prod.ext_iff, S.proj_surjective, coeff_mul, coeff_subst_single, epi_iff_surjective, exists_prop, ext_iff, fin_case, hmul_ne_zero, isValue, ite_eq_right_iff, mem_antidiagonal, mem_antidiagonal.mp, ne_eq, ne_zero_and_ne_zero_of_mul
-/
lemma coeff_subst_X_zero_subst_mul_X_one (f : R⟦X⟧) (e : Fin 2 ->₀ Nat) :
    MvPowerSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f := by
  rw [MvPowerSeries.coeff_mul]; rw [Finset.sum_eq_single (single 0 (e 0)]; rw [single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff]; rw [← mem_antidiagonal.mp hb]; rw [h0.1]; rw [h1.1]
    simp
  · intro he
    have he' : single 0 (e 0) + single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp
    exact absurd (mem_antidiagonal.mpr he') he

end Bivariate

end PowerSeries
