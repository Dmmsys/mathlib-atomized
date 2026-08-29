/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Wenrong Zou
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings and
is patterned after `Mathlib/Algebra/MvPolynomial/Equiv.lean`.

* `MvPowerSeries.isEmptyEquiv` : The isomorphism between multivariable power series
  in no variables and the ground ring.

* `MvPowerSeries.optionEquivLeft` : The isomorphism between multivariable power series
  in `Option σ` and power series with coefficients in `MvPowerSeries σ R`.

* `MvPowerSeries.finSuccEquiv` : The isomorphism between multivariable power series
  in `Fin (n + 1)` and power series over multivariable power series in `Fin n`.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials
  with respect to the ideal spanned by all variables when the index is finite.

-/

@[expose] public section

noncomputable section

open Finsupp Finset Function

namespace MvPowerSeries

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

section isEmptyEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in no variables and the ground ring. -/
@[simps!]
/--
Definition of `isEmptyEquiv` / `isEmptyEquiv` 的定义

English:
definition isEmptyEquiv
  signature: [IsEmpty σ]
  body: constantCoeff
  invFun := C
  left_inv _ := by ext x; simp [Subsingleton.eq_zero x]
  commutes' _ := rfl

中文:
定义 isEmptyEquiv
  签名: [是空 σ]
  定义体: constantCoeff
  invFun := C
  left_inv _ := by ext x; simp [Subsingleton.eq_zero x]
  commutes' _ := rfl

Depends on / 依赖: constantCoeff
-/
def isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where
  __ := constantCoeff
  invFun := C
  left_inv _ := by ext x; simp [Subsingleton.eq_zero x]
  commutes' _ := rfl

end isEmptyEquiv

section optionEquivLeft

variable (R σ) in
/--
Definition of `optionFunLeft` / `optionFunLeft` 的定义

English:
definition optionFunLeft
  signature: (p : MvPowerSeries (Option σ) R)
  body: .mk fun n x => p.coeff (x.optionElim n)

中文:
定义 optionFunLeft
  签名: (p : MvPowerSeries (选项类型 σ) R)
  定义体: .mk fun n x => p.coeff (x.optionElim n)
-/
private def optionFunLeft (p : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  .mk fun n x => p.coeff (x.optionElim n)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coeff_coeff_optionFunLeft` / 引理 `coeff_coeff_optionFunLeft`

English:
lemma coeff_coeff_optionFunLeft
  given: (p : MvPowerSeries (Option σ) R) (n : Nat) (x : σ ->₀ Nat)
  proof: by
  rw [optionFunLeft]; rw [PowerSeries.coeff_mk]
  exact LinearMap.proj_apply ..

中文:
引理 coeff_coeff_optionFunLeft
  条件: (p : MvPowerSeries (选项类型 σ) R) (n : 自然数) (x : σ ->₀ 自然数)
  证明: by
  rw [optionFunLeft]; rw [PowerSeries.coeff_mk]
  exact LinearMap.proj_apply ..
-/
private lemma coeff_coeff_optionFunLeft (p : MvPowerSeries (Option σ) R) (n : Nat) (x : σ ->₀ Nat) :
    coeff x (PowerSeries.coeff n (optionFunLeft σ R p)) = coeff (x.optionElim n) p := by
  rw [optionFunLeft]; rw [PowerSeries.coeff_mk]
  exact LinearMap.proj_apply ..

/--
theorem `optionFunLeft_monomial` / 定理 `optionFunLeft_monomial`

English:
theorem optionFunLeft_monomial
  given: (x : Option σ ->₀ Nat) (r : R)
  proof: by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial]; rw [coeff_coeff_optionFunLeft]; rw [coeff_monomial]
  split_ifs with h1 h2 h3
  · simp [← h1]
  · absurd h2
    rw [← optionElim_apply_none n]; rw [h1]
  · replace h1 : ¬ y = x.some := fun h => by
      absurd h1; ext u
      cases u <;> simp_all
    rw [coeff_monomial]; rw [if_neg h1]
  · rw [coeff_zero]

中文:
定理 optionFunLeft_monomial
  条件: (x : 选项类型 σ ->₀ 自然数) (r : R)
  证明: by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial]; rw [coeff_coeff_optionFunLeft]; rw [coeff_monomial]
  split_ifs with h1 h2 h3
  · simp [← h1]
  · absurd h2
    rw [← optionElim_apply_none n]; rw [h1]
  · replace h1 : ¬ y = x.some := fun h => by
      absurd h1; ext u
      cases u <;> simp_all
    rw [coeff_monomial]; rw [if_neg h1]
  · rw [coeff_zero]
-/
private theorem optionFunLeft_monomial (x : Option σ ->₀ Nat) (r : R) :
    optionFunLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) := by
  classical
  ext n y
  rw [PowerSeries.coeff_monomial]; rw [coeff_coeff_optionFunLeft]; rw [coeff_monomial]
  split_ifs with h1 h2 h3
  · simp [← h1]
  · absurd h2
    rw [← optionElim_apply_none n]; rw [h1]
  · replace h1 : ¬ y = x.some := fun h => by
      absurd h1; ext u
      cases u <;> simp_all
    rw [coeff_monomial]; rw [if_neg h1]
  · rw [coeff_zero]

/--
lemma `optionFunLeft_mul` / 引理 `optionFunLeft_mul`

English:
lemma optionFunLeft_mul
  given: (p q : MvPowerSeries (Option σ) R)
  proof: by
  classical
  ext k x
  simp only [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum, sum_sigma']
  refine sum_bij (fun y _ => ⟨(y.1 none, y.2 none), (y.1.some, y.2.some)⟩) ?_ ?_ ?_ ?_
  · intros; simp_all [Finsupp.ext_iff]
  · intros; ext t <;> cases t
    all_goals simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨m, n⟩, ⟨u, v⟩⟩ h
    suffices exists a b, (a none = m ∧ b none = n) ∧ a.some = u ∧ a + b = optionElim k x ∧
      b.some = v by simpa
    use u.optionElim m, v.optionElim n
    suffices optionElim m u + optionElim n v = optionElim k x by simp_all
    ext t; cases t <;> simp_all [Finsupp.ext_iff]
  · intros; simp_all [Finsupp.ext_iff]

中文:
引理 optionFunLeft_mul
  条件: (p q : MvPowerSeries (选项类型 σ) R)
  证明: by
  classical
  ext k x
  simp only [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum, sum_sigma']
  refine sum_bij (fun y _ => ⟨(y.1 none, y.2 none), (y.1.some, y.2.some)⟩) ?_ ?_ ?_ ?_
  · intros; simp_all [Finsupp.ext_iff]
  · intros; ext t <;> cases t
    all_goals simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨m, n⟩, ⟨u, v⟩⟩ h
    suffices exists a b, (a none = m ∧ b none = n) ∧ a.some = u ∧ a + b = optionElim k x ∧
      b.some = v by simpa
    use u.optionElim m, v.optionElim n
    suffices optionElim m u + optionElim n v = optionElim k x by simp_all
    ext t; cases t <;> simp_all [Finsupp.ext_iff]
  · intros; simp_all [Finsupp.ext_iff]
-/
private lemma optionFunLeft_mul (p q : MvPowerSeries (Option σ) R) :
    optionFunLeft σ R (p * q) = optionFunLeft σ R p * optionFunLeft σ R q := by
  classical
  ext k x
  simp only [coeff_coeff_optionFunLeft, coeff_mul, PowerSeries.coeff_mul, map_sum, sum_sigma']
  refine sum_bij (fun y _ => ⟨(y.1 none, y.2 none), (y.1.some, y.2.some)⟩) ?_ ?_ ?_ ?_
  · intros; simp_all [Finsupp.ext_iff]
  · intros; ext t <;> cases t
    all_goals simp_all [Finsupp.ext_iff]
  · rintro ⟨⟨m, n⟩, ⟨u, v⟩⟩ h
    suffices exists a b, (a none = m ∧ b none = n) ∧ a.some = u ∧ a + b = optionElim k x ∧
      b.some = v by simpa
    use u.optionElim m, v.optionElim n
    suffices optionElim m u + optionElim n v = optionElim k x by simp_all
    ext t; cases t <;> simp_all [Finsupp.ext_iff]
  · intros; simp_all [Finsupp.ext_iff]

variable (R σ) in
/--
Definition of `optionInvFunLeft` / `optionInvFunLeft` 的定义

English:
definition optionInvFunLeft
  signature: (p : PowerSeries (MvPowerSeries σ R))
  body: fun x => (p.coeff (x none)).coeff x.some

中文:
定义 optionInvFunLeft
  签名: (p : 幂级数 (MvPowerSeries σ R))
  定义体: fun x => (p.coeff (x none)).coeff x.some
-/
private def optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) :
    MvPowerSeries (Option σ) R := fun x => (p.coeff (x none)).coeff x.some

/--
lemma `coeff_optionInvFunLeft` / 引理 `coeff_optionInvFunLeft`

English:
lemma coeff_optionInvFunLeft
  given: (p : PowerSeries (MvPowerSeries σ R)) (x : Option σ ->₀ Nat)
  proof: rfl

中文:
引理 coeff_optionInvFunLeft
  条件: (p : 幂级数 (MvPowerSeries σ R)) (x : 选项类型 σ ->₀ 自然数)
  证明: rfl
-/
private lemma coeff_optionInvFunLeft (p : PowerSeries (MvPowerSeries σ R)) (x : Option σ ->₀ Nat) :
    coeff x (optionInvFunLeft σ R p) = (p.coeff (x none)).coeff x.some := rfl

variable (R σ) in
/-- The algebra isomorphism between multivariable power series in `Option σ` and
  power series with coefficients in `MvPowerSeries σ R`. -/
@[no_expose]
/--
Definition of `optionEquivLeft` / `optionEquivLeft` 的定义

English:
definition optionEquivLeft
  signature: : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) where
  body: optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ ->₀ Nat)

中文:
定义 optionEquivLeft
  签名: : MvPowerSeries (选项类型 σ) R ≃ₐ[R] 幂级数 (MvPowerSeries σ R) where
  定义体: optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ ->₀ Nat)

Depends on / 依赖: optionFunLeft
-/
def optionEquivLeft : MvPowerSeries (Option σ) R ≃ₐ[R] PowerSeries (MvPowerSeries σ R) where
  toFun := optionFunLeft σ R
  invFun := optionInvFunLeft σ R
  left_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  right_inv _ := by ext; simp [coeff_optionInvFunLeft, coeff_coeff_optionFunLeft]
  map_mul' := optionFunLeft_mul
  map_add' _ _ := by ext; simp [coeff_coeff_optionFunLeft]
  commutes' := by
    simpa [MvPowerSeries.algebraMap_apply, PowerSeries.C] using
      optionFunLeft_monomial (0 : Option σ ->₀ Nat)

/--
lemma `coeff_coeff_optionEquivLeft` / 引理 `coeff_coeff_optionEquivLeft`

English:
lemma coeff_coeff_optionEquivLeft
  given: (p : MvPowerSeries (Option σ) R) (n : Nat) (x : σ ->₀ Nat)
  proof: coeff_coeff_optionFunLeft ..

中文:
引理 coeff_coeff_optionEquivLeft
  条件: (p : MvPowerSeries (选项类型 σ) R) (n : 自然数) (x : σ ->₀ 自然数)
  证明: coeff_coeff_optionFunLeft ..

Depends on / 依赖: coeff_coeff_optionFunLeft
-/
lemma coeff_coeff_optionEquivLeft (p : MvPowerSeries (Option σ) R) (n : Nat) (x : σ ->₀ Nat) :
    coeff x (PowerSeries.coeff n (optionEquivLeft σ R p)) = coeff (x.optionElim n) p :=
  coeff_coeff_optionFunLeft ..

/--
theorem `optionEquivLeft_monomial` / 定理 `optionEquivLeft_monomial`

English:
theorem optionEquivLeft_monomial
  given: (x : Option σ ->₀ Nat) (r : R)
  proof: optionFunLeft_monomial ..

@[simp]

中文:
定理 optionEquivLeft_monomial
  条件: (x : 选项类型 σ ->₀ 自然数) (r : R)
  证明: optionFunLeft_monomial ..

@[simp]

Depends on / 依赖: optionFunLeft_monomial
-/
theorem optionEquivLeft_monomial (x : Option σ ->₀ Nat) (r : R) :
    optionEquivLeft σ R (monomial x r) = PowerSeries.monomial (x none) (monomial x.some r) :=
  optionFunLeft_monomial ..

@[simp]
/--
lemma `optionEquivLeft_X_some` / 引理 `optionEquivLeft_X_some`

English:
lemma optionEquivLeft_X_some
  given: (i : σ)
  proof: by
  have : (optionElim 0 (single i 1)) = single (Option.some i) 1 := by
    classical
    ext a; cases a <;> simp [single_apply]
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow, this] using
    optionEquivLeft_monomial (single (Option.some i) 1 : Option σ ->₀ Nat) (1 : R)

@[simp]

中文:
引理 optionEquivLeft_X_some
  条件: (i : σ)
  证明: by
  have : (optionElim 0 (single i 1)) = single (Option.some i) 1 := by
    classical
    ext a; cases a <;> simp [single_apply]
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow, this] using
    optionEquivLeft_monomial (single (Option.some i) 1 : Option σ ->₀ Nat) (1 : R)

@[simp]

Depends on / 依赖: Option.some, PowerSeries, PowerSeries.monomial_eq_C_mul_X_pow, X_def, classical, monomial_eq_C_mul_X_pow, optionElim, optionEquivLeft_monomial, single, single_apply
-/
lemma optionEquivLeft_X_some (i : σ) :
    optionEquivLeft σ R (X (Option.some i)) = (PowerSeries.C (X i)) := by
  have : (optionElim 0 (single i 1)) = single (Option.some i) 1 := by
    classical
    ext a; cases a <;> simp [single_apply]
  simpa [← X_def, PowerSeries.monomial_eq_C_mul_X_pow, this] using
    optionEquivLeft_monomial (single (Option.some i) 1 : Option σ ->₀ Nat) (1 : R)

@[simp]
/--
lemma `optionEquivLeft_X_none` / 引理 `optionEquivLeft_X_none`

English:
lemma optionEquivLeft_X_none
  statement: optionEquivLeft σ R (X none) = PowerSeries.X
  proof: by
  simpa [PowerSeries.monomial_eq_C_mul_X_pow, ← X_def] using
    optionEquivLeft_monomial (single none 1 : Option σ ->₀ Nat) (1 : R)

@[simp]

中文:
引理 optionEquivLeft_X_none
  结论: optionEquivLeft σ R (X none) = 幂级数.X
  证明: by
  simpa [PowerSeries.monomial_eq_C_mul_X_pow, ← X_def] using
    optionEquivLeft_monomial (single none 1 : Option σ ->₀ Nat) (1 : R)

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.monomial_eq_C_mul_X_pow, X_def, monomial_eq_C_mul_X_pow, optionEquivLeft_monomial, single
-/
lemma optionEquivLeft_X_none : optionEquivLeft σ R (X none) = PowerSeries.X := by
  simpa [PowerSeries.monomial_eq_C_mul_X_pow, ← X_def] using
    optionEquivLeft_monomial (single none 1 : Option σ ->₀ Nat) (1 : R)

@[simp]
/--
lemma `optionEquivLeft_C` / 引理 `optionEquivLeft_C`

English:
lemma optionEquivLeft_C
  given: (r : R)
  statement: (optionEquivLeft σ R) (C r) = PowerSeries.C (C r)
  proof: by
  simpa using optionEquivLeft_monomial (0 : Option σ ->₀ Nat) (r : R)

中文:
引理 optionEquivLeft_C
  条件: (r : R)
  结论: (optionEquivLeft σ R) (C r) = 幂级数.C (C r)
  证明: by
  simpa using optionEquivLeft_monomial (0 : Option σ ->₀ Nat) (r : R)

Depends on / 依赖: optionEquivLeft_monomial
-/
lemma optionEquivLeft_C (r : R) : (optionEquivLeft σ R) (C r) = PowerSeries.C (C r) := by
  simpa using optionEquivLeft_monomial (0 : Option σ ->₀ Nat) (r : R)

end optionEquivLeft

section finSuccEquiv

variable {n : Nat}

/--
lemma `embDomain_finSuccEquiv_cons` / 引理 `embDomain_finSuccEquiv_cons`

English:
lemma embDomain_finSuccEquiv_cons
  statement: {M : Type*} [AddCommMonoid M] {n : Nat} (i : M)
  proof: by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]

中文:
引理 embDomain_finSuccEquiv_cons
  结论: {M : 类型} [加法交换幺半群 M] {n : 自然数} (i : M)
  证明: by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]
-/
private lemma embDomain_finSuccEquiv_cons {M : Type*} [AddCommMonoid M] {n : Nat} (i : M)
    (x : Fin n ->₀ M) : embDomain (finSuccEquiv n).toEmbedding (cons i x) = optionElim i x := by
  ext a; cases a <;> simp [embDomain_eq_mapDomain]

variable (n R) in
/--
Definition of `finSuccEquiv` / `finSuccEquiv` 的定义

English:
definition finSuccEquiv
  signature: : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R)
  body: (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)

中文:
定义 finSuccEquiv
  签名: : MvPowerSeries (有限集 (n + 1)) R ≃ₐ[R] 幂级数 (MvPowerSeries (有限集 n) R)
  定义体: (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)

Depends on / 依赖: _root_, _root_.finSuccEquiv, finSuccEquiv, optionEquivLeft, renameEquiv
-/
def finSuccEquiv : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft (Fin n) R)

/--
theorem `coeff_coeff_finSuccEquiv` / 定理 `coeff_coeff_finSuccEquiv`

English:
theorem coeff_coeff_finSuccEquiv
  given: (p : MvPowerSeries (Fin (n + 1)) R) {k : Nat} {x : Fin n ->₀ Nat}
  proof: by
  suffices coeff x (PowerSeries.coeff k (optionEquivLeft (Fin n) R
    (rename (_root_.finSuccEquiv n) p))) = coeff (Finsupp.cons k x) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft, ← embDomain_finSuccEquiv_cons,
    coeff_embDomain_rename]

@[simp]

中文:
定理 coeff_coeff_finSuccEquiv
  条件: (p : MvPowerSeries (有限集 (n + 1)) R) {k : 自然数} {x : 有限集 n ->₀ 自然数}
  证明: by
  suffices coeff x (PowerSeries.coeff k (optionEquivLeft (Fin n) R
    (rename (_root_.finSuccEquiv n) p))) = coeff (Finsupp.cons k x) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft, ← embDomain_finSuccEquiv_cons,
    coeff_embDomain_rename]

@[simp]

Depends on / 依赖: Equiv.coe_toEmbedding, Finsupp, Finsupp.cons, PowerSeries, PowerSeries.coeff, _root_, _root_.finSuccEquiv, coe_toEmbedding, coeff_coeff_optionEquivLeft, coeff_embDomain_rename, embDomain_finSuccEquiv_cons, finSuccEquiv, optionEquivLeft, simp_rw
-/
theorem coeff_coeff_finSuccEquiv (p : MvPowerSeries (Fin (n + 1)) R) {k : Nat} {x : Fin n ->₀ Nat} :
    coeff x (PowerSeries.coeff k (finSuccEquiv R n p)) = coeff (x.cons k) p := by
  suffices coeff x (PowerSeries.coeff k (optionEquivLeft (Fin n) R
    (rename (_root_.finSuccEquiv n) p))) = coeff (Finsupp.cons k x) p by simpa [finSuccEquiv]
  simp_rw [← Equiv.coe_toEmbedding, coeff_coeff_optionEquivLeft, ← embDomain_finSuccEquiv_cons,
    coeff_embDomain_rename]

@[simp]
/--
theorem `finSuccEquiv_X_zero` / 定理 `finSuccEquiv_X_zero`

English:
theorem finSuccEquiv_X_zero
  statement: finSuccEquiv R n (X 0) = .X
  proof: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X, cons_eq_single_zero_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_one, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]

中文:
定理 finSuccEquiv_X_zero
  结论: finSuccEquiv R n (X 0) = .X
  证明: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X, cons_eq_single_zero_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_one, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_X, coeff_X, coeff_coeff_finSuccEquiv, coeff_one, coeff_zero, cons_eq_single_zero_iff, h1.left, if_neg, simp_rw, split_ifs
-/
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = .X := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_X, coeff_X, cons_eq_single_zero_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_one, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
/--
theorem `finSuccEquiv_X_succ` / 定理 `finSuccEquiv_X_succ`

English:
theorem finSuccEquiv_X_succ
  given: (j : Fin n)
  statement: finSuccEquiv R n (X j.succ) = .C (X j)
  proof: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X, cons_eq_single_succ_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_X, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]

中文:
定理 finSuccEquiv_X_succ
  条件: (j : 有限集 n)
  结论: finSuccEquiv R n (X j.succ) = .C (X j)
  证明: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X, cons_eq_single_succ_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_X, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_C, coeff_C, coeff_X, coeff_coeff_finSuccEquiv, coeff_zero, cons_eq_single_succ_iff, h1.left, if_neg, simp_rw, split_ifs
-/
theorem finSuccEquiv_X_succ (j : Fin n) : finSuccEquiv R n (X j.succ) = .C (X j) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_X, cons_eq_single_succ_iff]
  split_ifs with h1 h2 h3
  · simp [h1.left]
  · tauto
  · rw [coeff_X, if_neg (by tauto)]
  · rw [coeff_zero]

@[simp]
/--
theorem `finSuccEquiv_C` / 定理 `finSuccEquiv_C`

English:
theorem finSuccEquiv_C
  given: (r : R)
  statement: (finSuccEquiv R n) (C r) = PowerSeries.C (C r)
  proof: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_C, ← cons_zero_zero,
    cons_injective2.eq_iff]
  split_ifs with h1 h2 h3
  · simp [h1.right]
  · tauto
  · rw [coeff_C, if_neg (by tauto)]
  · rw [coeff_zero]

中文:
定理 finSuccEquiv_C
  条件: (r : R)
  结论: (finSuccEquiv R n) (C r) = 幂级数.C (C r)
  证明: by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_C, ← cons_zero_zero,
    cons_injective2.eq_iff]
  split_ifs with h1 h2 h3
  · simp [h1.right]
  · tauto
  · rw [coeff_C, if_neg (by tauto)]
  · rw [coeff_zero]

Depends on / 依赖: PowerSeries, PowerSeries.coeff_C, coeff_C, coeff_coeff_finSuccEquiv, coeff_zero, cons_injective2, cons_injective2.eq_iff, cons_zero_zero, eq_iff, h1.right, if_neg, simp_rw, split_ifs
-/
theorem finSuccEquiv_C (r : R) : (finSuccEquiv R n) (C r) = PowerSeries.C (C r) := by
  ext k x
  simp_rw [coeff_coeff_finSuccEquiv, PowerSeries.coeff_C, coeff_C, ← cons_zero_zero,
    cons_injective2.eq_iff]
  split_ifs with h1 h2 h3
  · simp [h1.right]
  · tauto
  · rw [coeff_C, if_neg (by tauto)]
  · rw [coeff_zero]

/--
theorem `finSuccEquiv_comp_C` / 定理 `finSuccEquiv_comp_C`

English:
theorem finSuccEquiv_comp_C
  statement: (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
  proof: by
  ext1; simp [AlgEquiv.symm_apply_eq]

中文:
定理 finSuccEquiv_comp_C
  结论: (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
  证明: by
  ext1; simp [AlgEquiv.symm_apply_eq]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_eq, symm_apply_eq
-/
theorem finSuccEquiv_comp_C : (MvPowerSeries.finSuccEquiv R n).symm.toRingHom.comp
    (PowerSeries.C.comp MvPowerSeries.C) = MvPowerSeries.C := by
  ext1; simp [AlgEquiv.symm_apply_eq]

variable (S : Type*) [CommRing S] [IsNoetherianRing S]

/--
lemma `isNoetherianRing_fin` / 引理 `isNoetherianRing_fin`

English:
lemma isNoetherianRing_fin
  given: (n : Nat)
  statement: IsNoetherianRing (MvPowerSeries (Fin n) S)
  proof: by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv S (isEmptyEquiv (Fin 0) S).toRingEquiv.symm
  | succ n _ =>
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) S))
      (finSuccEquiv S n).toRingEquiv.symm

中文:
引理 isNoetherianRing_fin
  条件: (n : 自然数)
  结论: 是Noether环 (MvPowerSeries (有限集 n) S)
  证明: by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv S (isEmptyEquiv (Fin 0) S).toRingEquiv.symm
  | succ n _ =>
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) S))
      (finSuccEquiv S n).toRingEquiv.symm

Depends on / 依赖: convolution, hfg.tsum_add, tsum_add
-/
private lemma isNoetherianRing_fin (n : Nat) : IsNoetherianRing (MvPowerSeries (Fin n) S) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv S (isEmptyEquiv (Fin 0) S).toRingEquiv.symm
  | succ n _ =>
    exact isNoetherianRing_of_ringEquiv (PowerSeries (MvPowerSeries (Fin n) S))
      (finSuccEquiv S n).toRingEquiv.symm

/--
Instance `isNoetherianRing` / 实例 `isNoetherianRing`

English:
instance isNoetherianRing
  signature: [Finite σ]
  body: by
  cases nonempty_fintype σ
  have := isNoetherianRing_fin S (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) S)
    (renameEquiv S (Fintype.equivFin σ)).toRingEquiv.symm

中文:
实例 isNoetherianRing
  签名: [有限 σ]
  定义体: by
  cases nonempty_fintype σ
  have := isNoetherianRing_fin S (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) S)
    (renameEquiv S (Fintype.equivFin σ)).toRingEquiv.symm

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivFin, MvPowerSeries, distrib_add, equivFin, isNoetherianRing_fin, isNoetherianRing_of_ringEquiv, nonempty_fintype, renameEquiv, toRingEquiv, toRingEquiv.symm
-/
instance isNoetherianRing [Finite σ] : IsNoetherianRing (MvPowerSeries σ S) := by
  cases nonempty_fintype σ
  have := isNoetherianRing_fin S (Fintype.card σ)
  exact isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin (Fintype.card σ)) S)
    (renameEquiv S (Fintype.equivFin σ)).toRingEquiv.symm

end finSuccEquiv

end CommSemiring

section toAdicCompletion

open Finsupp

variable {σ R : Type*} {n : Nat} [CommRing R] [Finite σ]

/--
lemma `truncTotal_sub_truncTotal_mem_pow_idealOfVars` / 引理 `truncTotal_sub_truncTotal_mem_pow_idealOfVars`

English:
lemma truncTotal_sub_truncTotal_mem_pow_idealOfVars
  statement: {l m n : Nat} (h : l <= m) (h' : l <= n)
  proof: by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ (by lia)]; rw [coeff_truncTotal _ (by lia)]

中文:
引理 truncTotal_sub_truncTotal_mem_pow_idealOfVars
  结论: {l m n : 自然数} (h : l <= m) (h' : l <= n)
  证明: by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ (by lia)]; rw [coeff_truncTotal _ (by lia)]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sub, MvPolynomial.mem_pow_idealOfVars_iff, coeff_sub, coeff_truncTotal, convolution, hfg.tsum_add, mem_pow_idealOfVars_iff, sub_eq_zero, tsum_add
-/
lemma truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : Nat} (h : l <= m) (h' : l <= n)
    (p : MvPowerSeries σ R) : p.truncTotal m - p.truncTotal n in
      MvPolynomial.idealOfVars σ R ^ l := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ (by lia)]; rw [coeff_truncTotal _ (by lia)]

/--
lemma `truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars` / 引理 `truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars`

English:
lemma truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars
  given: (p q : MvPowerSeries σ R)
  proof: by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ hx]; rw [coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

中文:
引理 truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars
  条件: (p q : MvPowerSeries σ R)
  证明: by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ hx]; rw [coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_sub, MvPolynomial.mem_pow_idealOfVars_iff, add_distrib, coeff_sub, coeff_truncTotal, coeff_truncTotal_mul_truncTotal_eq_coeff_mul, mem_pow_idealOfVars_iff, sub_eq_zero
-/
lemma truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries σ R) :
    (p * q).truncTotal n - p.truncTotal n * q.truncTotal n in
      MvPolynomial.idealOfVars σ R ^ n := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx => ?_)
  rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ hx]; rw [coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

/-- The canonical map induced by `truncTotal` from multivariate power series to
the quotient ring of multivariate polynomials by the `n`-th power of
the ideal spanned by all variables. -/
@[simps]
/--
Definition of `truncTotalAlgHom` / `truncTotalAlgHom` 的定义

English:
definition truncTotalAlgHom
  signature: (σ R : Type*) [Finite σ] [CommRing R] (n : Nat)
  body: truncTotal n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h]; rw [map_one]
  map_mul' p q := by
    rw [← map_mul]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq]; rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ h]; rw [MvPolynomial.coeff_coe]

中文:
定义 truncTotalAlgHom
  签名: (σ R : 类型) [有限 σ] [交换环 R] (n : 自然数)
  定义体: truncTotal n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h]; rw [map_one]
  map_mul' p q := by
    rw [← map_mul]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq]; rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ h]; rw [MvPolynomial.coeff_coe]

Depends on / 依赖: truncTotal
-/
def truncTotalAlgHom (σ R : Type*) [Finite σ] [CommRing R] (n : Nat) :
    MvPowerSeries σ R ->ₐ[MvPolynomial σ R]
      MvPolynomial σ R ⧸ (MvPolynomial.idealOfVars σ R) ^ n where
  toFun p := truncTotal n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h]; rw [map_one]
  map_mul' p q := by
    rw [← map_mul]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq]; rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub]; rw [sub_eq_zero]; rw [coeff_truncTotal _ h]; rw [MvPolynomial.coeff_coe]

/--
Definition of `toAdicCompletion` / `toAdicCompletion` 的定义

English:
definition toAdicCompletion
  signature: (σ R : Type*) [Finite σ] [CommRing R]
  body: AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h => AlgHom.ext fun _ => by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)

中文:
定义 toAdicCompletion
  签名: (σ R : 类型) [有限 σ] [交换环 R]
  定义体: AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h => AlgHom.ext fun _ => by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)

Depends on / 依赖: AdicCompletion, AdicCompletion.liftAlgHom, AlgHom, AlgHom.ext, Ideal.Quotient.mk_eq_mk_iff_sub_mem, MvPolynomial, MvPolynomial.idealOfVars, Quotient, idealOfVars, le_refl, liftAlgHom, mk_eq_mk_iff_sub_mem, truncTotalAlgHom, truncTotal_sub_truncTotal_mem_pow_idealOfVars
-/
def toAdicCompletion (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R ->ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) :=
  AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h => AlgHom.ext fun _ => by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)

/--
lemma `toAdicCompletion_apply_eq_mk_truncTotal` / 引理 `toAdicCompletion_apply_eq_mk_truncTotal`

English:
lemma toAdicCompletion_apply_eq_mk_truncTotal
  given: {n : Nat} {p : MvPowerSeries σ R}
  proof: by rfl

中文:
引理 toAdicCompletion_apply_eq_mk_truncTotal
  条件: {n : 自然数} {p : MvPowerSeries σ R}
  证明: by rfl
-/
lemma toAdicCompletion_apply_eq_mk_truncTotal {n : Nat} {p : MvPowerSeries σ R} :
    (toAdicCompletion σ R p).val n = truncTotal n p := by rfl

/--
theorem `coeff_toAdicCompletion_val_apply_out` / 定理 `coeff_toAdicCompletion_val_apply_out`

English:
theorem coeff_toAdicCompletion_val_apply_out
  statement: {x : σ ->₀ Nat} {p : MvPowerSeries σ R} {n : Nat}
  proof: by
  rw [← coeff_truncTotal _ hx]; rw [← sub_eq_zero]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

中文:
定理 coeff_toAdicCompletion_val_apply_out
  结论: {x : σ ->₀ 自然数} {p : MvPowerSeries σ R} {n : 自然数}
  证明: by
  rw [← coeff_truncTotal _ hx]; rw [← sub_eq_zero]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

Depends on / 依赖: Ideal.Quotient.eq, Ideal.Quotient.mk_out, Ideal.mul_top, MvPolynomial, MvPolynomial.coeff_sub, MvPolynomial.idealOfVars, MvPolynomial.mem_pow_idealOfVars_iff, Quotient, coeff_sub, coeff_truncTotal, idealOfVars, mem_pow_idealOfVars_iff, mk_out, mul_top, nth_rw, smul_eq_mul, sub_eq_zero, toAdicCompletion_apply_eq_mk_truncTotal
-/
theorem coeff_toAdicCompletion_val_apply_out {x : σ ->₀ Nat} {p : MvPowerSeries σ R} {n : Nat}
    (hx : degree x < n) : (Quotient.out (((toAdicCompletion σ R) p).val n)).coeff x =
      (coeff x) p := by
  rw [← coeff_truncTotal _ hx]; rw [← sub_eq_zero]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toAdicCompletion_coe` / 定理 `toAdicCompletion_coe`

English:
theorem toAdicCompletion_coe
  given: (p : MvPolynomial σ R)
  proof: by
  symm; ext n
  suffices p - (truncTotal n) p in MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx => by simp [coeff_truncTotal _ hx]

中文:
定理 toAdicCompletion_coe
  条件: (p : 多元多项式 σ R)
  证明: by
  symm; ext n
  suffices p - (truncTotal n) p in MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx => by simp [coeff_truncTotal _ hx]

Depends on / 依赖: AdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom, Ideal.Quotient.mk_eq_mk_iff_sub_mem, MvPolynomial, MvPolynomial.idealOfVars, MvPolynomial.mem_pow_idealOfVars_iff, Quotient, coeff_truncTotal, idealOfVars, liftAlgHom, liftRingHom, mem_pow_idealOfVars_iff, mk_eq_mk_iff_sub_mem, toAdicCompletion, truncTotal
-/
theorem toAdicCompletion_coe (p : MvPolynomial σ R) :
    toAdicCompletion σ R p = .of (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) p := by
  symm; ext n
  suffices p - (truncTotal n) p in MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx => by simp [coeff_truncTotal _ hx]

/--
Definition of `toAdicCompletionInv` / `toAdicCompletionInv` 的定义

English:
definition toAdicCompletionInv
  signature: (σ R : Type*) [CommRing R]
  body: fun x => (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in

中文:
定义 toAdicCompletionInv
  签名: (σ R : 类型) [交换环 R]
  定义体: fun x => (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in

Depends on / 依赖: degree, f.val, out.coeff
-/
def toAdicCompletionInv (σ R : Type*) [CommRing R]
    (f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      MvPowerSeries σ R := fun x => (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in
/--
lemma `coeff_toAdicCompletionInv` / 引理 `coeff_toAdicCompletionInv`

English:
lemma coeff_toAdicCompletionInv
  statement: {x : σ ->₀ Nat}
  proof: by rfl

中文:
引理 coeff_toAdicCompletionInv
  结论: {x : σ ->₀ 自然数}
  证明: by rfl
-/
lemma coeff_toAdicCompletionInv {x : σ ->₀ Nat}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      coeff x (toAdicCompletionInv σ R f) = (f.val (degree x + 1)).out.coeff x := by rfl

/--
theorem `mk_truncTotal_toAdicCompletionInv` / 定理 `mk_truncTotal_toAdicCompletionInv`

English:
theorem mk_truncTotal_toAdicCompletionInv
  statement: {n : Nat}
  proof: by
  rw [← Ideal.Quotient.mk_out (f.val n)]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h]; rw [coeff_toAdicCompletionInv]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h)]; rw [eq_comm]
    convert! f.prop h; simp
  simp

中文:
定理 mk_truncTotal_toAdicCompletionInv
  结论: {n : 自然数}
  证明: by
  rw [← Ideal.Quotient.mk_out (f.val n)]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h]; rw [coeff_toAdicCompletionInv]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h)]; rw [eq_comm]
    convert! f.prop h; simp
  simp

Depends on / 依赖: Ideal.Quotient.eq, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.Quotient.mk_out, Ideal.mul_top, MvPolynomial, MvPolynomial.coeff_sub, MvPolynomial.idealOfVars, MvPolynomial.mem_pow_idealOfVars_iff, Quotient, Submodule, Submodule.mapQ_eq_factor, coeff_sub, coeff_toAdicCompletionInv, coeff_truncTotal, degree, f.val, idealOfVars, mapQ_eq_factor, mem_pow_idealOfVars_iff, mk_eq_mk_iff_sub_mem
-/
theorem mk_truncTotal_toAdicCompletionInv {n : Nat}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n • ⊤)
    ((truncTotal n) (toAdicCompletionInv σ R f)) = f.val n := by
  rw [← Ideal.Quotient.mk_out (f.val n)]; rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h]; rw [coeff_toAdicCompletionInv]; rw [← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h)]; rw [eq_comm]
    convert! f.prop h; simp
  simp

/--
Definition of `toAdicCompletionAlgEquiv` / `toAdicCompletionAlgEquiv` 的定义

English:
definition toAdicCompletionAlgEquiv
  signature: (σ R : Type*) [Finite σ] [CommRing R]
  body: toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using! mk_truncTotal_toAdicCompletionInv

@[simp]

中文:
定义 toAdicCompletionAlgEquiv
  签名: (σ R : 类型) [有限 σ] [交换环 R]
  定义体: toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using! mk_truncTotal_toAdicCompletionInv

@[simp]

Depends on / 依赖: toAdicCompletion
-/
def toAdicCompletionAlgEquiv (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R ≃ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) where
  __ := toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using! mk_truncTotal_toAdicCompletionInv

@[simp]
/--
lemma `toAdicCompletionAlgEquiv_apply` / 引理 `toAdicCompletionAlgEquiv_apply`

English:
lemma toAdicCompletionAlgEquiv_apply
  given: (p : MvPowerSeries σ R)
  proof: by rfl

@[simp]

中文:
引理 toAdicCompletionAlgEquiv_apply
  条件: (p : MvPowerSeries σ R)
  证明: by rfl

@[simp]
-/
lemma toAdicCompletionAlgEquiv_apply (p : MvPowerSeries σ R) :
    toAdicCompletionAlgEquiv σ R p = toAdicCompletion σ R p := by rfl

@[simp]
/--
lemma `toAdicCompletionAlgEquiv_symm_apply` / 引理 `toAdicCompletionAlgEquiv_symm_apply`

English:
lemma toAdicCompletionAlgEquiv_symm_apply
  proof: by
  rfl

中文:
引理 toAdicCompletionAlgEquiv_symm_apply
  证明: by
  rfl
-/
lemma toAdicCompletionAlgEquiv_symm_apply
    (x : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      (toAdicCompletionAlgEquiv σ R).symm x = toAdicCompletionInv σ R x := by
  rfl

end toAdicCompletion

end MvPowerSeries

section toMvPowerSeries

variable {R σ τ : Type*} [CommSemiring R] {f : PowerSeries R} (i : σ) (r : R)

open PowerSeries Filter
namespace PowerSeries

/-- Given a power series `p : R⟦X⟧` and an index `i`, we may view it as a
multivariate power series `toMvPowerSeries i p : MvPowerSeries σ R`. -/
noncomputable
/--
Definition of `toMvPowerSeries` / `toMvPowerSeries` 的定义

English:
definition toMvPowerSeries
  signature: : PowerSeries R ->ₐ[R] MvPowerSeries σ R
  body: MvPowerSeries.rename (fun _ => i)

中文:
定义 toMvPowerSeries
  签名: : 幂级数 R ->ₐ[R] MvPowerSeries σ R
  定义体: MvPowerSeries.rename (fun _ => i)

Depends on / 依赖: MvPowerSeries, MvPowerSeries.rename
-/
def toMvPowerSeries : PowerSeries R ->ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.rename (fun _ => i)

/--
theorem `toMvPowerSeries_apply` / 定理 `toMvPowerSeries_apply`

English:
theorem toMvPowerSeries_apply
  statement: f.toMvPowerSeries i = f.rename (fun _ => i)
  proof: rfl

@[simp]

中文:
定理 toMvPowerSeries_apply
  结论: f.toMvPowerSeries i = f.rename (fun _ => i)
  证明: rfl

@[simp]
-/
theorem toMvPowerSeries_apply : f.toMvPowerSeries i = f.rename (fun _ => i) := rfl

@[simp]
/--
theorem `toMvPowerSeries_C` / 定理 `toMvPowerSeries_C`

English:
theorem toMvPowerSeries_C
  statement: (C r).toMvPowerSeries i = MvPowerSeries.C r
  proof: by
  rw [toMvPowerSeries_apply]; rw [C_apply]; rw [MvPowerSeries.rename_C]

@[simp]

中文:
定理 toMvPowerSeries_C
  结论: (C r).toMvPowerSeries i = MvPowerSeries.C r
  证明: by
  rw [toMvPowerSeries_apply]; rw [C_apply]; rw [MvPowerSeries.rename_C]

@[simp]

Depends on / 依赖: C_apply, MvPowerSeries, MvPowerSeries.rename_C, rename_C, toMvPowerSeries_apply
-/
theorem toMvPowerSeries_C : (C r).toMvPowerSeries i = MvPowerSeries.C r := by
  rw [toMvPowerSeries_apply]; rw [C_apply]; rw [MvPowerSeries.rename_C]

@[simp]
/--
theorem `toMvPowerSeries_X` / 定理 `toMvPowerSeries_X`

English:
theorem toMvPowerSeries_X
  statement: X.toMvPowerSeries i = MvPowerSeries.X i (R := R)
  proof: by
  rw [toMvPowerSeries_apply]; rw [X_apply]; rw [MvPowerSeries.rename_X]

中文:
定理 toMvPowerSeries_X
  结论: X.toMvPowerSeries i = MvPowerSeries.X i (R := R)
  证明: by
  rw [toMvPowerSeries_apply]; rw [X_apply]; rw [MvPowerSeries.rename_X]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.rename_X, X_apply, rename_X, toMvPowerSeries_apply
-/
theorem toMvPowerSeries_X : X.toMvPowerSeries i = MvPowerSeries.X i (R := R) := by
  rw [toMvPowerSeries_apply]; rw [X_apply]; rw [MvPowerSeries.rename_X]

/--
theorem `toMvPowerSeries_injective` / 定理 `toMvPowerSeries_injective`

English:
theorem toMvPowerSeries_injective
  given: (i : σ)
  statement: Function.Injective (toMvPowerSeries (R := R) i)
  proof: MvPowerSeries.rename_injective (Embedding.punit i)

中文:
定理 toMvPowerSeries_injective
  条件: (i : σ)
  结论: 函数.单射 (toMvPowerSeries (R := R) i)
  证明: MvPowerSeries.rename_injective (Embedding.punit i)
-/
theorem toMvPowerSeries_injective (i : σ) : Function.Injective (toMvPowerSeries (R := R) i) :=
  MvPowerSeries.rename_injective (Embedding.punit i)

/--
theorem `toMvPowerSeries_inj` / 定理 `toMvPowerSeries_inj`

English:
theorem toMvPowerSeries_inj
  given: (i : σ) {p q : R⟦X⟧}
  proof: (toMvPowerSeries_injective i).eq_iff

中文:
定理 toMvPowerSeries_inj
  条件: (i : σ) {p q : R⟦X⟧}
  证明: (toMvPowerSeries_injective i).eq_iff

Depends on / 依赖: eq_iff, toMvPowerSeries_injective
-/
theorem toMvPowerSeries_inj (i : σ) {p q : R⟦X⟧} :
    p.toMvPowerSeries i = q.toMvPowerSeries i ↔ p = q :=
  (toMvPowerSeries_injective i).eq_iff

section CommRing

variable {R : Type*} [CommRing R] {f : R⟦X⟧} {i : σ}

/--
theorem `toMvPowerSeries_eq_subst` / 定理 `toMvPowerSeries_eq_subst`

English:
theorem toMvPowerSeries_eq_subst
  statement: f.toMvPowerSeries i = f.subst (MvPowerSeries.X i)
  proof: by
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [comp_def]; rw [subst]

中文:
定理 toMvPowerSeries_eq_subst
  结论: f.toMvPowerSeries i = f.subst (MvPowerSeries.X i)
  证明: by
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [comp_def]; rw [subst]

Depends on / 依赖: MvPowerSeries, MvPowerSeries.rename_eq_subst, comp_def, rename_eq_subst, toMvPowerSeries_apply
-/
theorem toMvPowerSeries_eq_subst : f.toMvPowerSeries i = f.subst (MvPowerSeries.X i) := by
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [comp_def]; rw [subst]

/--
theorem `subst_toMvPowerSeries` / 定理 `subst_toMvPowerSeries`

English:
theorem subst_toMvPowerSeries
  given: {a : σ -> MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
  proof: by
  rw [toMvPowerSeries_eq_subst]; rw [subst]; rw [MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha]; rw [MvPowerSeries.subst_X ha]; rw [subst]

中文:
定理 subst_toMvPowerSeries
  条件: {a : σ -> MvPowerSeries τ R} (ha : MvPowerSeries.有Subst a)
  证明: by
  rw [toMvPowerSeries_eq_subst]; rw [subst]; rw [MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha]; rw [MvPowerSeries.subst_X ha]; rw [subst]

Depends on / 依赖: HasSubst, HasSubst.X, HasSubst.const, MvPowerSeries, MvPowerSeries.subst_X, MvPowerSeries.subst_comp_subst_apply, subst_X, subst_comp_subst_apply, toMvPowerSeries_eq_subst
-/
theorem subst_toMvPowerSeries {a : σ -> MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    (f.toMvPowerSeries i).subst a = f.subst (a i) := by
  rw [toMvPowerSeries_eq_subst]; rw [subst]; rw [MvPowerSeries.subst_comp_subst_apply
    (HasSubst.const (HasSubst.X _)) ha]; rw [MvPowerSeries.subst_X ha]; rw [subst]

/--
lemma `toMvPowerSeries_coeff_eq_zero` / 引理 `toMvPowerSeries_coeff_eq_zero`

English:
lemma toMvPowerSeries_coeff_eq_zero
  given: {d : σ ->₀ Nat} (hd : d i = 0) (hf : f.constantCoeff = 0)
  proof: by classical
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [subst_X_comp_const]; rw [coeff_subst (HasSubst.X _)]; rw [finsum_eq_zero_of_forall_eq_zero]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro _ a
  subst a
  simp_all

中文:
引理 toMvPowerSeries_coeff_eq_zero
  条件: {d : σ ->₀ 自然数} (hd : d i = 0) (hf : f.constantCoeff = 0)
  证明: by classical
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [subst_X_comp_const]; rw [coeff_subst (HasSubst.X _)]; rw [finsum_eq_zero_of_forall_eq_zero]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro _ a
  subst a
  simp_all

Depends on / 依赖: HasSubst, HasSubst.X, MvPowerSeries, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, MvPowerSeries.rename_eq_subst, X_pow_eq, classical, coeff_monomial, coeff_subst, finsum_eq_zero_of_forall_eq_zero, ite_eq_right_iff, mul_ite, mul_one, mul_zero, rename_eq_subst, smul_eq_mul, subst_X_comp_const, toMvPowerSeries_apply
-/
lemma toMvPowerSeries_coeff_eq_zero {d : σ ->₀ Nat} (hd : d i = 0) (hf : f.constantCoeff = 0) :
    (f.toMvPowerSeries i).coeff d = 0 := by classical
  rw [toMvPowerSeries_apply]; rw [MvPowerSeries.rename_eq_subst]; rw [subst_X_comp_const]; rw [coeff_subst (HasSubst.X _)]; rw [finsum_eq_zero_of_forall_eq_zero]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_eq_right_iff]
  intro _ a
  subst a
  simp_all

/--
theorem `_root_.MvPowerSeries.HasSubst.toMvPowerSeries` / 定理 `_root_.MvPowerSeries.HasSubst.toMvPowerSeries`

English:
theorem _root_.MvPowerSeries.HasSubst.toMvPowerSeries
  given: (hf : f.constantCoeff = 0)
  proof: by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype d.support) fun s => by
    contrapose
    simpa using fun hd => toMvPowerSeries_coeff_eq_zero hd hf

中文:
定理 _root_.MvPowerSeries.有Subst.toMvPowerSeries
  条件: (hf : f.constantCoeff = 0)
  证明: by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype d.support) fun s => by
    contrapose
    simpa using fun hd => toMvPowerSeries_coeff_eq_zero hd hf
-/
theorem _root_.MvPowerSeries.HasSubst.toMvPowerSeries (hf : f.constantCoeff = 0) :
    MvPowerSeries.HasSubst (f.toMvPowerSeries · (σ := σ)) (S := R) where
  const_coeff := by simp_all [constantCoeff, toMvPowerSeries_apply]
  coeff_zero d := Set.Finite.subset (Finite.of_fintype d.support) fun s => by
    contrapose
    simpa using fun hd => toMvPowerSeries_coeff_eq_zero hd hf

end CommRing

end PowerSeries

variable (f : σ -> τ) [TendstoCofinite f] (a : σ) (p : R⟦X⟧)

@[simp]
/--
lemma `MvPowerSeries.rename_comp_toMvPowerSeries` / 引理 `MvPowerSeries.rename_comp_toMvPowerSeries`

English:
lemma MvPowerSeries.rename_comp_toMvPowerSeries
  proof: by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]

中文:
引理 MvPowerSeries.rename_comp_toMvPowerSeries
  证明: by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]

Depends on / 依赖: PowerSeries, PowerSeries.toMvPowerSeries, toMvPowerSeries
-/
lemma MvPowerSeries.rename_comp_toMvPowerSeries :
    (rename (R := R) f).comp (PowerSeries.toMvPowerSeries a) =
      PowerSeries.toMvPowerSeries (f a) := by
  ext
  simp [toMvPowerSeries_apply, comp_def]

@[simp]
/--
lemma `MvPowerSeries.rename_toMvPowerSeries` / 引理 `MvPowerSeries.rename_toMvPowerSeries`

English:
lemma MvPowerSeries.rename_toMvPowerSeries
  proof: DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

中文:
引理 MvPowerSeries.rename_toMvPowerSeries
  证明: DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, rename_comp_toMvPowerSeries
-/
lemma MvPowerSeries.rename_toMvPowerSeries :
    (p.toMvPowerSeries a).rename f = p.toMvPowerSeries (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPowerSeries ..) p

end toMvPowerSeries
