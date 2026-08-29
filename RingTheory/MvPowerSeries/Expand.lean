/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
## Expand multivariate power series

Given a multivariate power series `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some nonzero natural number `n`.
This operation is called `MvPowerSeries.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPowerSeries.expand`: expand a multi variate power series by a nonzero factor of p,
  so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] (p : Nat) (hp : p != 0)

/--
Definition of `expand` / `expand` 的定义

English:
definition expand
  signature: : MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R
  body: substAlgHom (HasSubst.X_pow hp)

中文:
定义 expand
  签名: : MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R
  定义体: substAlgHom (HasSubst.X_pow hp)

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, substAlgHom
-/
noncomputable def expand : MvPowerSeries σ R ->ₐ[R] MvPowerSeries σ R :=
  substAlgHom (HasSubst.X_pow hp)

/--
theorem `expand_C` / 定理 `expand_C`

English:
theorem expand_C
  given: (r : R)
  statement: expand p hp (C r : MvPowerSeries σ R) = C r
  proof: by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

@[simp]

中文:
定理 expand_C
  条件: (r : R)
  结论: expand p hp (C r : MvPowerSeries σ R) = C r
  证明: by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.map_smul_of_tower, conv_lhs, expand, map_one, map_smul_of_tower, mul_one, smul_eq_C_mul
-/
theorem expand_C (r : R) : expand p hp (C r : MvPowerSeries σ R) = C r := by
  conv_lhs => rw [← mul_one (C r), ← smul_eq_C_mul, expand, AlgHom.map_smul_of_tower,
    map_one, smul_eq_C_mul, mul_one]

@[simp]
/--
theorem `expand_X` / 定理 `expand_X`

English:
theorem expand_X
  given: (i : σ)
  statement: expand p hp (X i : MvPowerSeries σ R) = X i ^ p
  proof: substAlgHom_X (HasSubst.X_pow hp) i

@[simp]

中文:
定理 expand_X
  条件: (i : σ)
  结论: expand p hp (X i : MvPowerSeries σ R) = X i ^ p
  证明: substAlgHom_X (HasSubst.X_pow hp) i

@[simp]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, substAlgHom_X
-/
theorem expand_X (i : σ) : expand p hp (X i : MvPowerSeries σ R) = X i ^ p :=
  substAlgHom_X (HasSubst.X_pow hp) i

@[simp]
/--
theorem `expand_monomial` / 定理 `expand_monomial`

English:
theorem expand_monomial
  given: (d : σ ->₀ Nat) (r : R)
  proof: by
  rw [expand]; rw [substAlgHom_monomial (HasSubst.X_pow hp)]; rw [monomial_eq']; rw [Finsupp.prod]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul, algebraMap_apply, Algebra.algebraMap_self]
  · simp

@[simp]

中文:
定理 expand_monomial
  条件: (d : σ ->₀ 自然数) (r : R)
  证明: by
  rw [expand]; rw [substAlgHom_monomial (HasSubst.X_pow hp)]; rw [monomial_eq']; rw [Finsupp.prod]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul, algebraMap_apply, Algebra.algebraMap_self]
  · simp

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Finsupp, Finsupp.prod, Finsupp.prod_of_support_subset, Finsupp.support_smul, HasSubst, HasSubst.X_pow, X_pow, algebraMap_apply, algebraMap_self, expand, monomial_eq, pow_mul, prod_of_support_subset, substAlgHom_monomial, support_smul
-/
theorem expand_monomial (d : σ ->₀ Nat) (r : R) :
    expand p hp (monomial d r) = monomial (p • d) r := by
  rw [expand]; rw [substAlgHom_monomial (HasSubst.X_pow hp)]; rw [monomial_eq']; rw [Finsupp.prod]; rw [Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul, algebraMap_apply, Algebra.algebraMap_self]
  · simp

@[simp]
/--
theorem `expand_one` / 定理 `expand_one`

English:
theorem expand_one
  statement: expand 1 one_ne_zero = AlgHom.id R (MvPowerSeries σ R)
  proof: by
  ext1 i
  simp [expand, subst_self]

中文:
定理 expand_one
  结论: expand 1 one_ne_zero = 代数态射.id R (MvPowerSeries σ R)
  证明: by
  ext1 i
  simp [expand, subst_self]

Depends on / 依赖: expand, subst_self
-/
theorem expand_one : expand 1 one_ne_zero = AlgHom.id R (MvPowerSeries σ R) := by
  ext1 i
  simp [expand, subst_self]

/--
theorem `expand_one_apply` / 定理 `expand_one_apply`

English:
theorem expand_one_apply
  given: (f : MvPowerSeries σ R)
  statement: expand 1 one_ne_zero f = f
  proof: by simp

@[simp]

中文:
定理 expand_one_apply
  条件: (f : MvPowerSeries σ R)
  结论: expand 1 one_ne_zero f = f
  证明: by simp

@[simp]
-/
theorem expand_one_apply (f : MvPowerSeries σ R) : expand 1 one_ne_zero f = f := by simp

@[simp]
/--
theorem `map_expand` / 定理 `map_expand`

English:
theorem map_expand
  given: (f : R ->+* S) (φ : MvPowerSeries σ R)
  proof: by
  simp [expand, map_subst (HasSubst.X_pow hp)]

中文:
定理 map_expand
  条件: (f : R ->+* S) (φ : MvPowerSeries σ R)
  证明: by
  simp [expand, map_subst (HasSubst.X_pow hp)]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, expand, map_subst
-/
theorem map_expand (f : R ->+* S) (φ : MvPowerSeries σ R) :
    map f (expand p hp φ) = expand p hp (map f φ) := by
  simp [expand, map_subst (HasSubst.X_pow hp)]

section

/--
theorem `HasSubst.expand` / 定理 `HasSubst.expand`

English:
theorem HasSubst.expand
  given: {f : σ -> MvPowerSeries τ S} (hf : HasSubst f)
  proof: comp hf (HasSubst.X_pow hp)

中文:
定理 有Subst.expand
  条件: {f : σ -> MvPowerSeries τ S} (hf : 有Subst f)
  证明: comp hf (HasSubst.X_pow hp)

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow
-/
theorem HasSubst.expand {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) :
    HasSubst fun i => expand p hp (f i) := comp hf (HasSubst.X_pow hp)

/--
theorem `expand_comp_substAlgHom` / 定理 `expand_comp_substAlgHom`

English:
theorem expand_comp_substAlgHom
  given: {f : σ -> MvPowerSeries τ S} (hf : HasSubst f)
  proof: by
  ext1 i
  simp [expand, subst_comp_subst_apply hf (HasSubst.X_pow hp)]

中文:
定理 expand_comp_substAlgHom
  条件: {f : σ -> MvPowerSeries τ S} (hf : 有Subst f)
  证明: by
  ext1 i
  simp [expand, subst_comp_subst_apply hf (HasSubst.X_pow hp)]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, expand, subst_comp_subst_apply
-/
theorem expand_comp_substAlgHom {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) :
    (expand p hp).comp (substAlgHom hf) = substAlgHom (HasSubst.expand p hp hf) := by
  ext1 i
  simp [expand, subst_comp_subst_apply hf (HasSubst.X_pow hp)]

/--
theorem `expand_substAlgHom` / 定理 `expand_substAlgHom`

English:
theorem expand_substAlgHom
  given: {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) {φ : MvPowerSeries σ S}
  proof: by
  rw [← AlgHom.comp_apply]; rw [expand_comp_substAlgHom]

中文:
定理 expand_substAlgHom
  条件: {f : σ -> MvPowerSeries τ S} (hf : 有Subst f) {φ : MvPowerSeries σ S}
  证明: by
  rw [← AlgHom.comp_apply]; rw [expand_comp_substAlgHom]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, comp_apply, expand_comp_substAlgHom
-/
theorem expand_substAlgHom {f : σ -> MvPowerSeries τ S} (hf : HasSubst f) {φ : MvPowerSeries σ S} :
    expand p hp (substAlgHom hf φ) = substAlgHom (HasSubst.expand p hp hf) φ := by
  rw [← AlgHom.comp_apply]; rw [expand_comp_substAlgHom]

/--
theorem `expand_subst` / 定理 `expand_subst`

English:
theorem expand_subst
  given: {f : σ -> MvPowerSeries τ R} (hf : HasSubst f) {φ : MvPowerSeries σ R}
  proof: by
  rw [← substAlgHom_apply hf]; rw [expand_substAlgHom]; rw [substAlgHom_apply]

中文:
定理 expand_subst
  条件: {f : σ -> MvPowerSeries τ R} (hf : 有Subst f) {φ : MvPowerSeries σ R}
  证明: by
  rw [← substAlgHom_apply hf]; rw [expand_substAlgHom]; rw [substAlgHom_apply]

Depends on / 依赖: expand_substAlgHom, substAlgHom_apply
-/
theorem expand_subst {f : σ -> MvPowerSeries τ R} (hf : HasSubst f) {φ : MvPowerSeries σ R} :
    expand p hp (subst f φ) = subst (fun i => (f i).expand p hp) φ := by
  rw [← substAlgHom_apply hf]; rw [expand_substAlgHom]; rw [substAlgHom_apply]

end

/- TODO : In the original file of `MvPolynomial`, there are two theorems about `rename`
here, but we don't have `rename` for `MvPowerSeries`. And for `eval₂Hom`, `eval₂`
and `aeval`, the expression doesn't look good. -/

variable (q : Nat) (hq : q != 0)

/--
theorem `expand_mul_eq_comp` / 定理 `expand_mul_eq_comp`

English:
theorem expand_mul_eq_comp
  proof: by
  ext1 i
  simp [expand, pow_mul, subst_comp_subst_apply (HasSubst.X_pow hq) (HasSubst.X_pow hp),
    subst_pow (HasSubst.X_pow hp), subst_X (HasSubst.X_pow hp)]

中文:
定理 expand_mul_eq_comp
  证明: by
  ext1 i
  simp [expand, pow_mul, subst_comp_subst_apply (HasSubst.X_pow hq) (HasSubst.X_pow hp),
    subst_pow (HasSubst.X_pow hp), subst_X (HasSubst.X_pow hp)]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, expand, mul_ne_zero, p.mul_ne_zero, pow_mul, subst_X, subst_comp_subst_apply, subst_pow
-/
theorem expand_mul_eq_comp :
    expand (σ := σ) (R := R) (p * q) (p.mul_ne_zero hp hq) = (expand p hp).comp (expand q hq) := by
  ext1 i
  simp [expand, pow_mul, subst_comp_subst_apply (HasSubst.X_pow hq) (HasSubst.X_pow hp),
    subst_pow (HasSubst.X_pow hp), subst_X (HasSubst.X_pow hp)]

/--
theorem `expand_mul` / 定理 `expand_mul`

English:
theorem expand_mul
  given: (φ : MvPowerSeries σ R)
  statement: φ.expand (p * q) (p.mul_ne_zero hp hq) =
  proof: DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]

中文:
定理 expand_mul
  条件: (φ : MvPowerSeries σ R)
  结论: φ.expand (p * q) (p.mul_ne_zero hp hq) =
  证明: DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, expand_mul_eq_comp
-/
theorem expand_mul (φ : MvPowerSeries σ R) : φ.expand (p * q) (p.mul_ne_zero hp hq) =
    (φ.expand q hq).expand p hp :=
  DFunLike.congr_fun (expand_mul_eq_comp p hp q hq) φ

@[simp]
/--
theorem `coeff_expand_smul` / 定理 `coeff_expand_smul`

English:
theorem coeff_expand_smul
  given: (φ : MvPowerSeries σ R) (m : σ ->₀ Nat)
  proof: by
  classical
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp), smul_eq_mul]
  have {d : σ ->₀ Nat} : (d.prod fun s e => (X s (R := R) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [finsum_eq_single _ m]
  · rw [this, coeff_monomial, if_pos rfl, mul_one]
  · intro d hd
    rw [this]; rw [coeff_monomial]; rw [if_neg _]; rw [mul_zero]
    simp [nsmul_right_inj hp, hd.symm]

@[simp]

中文:
定理 coeff_expand_smul
  条件: (φ : MvPowerSeries σ R) (m : σ ->₀ 自然数)
  证明: by
  classical
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp), smul_eq_mul]
  have {d : σ ->₀ Nat} : (d.prod fun s e => (X s (R := R) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [finsum_eq_single _ m]
  · rw [this, coeff_monomial, if_pos rfl, mul_one]
  · intro d hd
    rw [this]; rw [coeff_monomial]; rw [if_neg _]; rw [mul_zero]
    simp [nsmul_right_inj hp, hd.symm]

@[simp]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, classical, coeff_monomial, coeff_subst, d.prod, expand, finsum_eq_single, hd.symm, if_neg, if_pos, monomial, monomial_smul_eq, mul_one, mul_zero, nsmul_right_inj, smul_eq_mul, substAlgHom_apply
-/
theorem coeff_expand_smul (φ : MvPowerSeries σ R) (m : σ ->₀ Nat) :
    (expand p hp φ).coeff (p • m) = φ.coeff m := by
  classical
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp), smul_eq_mul]
  have {d : σ ->₀ Nat} : (d.prod fun s e => (X s (R := R) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [finsum_eq_single _ m]
  · rw [this, coeff_monomial, if_pos rfl, mul_one]
  · intro d hd
    rw [this]; rw [coeff_monomial]; rw [if_neg _]; rw [mul_zero]
    simp [nsmul_right_inj hp, hd.symm]

@[simp]
/--
theorem `constantCoeff_expand` / 定理 `constantCoeff_expand`

English:
theorem constantCoeff_expand
  given: (φ : MvPowerSeries σ R)
  proof: by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

中文:
定理 constantCoeff_expand
  条件: (φ : MvPowerSeries σ R)
  证明: by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

Depends on / 依赖: coeff_expand_smul, coeff_zero_eq_constantCoeff, conv_lhs, smul_zero
-/
theorem constantCoeff_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).constantCoeff = φ.constantCoeff := by
  conv_lhs => rw [← coeff_zero_eq_constantCoeff, ← smul_zero p, coeff_expand_smul]
  simp

/--
theorem `coeff_expand_of_not_dvd` / 定理 `coeff_expand_of_not_dvd`

English:
theorem coeff_expand_of_not_dvd
  given: (φ : MvPowerSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i)
  proof: by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  obtain ⟨d, hd⟩ : exists (d : σ ->₀ Nat), (coeff m) (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) != 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
  have : (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [this]; rw [coeff_monomial] at hd
  have meq : m = p • d := by
    by_contra hc
    rw [if_neg hc] at hd
    contradiction
  simp [meq]

中文:
定理 coeff_expand_of_not_dvd
  条件: (φ : MvPowerSeries σ R) {m : σ ->₀ 自然数} {i : σ} (h : ¬ p ∣ m i)
  证明: by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  obtain ⟨d, hd⟩ : exists (d : σ ->₀ Nat), (coeff m) (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) != 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
  have : (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [this]; rw [coeff_monomial] at hd
  have meq : m = p • d := by
    by_contra hc
    rw [if_neg hc] at hd
    contradiction
  simp [meq]

Depends on / 依赖: HasSubst, HasSubst.X_pow, X_pow, classical, coeff_monomial, coeff_subst, contrapose, d.prod, expand, finsum_eq_zero_of_forall_eq_zero, if_neg, monomial, monomial_smul_eq, substAlgHom_apply
-/
theorem coeff_expand_of_not_dvd (φ : MvPowerSeries σ R) {m : σ ->₀ Nat} {i : σ} (h : ¬ p ∣ m i) :
    (expand p hp φ).coeff m = 0 := by
  classical
  contrapose! h
  simp only [expand, substAlgHom_apply, coeff_subst (HasSubst.X_pow hp)] at h
  obtain ⟨d, hd⟩ : exists (d : σ ->₀ Nat), (coeff m) (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) != 0 := by
    by_contra! hc
    rw [finsum_eq_zero_of_forall_eq_zero fun d => by simp [hc d]] at h
    contradiction
  have : (d.prod fun s e => ((X s (R := R)) ^ p) ^ e) = monomial (p • d) 1 := by
    simp [monomial_smul_eq]
  rw [this]; rw [coeff_monomial] at hd
  have meq : m = p • d := by
    by_contra hc
    rw [if_neg hc] at hd
    contradiction
  simp [meq]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `support_expand_subset` / 定理 `support_expand_subset`

English:
theorem support_expand_subset
  given: (φ : MvPowerSeries σ R)
  proof: by
  intro d hd
  have : forall i, p ∣ d i := fun _ => by_contra fun hc => hd (coeff_expand_of_not_dvd p hp φ hc)
  let m := d.mapRange (fun n => n / p) (Nat.zero_div p)
  have eq_aux : p • m = d := (Finsupp.ext fun a => Nat.eq_mul_of_div_eq_right (this a) rfl).symm
  rw [Function.mem_support]; rw [← eq_aux]; rw [← coeff_apply (expand p hp φ)]; rw [coeff_expand_smul]; rw [coeff_apply] at hd
  exact ⟨m, hd, eq_aux⟩

中文:
定理 support_expand_subset
  条件: (φ : MvPowerSeries σ R)
  证明: by
  intro d hd
  have : forall i, p ∣ d i := fun _ => by_contra fun hc => hd (coeff_expand_of_not_dvd p hp φ hc)
  let m := d.mapRange (fun n => n / p) (Nat.zero_div p)
  have eq_aux : p • m = d := (Finsupp.ext fun a => Nat.eq_mul_of_div_eq_right (this a) rfl).symm
  rw [Function.mem_support]; rw [← eq_aux]; rw [← coeff_apply (expand p hp φ)]; rw [coeff_expand_smul]; rw [coeff_apply] at hd
  exact ⟨m, hd, eq_aux⟩

Depends on / 依赖: Finsupp, Finsupp.ext, Function, Function.mem_support, Nat.eq_mul_of_div_eq_right, Nat.zero_div, coeff_apply, coeff_expand_of_not_dvd, coeff_expand_smul, d.mapRange, eq_aux, eq_mul_of_div_eq_right, expand, mapRange, mem_support, zero_div
-/
theorem support_expand_subset (φ : MvPowerSeries σ R) :
    (expand p hp φ).support subseteq φ.support.image (p • ·) := by
  intro d hd
  have : forall i, p ∣ d i := fun _ => by_contra fun hc => hd (coeff_expand_of_not_dvd p hp φ hc)
  let m := d.mapRange (fun n => n / p) (Nat.zero_div p)
  have eq_aux : p • m = d := (Finsupp.ext fun a => Nat.eq_mul_of_div_eq_right (this a) rfl).symm
  rw [Function.mem_support]; rw [← eq_aux]; rw [← coeff_apply (expand p hp φ)]; rw [coeff_expand_smul]; rw [coeff_apply] at hd
  exact ⟨m, hd, eq_aux⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `support_expand` / 定理 `support_expand`

English:
theorem support_expand
  given: (φ : MvPowerSeries σ R)
  proof: by
  refine (support_expand_subset p hp φ).antisymm ?_
  intro d hd
  obtain ⟨n, hn₁, hn₂⟩ := hd
  simp only [← hn₂, Function.mem_support]
  by_contra hc
  rw [Function.mem_support]; rw [← coeff_apply φ]; rw [← coeff_expand_smul p hp]; rw [coeff_apply]; rw [hc] at hn₁
  contradiction

@[simp]

中文:
定理 support_expand
  条件: (φ : MvPowerSeries σ R)
  证明: by
  refine (support_expand_subset p hp φ).antisymm ?_
  intro d hd
  obtain ⟨n, hn₁, hn₂⟩ := hd
  simp only [← hn₂, Function.mem_support]
  by_contra hc
  rw [Function.mem_support]; rw [← coeff_apply φ]; rw [← coeff_expand_smul p hp]; rw [coeff_apply]; rw [hc] at hn₁
  contradiction

@[simp]

Depends on / 依赖: Function, Function.mem_support, antisymm, coeff_apply, coeff_expand_smul, mem_support, support_expand_subset
-/
theorem support_expand (φ : MvPowerSeries σ R) :
    (expand p hp φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset p hp φ).antisymm ?_
  intro d hd
  obtain ⟨n, hn₁, hn₂⟩ := hd
  simp only [← hn₂, Function.mem_support]
  by_contra hc
  rw [Function.mem_support]; rw [← coeff_apply φ]; rw [← coeff_expand_smul p hp]; rw [coeff_apply]; rw [hc] at hn₁
  contradiction

@[simp]
/--
theorem `order_expand` / 定理 `order_expand`

English:
theorem order_expand
  given: (φ : MvPowerSeries σ R)
  proof: by
  by_cases! hφ : φ = 0
  · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
  · apply eq_of_le_of_ge
    · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
      have : p • φ.order = (p • d).degree := by simp [← hd₂]
      rw [this]
exact order_le (coeff_expand_smul p hp φ _) ▸ hd₁
    · refine MvPowerSeries.le_order fun d hd => ?_
      by_cases! h : forall i, p ∣ d i
      · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
          by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
        rw [← hm]; rw [coeff_expand_smul]; rw [coeff_of_lt_order]
        simp only [← hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
        exact lt_of_mul_lt_mul_left' hd
      · obtain ⟨i, hi⟩ := h
        exact coeff_expand_of_not_dvd p hp φ hi

中文:
定理 order_expand
  条件: (φ : MvPowerSeries σ R)
  证明: by
  by_cases! hφ : φ = 0
  · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
  · apply eq_of_le_of_ge
    · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
      have : p • φ.order = (p • d).degree := by simp [← hd₂]
      rw [this]
exact order_le (coeff_expand_smul p hp φ _) ▸ hd₁
    · refine MvPowerSeries.le_order fun d hd => ?_
      by_cases! h : forall i, p ∣ d i
      · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
          by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
        rw [← hm]; rw [coeff_expand_smul]; rw [coeff_of_lt_order]
        simp only [← hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
        exact lt_of_mul_lt_mul_left' hd
      · obtain ⟨i, hi⟩ := h
        exact coeff_expand_of_not_dvd p hp φ hi

Depends on / 依赖: ENat.mul_top, MvPowerSeries, MvPowerSeries.le_order, Nat.mul_div_canc, coeff_expand_smul, d.mapRange, degree, eq_of_le_of_ge, exists_coeff_ne_zero_and_order, le_order, mapRange, mul_div_canc, mul_top, ne_zero_iff_order_finite, ne_zero_iff_order_finite.mp, order_le
-/
theorem order_expand (φ : MvPowerSeries σ R) :
    (φ.expand p hp).order = p • φ.order := by
  by_cases! hφ : φ = 0
  · simpa [hφ] using (ENat.mul_top (by norm_cast)).symm
  · apply eq_of_le_of_ge
    · obtain ⟨d, hd₁, hd₂⟩ := exists_coeff_ne_zero_and_order (ne_zero_iff_order_finite.mp hφ)
      have : p • φ.order = (p • d).degree := by simp [← hd₂]
      rw [this]
exact order_le (coeff_expand_smul p hp φ _) ▸ hd₁
    · refine MvPowerSeries.le_order fun d hd => ?_
      by_cases! h : forall i, p ∣ d i
      · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
          by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
        rw [← hm]; rw [coeff_expand_smul]; rw [coeff_of_lt_order]
        simp only [← hm, map_nsmul, smul_eq_mul, Nat.cast_mul, nsmul_eq_mul] at hd
        exact lt_of_mul_lt_mul_left' hd
      · obtain ⟨i, hi⟩ := h
        exact coeff_expand_of_not_dvd p hp φ hi

section MvPolynomial

/-- For any multivariate polynomial `φ`, then `MvPolynomial.expand p φ` and
`MvPowerSeries.expand p hp ↑φ` coincide. -/
@[simp]
/--
theorem `expand_eq_expand` / 定理 `expand_eq_expand`

English:
theorem expand_eq_expand
  given: {φ : MvPolynomial σ R}
  proof: by
  ext n
  simp only [MvPolynomial.coeff_coe]
  by_cases! h : forall i, p ∣ n i
  · obtain ⟨m, hm⟩ : exists m, p • m = n := ⟨n.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm]; rw [coeff_expand_smul p hp _ _]; rw [φ.coeff_expand_smul _ hp]; rw [φ.coeff_coe]
  · obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp _ hi]; rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]

中文:
定理 expand_eq_expand
  条件: {φ : 多元多项式 σ R}
  证明: by
  ext n
  simp only [MvPolynomial.coeff_coe]
  by_cases! h : forall i, p ∣ n i
  · obtain ⟨m, hm⟩ : exists m, p • m = n := ⟨n.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm]; rw [coeff_expand_smul p hp _ _]; rw [φ.coeff_expand_smul _ hp]; rw [φ.coeff_coe]
  · obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp _ hi]; rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]

Depends on / 依赖: MvPolynomial, MvPolynomial.coeff_coe, MvPolynomial.coeff_expand_of_not_dvd, Nat.mul_div_cancel, coeff_coe, coeff_expand_of_not_dvd, coeff_expand_smul, mapRange, mul_div_cancel, n.mapRange
-/
theorem expand_eq_expand {φ : MvPolynomial σ R} :
    expand p hp (↑φ) = (φ.expand p : MvPowerSeries σ R) := by
  ext n
  simp only [MvPolynomial.coeff_coe]
  by_cases! h : forall i, p ∣ n i
  · obtain ⟨m, hm⟩ : exists m, p • m = n := ⟨n.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm]; rw [coeff_expand_smul p hp _ _]; rw [φ.coeff_expand_smul _ hp]; rw [φ.coeff_coe]
  · obtain ⟨i, hi⟩ := h
    rw [coeff_expand_of_not_dvd p hp _ hi]; rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]

/--
theorem `trunc'_expand` / 定理 `trunc'_expand`

English:
theorem trunc'_expand
  given: [DecidableEq σ] {n : σ ->₀ Nat} (φ : MvPowerSeries σ R)
  proof: by
  ext d
  by_cases! h : forall i, p ∣ d i
  · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    by_cases h_le : m <= n
    · rw [← hm, coeff_trunc', if_pos (nsmul_le_nsmul_right h_le p), coeff_expand_smul,
        MvPolynomial.coeff_expand_smul _ hp, coeff_trunc', if_pos h_le]
    · have not_le : ¬ p • m <= p • n := by
        obtain ⟨i, hi⟩ : exists i, m i > n i := by
          by_contra! hc
          exact h_le (Finsupp.coe_le_coe.mp hc)
        have : ¬ p • m i <= p • n i := by
          simp [Nat.mul_lt_mul_of_pos_left hi (p.ne_zero_iff_zero_lt.mp hp)]
        exact Not.intro fun a => this (a i)
      rw [coeff_trunc']; rw [← hm]; rw [if_neg not_le]; rw [MvPolynomial.coeff_expand_smul _ hp]; rw [coeff_trunc']; rw [if_neg h_le]
  · obtain ⟨i, hi⟩ := h
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]
    by_cases hd : d <= p • n
    · rw [coeff_trunc', if_pos hd, coeff_expand_of_not_dvd _ hp _ hi]
    rw [coeff_trunc']; rw [if_neg hd]

include hp in

中文:
定理 trunc'_expand
  条件: [DecidableEq σ] {n : σ ->₀ 自然数} (φ : MvPowerSeries σ R)
  证明: by
  ext d
  by_cases! h : forall i, p ∣ d i
  · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    by_cases h_le : m <= n
    · rw [← hm, coeff_trunc', if_pos (nsmul_le_nsmul_right h_le p), coeff_expand_smul,
        MvPolynomial.coeff_expand_smul _ hp, coeff_trunc', if_pos h_le]
    · have not_le : ¬ p • m <= p • n := by
        obtain ⟨i, hi⟩ : exists i, m i > n i := by
          by_contra! hc
          exact h_le (Finsupp.coe_le_coe.mp hc)
        have : ¬ p • m i <= p • n i := by
          simp [Nat.mul_lt_mul_of_pos_left hi (p.ne_zero_iff_zero_lt.mp hp)]
        exact Not.intro fun a => this (a i)
      rw [coeff_trunc']; rw [← hm]; rw [if_neg not_le]; rw [MvPolynomial.coeff_expand_smul _ hp]; rw [coeff_trunc']; rw [if_neg h_le]
  · obtain ⟨i, hi⟩ := h
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]
    by_cases hd : d <= p • n
    · rw [coeff_trunc', if_pos hd, coeff_expand_of_not_dvd _ hp _ hi]
    rw [coeff_trunc']; rw [if_neg hd]

include hp in

Depends on / 依赖: Finsupp, Finsupp.coe_le_coe.mp, MvPolynomial, MvPolynomial.coeff_expand_smul, Nat.mul_div_cancel, coe_le_coe, coeff_expand_smul, coeff_trunc, d.mapRange, h_le, if_pos, mapRange, mul_div_cancel, not_le, nsmul_le_nsmul_right
-/
theorem trunc'_expand [DecidableEq σ] {n : σ ->₀ Nat} (φ : MvPowerSeries σ R) :
    trunc' R (p • n) (expand p hp φ) = (trunc' R n φ).expand p := by
  ext d
  by_cases! h : forall i, p ∣ d i
  · obtain ⟨m, hm⟩ : exists m, p • m = d := ⟨d.mapRange (fun a => a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    by_cases h_le : m <= n
    · rw [← hm, coeff_trunc', if_pos (nsmul_le_nsmul_right h_le p), coeff_expand_smul,
        MvPolynomial.coeff_expand_smul _ hp, coeff_trunc', if_pos h_le]
    · have not_le : ¬ p • m <= p • n := by
        obtain ⟨i, hi⟩ : exists i, m i > n i := by
          by_contra! hc
          exact h_le (Finsupp.coe_le_coe.mp hc)
        have : ¬ p • m i <= p • n i := by
          simp [Nat.mul_lt_mul_of_pos_left hi (p.ne_zero_iff_zero_lt.mp hp)]
        exact Not.intro fun a => this (a i)
      rw [coeff_trunc']; rw [← hm]; rw [if_neg not_le]; rw [MvPolynomial.coeff_expand_smul _ hp]; rw [coeff_trunc']; rw [if_neg h_le]
  · obtain ⟨i, hi⟩ := h
    rw [MvPolynomial.coeff_expand_of_not_dvd _ hi]
    by_cases hd : d <= p • n
    · rw [coeff_trunc', if_pos hd, coeff_expand_of_not_dvd _ hp _ hi]
    rw [coeff_trunc']; rw [if_neg hd]

include hp in
/--
theorem `trunc'_expand_trunc'` / 定理 `trunc'_expand_trunc'`

English:
theorem trunc'_expand_trunc'
  given: {n m : σ ->₀ Nat} (h : n <= m) [DecidableEq σ] (f : MvPowerSeries σ R)
  proof: by
  rw [← expand_eq_expand p hp]; rw [trunc'_expand]; rw [← trunc'_trunc' h]

中文:
定理 trunc'_expand_trunc'
  条件: {n m : σ ->₀ 自然数} (h : n <= m) [DecidableEq σ] (f : MvPowerSeries σ R)
  证明: by
  rw [← expand_eq_expand p hp]; rw [trunc'_expand]; rw [← trunc'_trunc' h]
-/
theorem trunc'_expand_trunc' {n m : σ ->₀ Nat} (h : n <= m) [DecidableEq σ] (f : MvPowerSeries σ R) :
    (MvPolynomial.expand p) (trunc' R n f) = (trunc' R (p • n))
      ↑((MvPolynomial.expand p) (trunc' R m f)) := by
  rw [← expand_eq_expand p hp]; rw [trunc'_expand]; rw [← trunc'_trunc' h]

end MvPolynomial

section ExpChar

variable [ExpChar R p]

/--
theorem `map_frobenius_expand` / 定理 `map_frobenius_expand`

English:
theorem map_frobenius_expand
  given: {f : MvPowerSeries σ R}
  proof: by
  classical
  rw [eq_iff_frequently_trunc'_eq]; rw [Filter.frequently_atTop]
  intro n
  use (p • n)
  refine ⟨le_self_nsmul zero_le hp, ?_⟩
  · have : (((trunc' R (p • n) f).expand p).map (frobenius R p)).toMvPowerSeries =
      MvPowerSeries.map (frobenius R p) ((trunc' R (p • n) f).expand p) := by
      simp only [MvPolynomial.map_expand, ← expand_eq_expand p hp, map_expand]
      congr
    rw [trunc'_map]; rw [trunc'_expand]; rw [← trunc'_trunc'_pow (Nat.one_le_iff_ne_zero.mpr
      (expChar_ne_zero R p))]; rw [← MvPolynomial.coe_pow p]; rw [← MvPolynomial.map_frobenius_expand]; rw [this]; rw [trunc'_map]; rw [trunc'_expand_trunc' p hp (le_self_nsmul zero_le hp)]

中文:
定理 map_frobenius_expand
  条件: {f : MvPowerSeries σ R}
  证明: by
  classical
  rw [eq_iff_frequently_trunc'_eq]; rw [Filter.frequently_atTop]
  intro n
  use (p • n)
  refine ⟨le_self_nsmul zero_le hp, ?_⟩
  · have : (((trunc' R (p • n) f).expand p).map (frobenius R p)).toMvPowerSeries =
      MvPowerSeries.map (frobenius R p) ((trunc' R (p • n) f).expand p) := by
      simp only [MvPolynomial.map_expand, ← expand_eq_expand p hp, map_expand]
      congr
    rw [trunc'_map]; rw [trunc'_expand]; rw [← trunc'_trunc'_pow (Nat.one_le_iff_ne_zero.mpr
      (expChar_ne_zero R p))]; rw [← MvPolynomial.coe_pow p]; rw [← MvPolynomial.map_frobenius_expand]; rw [this]; rw [trunc'_map]; rw [trunc'_expand_trunc' p hp (le_self_nsmul zero_le hp)]

Depends on / 依赖: Filter, Filter.frequently_atTop, MvPolynomial, MvPolynomial.c, MvPolynomial.map_expand, MvPowerSeries, MvPowerSeries.map, Nat.one_le_iff_ne_zero.mpr, _expand, _map, _pow, _trunc, classical, eq_iff_frequently_trunc, expChar_ne_zero, expand, expand_eq_expand, frequently_atTop, frobenius, le_self_nsmul
-/
theorem map_frobenius_expand {f : MvPowerSeries σ R} :
    (f.expand p hp).map (frobenius R p) = f ^ p := by
  classical
  rw [eq_iff_frequently_trunc'_eq]; rw [Filter.frequently_atTop]
  intro n
  use (p • n)
  refine ⟨le_self_nsmul zero_le hp, ?_⟩
  · have : (((trunc' R (p • n) f).expand p).map (frobenius R p)).toMvPowerSeries =
      MvPowerSeries.map (frobenius R p) ((trunc' R (p • n) f).expand p) := by
      simp only [MvPolynomial.map_expand, ← expand_eq_expand p hp, map_expand]
      congr
    rw [trunc'_map]; rw [trunc'_expand]; rw [← trunc'_trunc'_pow (Nat.one_le_iff_ne_zero.mpr
      (expChar_ne_zero R p))]; rw [← MvPolynomial.coe_pow p]; rw [← MvPolynomial.map_frobenius_expand]; rw [this]; rw [trunc'_map]; rw [trunc'_expand_trunc' p hp (le_self_nsmul zero_le hp)]

/--
theorem `map_iterateFrobenius_expand` / 定理 `map_iterateFrobenius_expand`

English:
theorem map_iterateFrobenius_expand
  given: (f : MvPowerSeries σ R) (n : Nat)
  proof: by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p hp, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

中文:
定理 map_iterateFrobenius_expand
  条件: (f : MvPowerSeries σ R) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p hp, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

Depends on / 依赖: add_comm, conv_lhs, expand_mul, iterateFrobenius_add, iterateFrobenius_one, map_expand, map_frobenius_expand, map_id, map_map, n_ih, pow_mul, pow_succ, simp_rw
-/
theorem map_iterateFrobenius_expand (f : MvPowerSeries σ R) (n : Nat) :
    map (iterateFrobenius R p n) (expand (p ^ n) (pow_ne_zero n hp) f) = f ^ p ^ n := by
  induction n with
  | zero => simp [map_id]
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← map_frobenius_expand p hp, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← map_expand, ← expand_mul, iterateFrobenius_one]

end ExpChar

end MvPowerSeries
