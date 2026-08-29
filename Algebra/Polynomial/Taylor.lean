/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Taylor expansions of polynomials

## Main declarations

* `Polynomial.taylor`: the Taylor expansion of the polynomial `f` at `r`
* `Polynomial.taylor_coeff`: the `k`th coefficient of `taylor r f` is
  `(Polynomial.hasseDeriv k f).eval r`
* `Polynomial.eq_zero_of_hasseDeriv_eq_zero`:
  the identity principle: a polynomial is 0 iff all its Hasse derivatives are zero

-/

@[expose] public section


noncomputable section

namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

/--
Definition of `taylor` / `taylor` 的定义

English:
definition taylor
  signature: (r : R)
  body: f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]

中文:
定义 taylor
  签名: (r : R)
  定义体: f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]

Depends on / 依赖: f.comp
-/
def taylor (r : R) : R[X] ->ₗ[R] R[X] where
  toFun f := f.comp (X + C r)
  map_add' _ _ := add_comp
  map_smul' c f := by simp only [smul_eq_C_mul, C_mul_comp, RingHom.id_apply]

/--
theorem `taylor_apply` / 定理 `taylor_apply`

English:
theorem taylor_apply
  statement: taylor r f = f.comp (X + C r)
  proof: rfl

@[simp]

中文:
定理 taylor_apply
  结论: taylor r f = f.comp (X + C r)
  证明: rfl

@[simp]
-/
theorem taylor_apply : taylor r f = f.comp (X + C r) :=
  rfl

@[simp]
/--
theorem `taylor_X` / 定理 `taylor_X`

English:
theorem taylor_X
  statement: taylor r X = X + C r
  proof: X_comp

@[simp]

中文:
定理 taylor_X
  结论: taylor r X = X + C r
  证明: X_comp

@[simp]

Depends on / 依赖: X_comp
-/
theorem taylor_X : taylor r X = X + C r := X_comp

@[simp]
/--
theorem `taylor_X_pow` / 定理 `taylor_X_pow`

English:
theorem taylor_X_pow
  given: (n : Nat)
  statement: taylor r (X ^ n) = (X + C r) ^ n
  proof: X_pow_comp

@[simp]

中文:
定理 taylor_X_pow
  条件: (n : 自然数)
  结论: taylor r (X ^ n) = (X + C r) ^ n
  证明: X_pow_comp

@[simp]

Depends on / 依赖: X_pow_comp
-/
theorem taylor_X_pow (n : Nat) : taylor r (X ^ n) = (X + C r) ^ n := X_pow_comp

@[simp]
/--
theorem `taylor_C` / 定理 `taylor_C`

English:
theorem taylor_C
  given: (x : R)
  statement: taylor r (C x) = C x
  proof: C_comp

中文:
定理 taylor_C
  条件: (x : R)
  结论: taylor r (C x) = C x
  证明: C_comp

Depends on / 依赖: C_comp
-/
theorem taylor_C (x : R) : taylor r (C x) = C x := C_comp

/--
theorem `taylor_zero` / 定理 `taylor_zero`

English:
theorem taylor_zero
  given: (f : R[X])
  statement: taylor 0 f = f
  proof: by rw [taylor_apply, C_0, add_zero, comp_X]

@[simp]

中文:
定理 taylor_zero
  条件: (f : R[X])
  结论: taylor 0 f = f
  证明: by rw [taylor_apply, C_0, add_zero, comp_X]

@[simp]

Depends on / 依赖: add_zero, comp_X, taylor_apply
-/
theorem taylor_zero (f : R[X]) : taylor 0 f = f := by rw [taylor_apply, C_0, add_zero, comp_X]

@[simp]
/--
theorem `taylor_zero'` / 定理 `taylor_zero'`

English:
theorem taylor_zero'
  statement: taylor (0 : R) = LinearMap.id
  proof: LinearMap.ext taylor_zero

@[simp]

中文:
定理 taylor_zero'
  结论: taylor (0 : R) = 线性映射.id
  证明: LinearMap.ext taylor_zero

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, taylor_zero
-/
theorem taylor_zero' : taylor (0 : R) = LinearMap.id := LinearMap.ext taylor_zero

@[simp]
/--
theorem `taylor_one` / 定理 `taylor_one`

English:
theorem taylor_one
  statement: taylor r (1 : R[X]) = C 1
  proof: taylor_C r 1

@[simp]

中文:
定理 taylor_one
  结论: taylor r (1 : R[X]) = C 1
  证明: taylor_C r 1

@[simp]

Depends on / 依赖: taylor_C
-/
theorem taylor_one : taylor r (1 : R[X]) = C 1 := taylor_C r 1

@[simp]
/--
theorem `taylor_monomial` / 定理 `taylor_monomial`

English:
theorem taylor_monomial
  given: (i : Nat) (k : R)
  statement: taylor r (monomial i k) = C k * (X + C r) ^ i
  proof: by
  simp [taylor_apply]

中文:
定理 taylor_monomial
  条件: (i : 自然数) (k : R)
  结论: taylor r (monomial i k) = C k * (X + C r) ^ i
  证明: by
  simp [taylor_apply]

Depends on / 依赖: taylor_apply
-/
theorem taylor_monomial (i : Nat) (k : R) : taylor r (monomial i k) = C k * (X + C r) ^ i := by
  simp [taylor_apply]

/--
theorem `taylor_coeff` / 定理 `taylor_coeff`

English:
theorem taylor_coeff
  given: (n : Nat)
  statement: (taylor r f).coeff n = (hasseDeriv n f).eval r
  proof: show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push Not at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

@[simp]

中文:
定理 taylor_coeff
  条件: (n : 自然数)
  结论: (taylor r f).coeff n = (hasseDeriv n f).eval r
  证明: show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push Not at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

@[simp]

Depends on / 依赖: C_eq_natCast, C_mul, C_pow, Finset, Finset.mem_range, Finset.sum_ite_eq, LinearMap, LinearMap.comp_apply, Nat.cast_commute, Nat.choose_eq_ze, add_pow, boole_mul, cast_commute, choose_eq_ze, coeff_X_pow, coeff_mul_C, commute_X, comp_apply, eval_monomial, hasseDeriv
-/
theorem taylor_coeff (n : Nat) : (taylor r f).coeff n = (hasseDeriv n f).eval r :=
  show (lcoeff R n).comp (taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push Not at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

@[simp]
/--
theorem `taylor_coeff_zero` / 定理 `taylor_coeff_zero`

English:
theorem taylor_coeff_zero
  statement: (taylor r f).coeff 0 = f.eval r
  proof: by
  rw [taylor_coeff]; rw [hasseDeriv_zero]; rw [LinearMap.id_apply]

@[simp]

中文:
定理 taylor_coeff_zero
  结论: (taylor r f).coeff 0 = f.eval r
  证明: by
  rw [taylor_coeff]; rw [hasseDeriv_zero]; rw [LinearMap.id_apply]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id_apply, hasseDeriv_zero, id_apply, taylor_coeff
-/
theorem taylor_coeff_zero : (taylor r f).coeff 0 = f.eval r := by
  rw [taylor_coeff]; rw [hasseDeriv_zero]; rw [LinearMap.id_apply]

@[simp]
/--
theorem `taylor_coeff_one` / 定理 `taylor_coeff_one`

English:
theorem taylor_coeff_one
  statement: (taylor r f).coeff 1 = f.derivative.eval r
  proof: by
  rw [taylor_coeff]; rw [hasseDeriv_one]

@[simp]

中文:
定理 taylor_coeff_one
  结论: (taylor r f).coeff 1 = f.derivative.eval r
  证明: by
  rw [taylor_coeff]; rw [hasseDeriv_one]

@[simp]

Depends on / 依赖: hasseDeriv_one, taylor_coeff
-/
theorem taylor_coeff_one : (taylor r f).coeff 1 = f.derivative.eval r := by
  rw [taylor_coeff]; rw [hasseDeriv_one]

@[simp]
/--
theorem `coeff_taylor_natDegree` / 定理 `coeff_taylor_natDegree`

English:
theorem coeff_taylor_natDegree
  statement: (taylor r f).coeff f.natDegree = f.leadingCoeff
  proof: by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

@[simp]

中文:
定理 coeff_taylor_natDegree
  结论: (taylor r f).coeff f.natDegree = f.leadingCoeff
  证明: by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

@[simp]

Depends on / 依赖: coeff_natDegree, eval_C, hasseDeriv_natDegree_eq_C, map_zero, taylor_coeff
-/
theorem coeff_taylor_natDegree : (taylor r f).coeff f.natDegree = f.leadingCoeff := by
  by_cases hf : f = 0
  · rw [hf, map_zero, coeff_natDegree]
  · rw [taylor_coeff, hasseDeriv_natDegree_eq_C, eval_C]

@[simp]
/--
theorem `natDegree_taylor` / 定理 `natDegree_taylor`

English:
theorem natDegree_taylor
  given: (p : R[X]) (r : R)
  statement: natDegree (taylor r p) = natDegree p
  proof: by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

@[simp]

中文:
定理 natDegree_taylor
  条件: (p : R[X]) (r : R)
  结论: natDegree (taylor r p) = natDegree p
  证明: by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

@[simp]

Depends on / 依赖: map_natDegree_eq_natDegree, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, nontriviality, taylor_monomial
-/
theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (taylor r p) = natDegree p := by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

@[simp]
/--
theorem `leadingCoeff_taylor` / 定理 `leadingCoeff_taylor`

English:
theorem leadingCoeff_taylor
  statement: (taylor r f).leadingCoeff = f.leadingCoeff
  proof: by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_taylor]; rw [coeff_taylor_natDegree]; rw [leadingCoeff]

@[simp]

中文:
定理 leadingCoeff_taylor
  结论: (taylor r f).leadingCoeff = f.leadingCoeff
  证明: by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_taylor]; rw [coeff_taylor_natDegree]; rw [leadingCoeff]

@[simp]

Depends on / 依赖: coeff_taylor_natDegree, leadingCoeff, natDegree_taylor
-/
theorem leadingCoeff_taylor : (taylor r f).leadingCoeff = f.leadingCoeff := by
  rw [leadingCoeff]; rw [leadingCoeff]; rw [natDegree_taylor]; rw [coeff_taylor_natDegree]; rw [leadingCoeff]

@[simp]
/--
theorem `taylor_eq_zero` / 定理 `taylor_eq_zero`

English:
theorem taylor_eq_zero
  statement: taylor r f = 0 ↔ f = 0
  proof: by
  rw [← leadingCoeff_eq_zero]; rw [← leadingCoeff_eq_zero]; rw [leadingCoeff_taylor]

@[simp]

中文:
定理 taylor_eq_zero
  结论: taylor r f = 0 ↔ f = 0
  证明: by
  rw [← leadingCoeff_eq_zero]; rw [← leadingCoeff_eq_zero]; rw [leadingCoeff_taylor]

@[simp]

Depends on / 依赖: leadingCoeff_eq_zero, leadingCoeff_taylor
-/
theorem taylor_eq_zero : taylor r f = 0 ↔ f = 0 := by
  rw [← leadingCoeff_eq_zero]; rw [← leadingCoeff_eq_zero]; rw [leadingCoeff_taylor]

@[simp]
/--
theorem `degree_taylor` / 定理 `degree_taylor`

English:
theorem degree_taylor
  given: (p : R[X]) (r : R)
  statement: degree (taylor r p) = degree p
  proof: by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((taylor_eq_zero r p).not.2 hp),
      natDegree_taylor]

中文:
定理 degree_taylor
  条件: (p : R[X]) (r : R)
  结论: degree (taylor r p) = degree p
  证明: by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((taylor_eq_zero r p).not.2 hp),
      natDegree_taylor]

Depends on / 依赖: degree_eq_iff_natDegree_eq, degree_eq_natDegree, map_zero, natDegree_taylor, taylor_eq_zero
-/
theorem degree_taylor (p : R[X]) (r : R) : degree (taylor r p) = degree p := by
  by_cases hp : p = 0
  · rw [hp, map_zero]
  · rw [degree_eq_natDegree hp, degree_eq_iff_natDegree_eq ((taylor_eq_zero r p).not.2 hp),
      natDegree_taylor]

/--
theorem `eq_zero_of_hasseDeriv_eq_zero` / 定理 `eq_zero_of_hasseDeriv_eq_zero`

English:
theorem eq_zero_of_hasseDeriv_eq_zero
  statement: (f : R[X]) (r : R)
  proof: by
  rw [← taylor_eq_zero r]
  ext k
  rw [taylor_coeff]; rw [h]; rw [coeff_zero]

中文:
定理 eq_zero_of_hasseDeriv_eq_zero
  结论: (f : R[X]) (r : R)
  证明: by
  rw [← taylor_eq_zero r]
  ext k
  rw [taylor_coeff]; rw [h]; rw [coeff_zero]

Depends on / 依赖: coeff_zero, taylor_coeff, taylor_eq_zero
-/
theorem eq_zero_of_hasseDeriv_eq_zero (f : R[X]) (r : R)
    (h : forall k, (hasseDeriv k f).eval r = 0) : f = 0 := by
  rw [← taylor_eq_zero r]
  ext k
  rw [taylor_coeff]; rw [h]; rw [coeff_zero]

/--
lemma `map_taylor` / 引理 `map_taylor`

English:
lemma map_taylor
  given: {R S : Type*} [Semiring R] [Semiring S] (p : R[X]) (r : R) (f : R ->+* S)
  proof: by
  simp [taylor_apply, Polynomial.map_comp]

中文:
引理 map_taylor
  条件: {R S : 类型} [半环 R] [半环 S] (p : R[X]) (r : R) (f : R ->+* S)
  证明: by
  simp [taylor_apply, Polynomial.map_comp]
-/
@[simp] lemma map_taylor {R S : Type*} [Semiring R] [Semiring S] (p : R[X]) (r : R) (f : R ->+* S) :
    (p.taylor r).map f = (p.map f).taylor (f r) := by
  simp [taylor_apply, Polynomial.map_comp]

end Semiring

section Ring

variable {R : Type*} [Ring R]

/--
theorem `taylor_injective` / 定理 `taylor_injective`

English:
theorem taylor_injective
  given: (r : R)
  statement: Function.Injective (taylor r)
  proof: (injective_iff_map_eq_zero' _).2 (taylor_eq_zero r)

中文:
定理 taylor_injective
  条件: (r : R)
  结论: 函数.单射 (taylor r)
  证明: (injective_iff_map_eq_zero' _).2 (taylor_eq_zero r)

Depends on / 依赖: injective_iff_map_eq_zero, taylor_eq_zero
-/
theorem taylor_injective (r : R) : Function.Injective (taylor r) :=
  (injective_iff_map_eq_zero' _).2 (taylor_eq_zero r)

/--
lemma `taylor_inj` / 引理 `taylor_inj`

English:
lemma taylor_inj
  given: {r : R} {p q : R[X]}
  proof: (taylor_injective r).eq_iff

中文:
引理 taylor_inj
  条件: {r : R} {p q : R[X]}
  证明: (taylor_injective r).eq_iff
-/
@[simp] lemma taylor_inj {r : R} {p q : R[X]} :
    taylor r p = taylor r q ↔ p = q := (taylor_injective r).eq_iff

end Ring

section CommSemiring

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

@[simp]
/--
theorem `taylor_mul` / 定理 `taylor_mul`

English:
theorem taylor_mul
  given: (p q : R[X])
  statement: taylor r (p * q) = taylor r p * taylor r q
  proof: mul_comp ..

中文:
定理 taylor_mul
  条件: (p q : R[X])
  结论: taylor r (p * q) = taylor r p * taylor r q
  证明: mul_comp ..

Depends on / 依赖: mul_comp
-/
theorem taylor_mul (p q : R[X]) : taylor r (p * q) = taylor r p * taylor r q := mul_comp ..

/-- `Polynomial.taylor` as an `AlgHom` for commutative semirings -/
@[simps!]
/--
Definition of `taylorAlgHom` / `taylorAlgHom` 的定义

English:
definition taylorAlgHom
  signature: (r : R)
  body: AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[simp]

中文:
定义 taylorAlgHom
  签名: (r : R)
  定义体: AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, ofLinearMap, taylor, taylor_mul, taylor_one
-/
def taylorAlgHom (r : R) : R[X] ->ₐ[R] R[X] :=
  AlgHom.ofLinearMap (taylor r) (taylor_one r) (taylor_mul r)

@[simp]
/--
theorem `taylor_pow` / 定理 `taylor_pow`

English:
theorem taylor_pow
  given: (n : Nat)
  statement: taylor r (f ^ n) = taylor r f ^ n
  proof: (taylorAlgHom r).map_pow ..

中文:
定理 taylor_pow
  条件: (n : 自然数)
  结论: taylor r (f ^ n) = taylor r f ^ n
  证明: (taylorAlgHom r).map_pow ..

Depends on / 依赖: map_pow, taylorAlgHom
-/
theorem taylor_pow (n : Nat) : taylor r (f ^ n) = taylor r f ^ n :=
  (taylorAlgHom r).map_pow ..

/--
lemma `coe_taylorAlgHom` / 引理 `coe_taylorAlgHom`

English:
lemma coe_taylorAlgHom
  statement: taylorAlgHom r = taylor r
  proof: rfl

中文:
引理 coe_taylorAlgHom
  结论: taylorAlgHom r = taylor r
  证明: rfl
-/
@[simp, norm_cast] lemma coe_taylorAlgHom : taylorAlgHom r = taylor r :=
  rfl

/--
theorem `taylor_taylor` / 定理 `taylor_taylor`

English:
theorem taylor_taylor
  given: (f : R[X]) (r s : R)
  statement: taylor r (taylor s f) = taylor (r + s) f
  proof: by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]

中文:
定理 taylor_taylor
  条件: (f : R[X]) (r s : R)
  结论: taylor r (taylor s f) = taylor (r + s) f
  证明: by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]

Depends on / 依赖: C_comp, X_comp, add_assoc, add_comp, comp_assoc, map_add, taylor_apply
-/
theorem taylor_taylor (f : R[X]) (r s : R) : taylor r (taylor s f) = taylor (r + s) f := by
  simp only [taylor_apply, comp_assoc, map_add, add_comp, X_comp, C_comp, add_assoc]

/--
theorem `taylor_eval` / 定理 `taylor_eval`

English:
theorem taylor_eval
  given: (r : R) (f : R[X]) (s : R)
  statement: (taylor r f).eval s = f.eval (s + r)
  proof: by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

中文:
定理 taylor_eval
  条件: (r : R) (f : R[X]) (s : R)
  结论: (taylor r f).eval s = f.eval (s + r)
  证明: by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

Depends on / 依赖: eval_C, eval_X, eval_add, eval_comp, taylor_apply
-/
theorem taylor_eval (r : R) (f : R[X]) (s : R) : (taylor r f).eval s = f.eval (s + r) := by
  simp only [taylor_apply, eval_comp, eval_C, eval_X, eval_add]

/--
theorem `exists_mul_sq_add_linear_part_eq_eval_add` / 定理 `exists_mul_sq_add_linear_part_eq_eval_add`

English:
theorem exists_mul_sq_add_linear_part_eq_eval_add
  given: (p : R[X]) (x y : R)
  proof: by
  have this t :
      (taylor x p).eval t =
      ∑ i in Finset.range ((taylor x p).natDegree + 2), (taylor x p).coeff i * t ^ i :=
    (taylor x p).eval_eq_sum_range' (n := (taylor x p).natDegree + 2) (by lia) t
  rw [add_comm]; rw [← p.taylor_eval x y]; rw [this]; rw [Finset.sum_range_succ']; rw [Finset.sum_range_succ']
  use ∑ i in Finset.range p.natDegree, (taylor x p).coeff (i + 2) * y ^ i
  simp [pow_succ, mul_assoc, Finset.sum_mul]

中文:
定理 存在_mul_sq_add_linear_part_eq_eval_add
  条件: (p : R[X]) (x y : R)
  证明: by
  have this t :
      (taylor x p).eval t =
      ∑ i in Finset.range ((taylor x p).natDegree + 2), (taylor x p).coeff i * t ^ i :=
    (taylor x p).eval_eq_sum_range' (n := (taylor x p).natDegree + 2) (by lia) t
  rw [add_comm]; rw [← p.taylor_eval x y]; rw [this]; rw [Finset.sum_range_succ']; rw [Finset.sum_range_succ']
  use ∑ i in Finset.range p.natDegree, (taylor x p).coeff (i + 2) * y ^ i
  simp [pow_succ, mul_assoc, Finset.sum_mul]

Depends on / 依赖: Finset, Finset.range, Finset.sum_mul, Finset.sum_range_succ, add_comm, eval_eq_sum_range, mul_assoc, natDegree, p.natDegree, p.taylor_eval, pow_succ, sum_mul, sum_range_succ, taylor, taylor_eval
-/
theorem exists_mul_sq_add_linear_part_eq_eval_add (p : R[X]) (x y : R) :
    exists c : R, c * y ^ 2 + p.derivative.eval x * y + p.eval x = p.eval (x + y) := by
  have this t :
      (taylor x p).eval t =
      ∑ i in Finset.range ((taylor x p).natDegree + 2), (taylor x p).coeff i * t ^ i :=
    (taylor x p).eval_eq_sum_range' (n := (taylor x p).natDegree + 2) (by lia) t
  rw [add_comm]; rw [← p.taylor_eval x y]; rw [this]; rw [Finset.sum_range_succ']; rw [Finset.sum_range_succ']
  use ∑ i in Finset.range p.natDegree, (taylor x p).coeff (i + 2) * y ^ i
  simp [pow_succ, mul_assoc, Finset.sum_mul]

/--
theorem `eval_add_of_sq_eq_zero` / 定理 `eval_add_of_sq_eq_zero`

English:
theorem eval_add_of_sq_eq_zero
  given: (p : R[X]) (x y : R) (hy : y ^ 2 = 0)
  proof: by
  rcases exists_mul_sq_add_linear_part_eq_eval_add p x y with ⟨c, h⟩
  rw [← h]; rw [hy]; ring

中文:
定理 eval_add_of_sq_eq_zero
  条件: (p : R[X]) (x y : R) (hy : y ^ 2 = 0)
  证明: by
  rcases exists_mul_sq_add_linear_part_eq_eval_add p x y with ⟨c, h⟩
  rw [← h]; rw [hy]; ring

Depends on / 依赖: exists_mul_sq_add_linear_part_eq_eval_add
-/
theorem eval_add_of_sq_eq_zero (p : R[X]) (x y : R) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  rcases exists_mul_sq_add_linear_part_eq_eval_add p x y with ⟨c, h⟩
  rw [← h]; rw [hy]; ring

/--
theorem `aeval_add_of_sq_eq_zero` / 定理 `aeval_add_of_sq_eq_zero`

English:
theorem aeval_add_of_sq_eq_zero
  statement: {S : Type*} [CommRing S] [Algebra R S]
  proof: by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

中文:
定理 aeval_add_of_sq_eq_zero
  结论: {S : 类型} [交换环 S] [代数 R S]
  证明: by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

Depends on / 依赖: Polynomial, Polynomial.eval_add_of_sq_eq_zero, derivative_map, eval_add_of_sq_eq_zero, eval_map_algebraMap
-/
theorem aeval_add_of_sq_eq_zero {S : Type*} [CommRing S] [Algebra R S]
    (p : R[X]) (x y : S) (hy : y ^ 2 = 0) :
    p.aeval (x + y) = p.aeval x + p.derivative.aeval x * y := by
  simp only [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero _ _ _ hy, derivative_map]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (r : R) (f : R[X])

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `taylorEquiv` / `taylorEquiv` 的定义

English:
definition taylorEquiv
  signature: (r : R)
  body: taylorAlgHom (-r)
  left_inv P := by simp [taylor, comp_assoc]
  right_inv P := by simp [taylor, comp_assoc]
  __ := taylorAlgHom r

中文:
定义 taylorEquiv
  签名: (r : R)
  定义体: taylorAlgHom (-r)
  left_inv P := by simp [taylor, comp_assoc]
  right_inv P := by simp [taylor, comp_assoc]
  __ := taylorAlgHom r

Depends on / 依赖: taylorAlgHom
-/
noncomputable def taylorEquiv (r : R) : R[X] ≃ₐ[R] R[X] where
  invFun := taylorAlgHom (-r)
  left_inv P := by simp [taylor, comp_assoc]
  right_inv P := by simp [taylor, comp_assoc]
  __ := taylorAlgHom r

/--
lemma `toAlgHom_taylorEquiv` / 引理 `toAlgHom_taylorEquiv`

English:
lemma toAlgHom_taylorEquiv
  statement: taylorEquiv r = taylorAlgHom r
  proof: rfl

中文:
引理 toAlgHom_taylorEquiv
  结论: taylorEquiv r = taylorAlgHom r
  证明: rfl
-/
@[simp, norm_cast] lemma toAlgHom_taylorEquiv : taylorEquiv r = taylorAlgHom r := rfl

/--
lemma `coe_taylorEquiv` / 引理 `coe_taylorEquiv`

English:
lemma coe_taylorEquiv
  statement: taylorEquiv r = taylor r
  proof: rfl

中文:
引理 coe_taylorEquiv
  结论: taylorEquiv r = taylor r
  证明: rfl
-/
@[simp, norm_cast] lemma coe_taylorEquiv : taylorEquiv r = taylor r := rfl

/--
lemma `taylorEquiv_symm` / 引理 `taylorEquiv_symm`

English:
lemma taylorEquiv_symm
  statement: (taylorEquiv r).symm = taylorEquiv (-r)
  proof: AlgEquiv.ext fun _ => rfl

中文:
引理 taylorEquiv_symm
  结论: (taylorEquiv r).symm = taylorEquiv (-r)
  证明: AlgEquiv.ext fun _ => rfl
-/
@[simp] lemma taylorEquiv_symm : (taylorEquiv r).symm = taylorEquiv (-r) :=
  AlgEquiv.ext fun _ => rfl

/--
theorem `taylor_eval_sub` / 定理 `taylor_eval_sub`

English:
theorem taylor_eval_sub
  given: (s : R)
  proof: by rw [taylor_eval, sub_add_cancel]

中文:
定理 taylor_eval_sub
  条件: (s : R)
  证明: by rw [taylor_eval, sub_add_cancel]

Depends on / 依赖: sub_add_cancel, taylor_eval
-/
theorem taylor_eval_sub (s : R) :
    (taylor r f).eval (s - r) = f.eval s := by rw [taylor_eval, sub_add_cancel]

/--
theorem `sum_taylor_eq` / 定理 `sum_taylor_eq`

English:
theorem sum_taylor_eq
  given: (f : R[X]) (r : R)
  proof: by
  rw [← comp_eq_sum_left]; rw [sub_eq_add_neg]; rw [← C_neg]; rw [← taylor_apply]; rw [taylor_taylor]; rw [neg_add_cancel]; rw [taylor_zero]

中文:
定理 sum_taylor_eq
  条件: (f : R[X]) (r : R)
  证明: by
  rw [← comp_eq_sum_left]; rw [sub_eq_add_neg]; rw [← C_neg]; rw [← taylor_apply]; rw [taylor_taylor]; rw [neg_add_cancel]; rw [taylor_zero]

Depends on / 依赖: C_neg, comp_eq_sum_left, neg_add_cancel, sub_eq_add_neg, taylor_apply, taylor_taylor, taylor_zero
-/
theorem sum_taylor_eq (f : R[X]) (r : R) :
    ((taylor r f).sum fun i a => C a * (X - C r) ^ i) = f := by
  rw [← comp_eq_sum_left]; rw [sub_eq_add_neg]; rw [← C_neg]; rw [← taylor_apply]; rw [taylor_taylor]; rw [neg_add_cancel]; rw [taylor_zero]

end CommRing

end Polynomial
