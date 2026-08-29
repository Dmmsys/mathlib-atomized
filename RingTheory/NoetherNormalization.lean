/-
Copyright (c) 2025 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sihan Su, Wan Lin, Xiaoyang Su
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.List.Indexes
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
/-!
# Noether normalization lemma

This file contains a proof by Nagata of the Noether normalization lemma.

## Main Results
Let `A` be a finitely generated algebra over a field `k`.
Then there exists a natural number `s` and an injective homomorphism
from `k[X_0, X_1, ..., X_(s-1)]` to `A` such that `A` is integral over `k[X_0, X_1, ..., X_(s-1)]`.

## Strategy of the proof
Suppose `f` is a nonzero polynomial in `n+1` variables.
First, we construct an algebra equivalence `T` from `k[X_0,...,X_n]` to itself such that
`f` is mapped to a polynomial in `X_0` with invertible leading coefficient.
More precisely, `T` maps `X_i` to `X_i + X_0 ^ r_i` when `i ≠ 0`, and `X_0` to `X_0`.
Here we choose `r_i` to be `up ^ i` where `up` is big enough, so that `T` maps
different monomials of `f` to polynomials with different degrees in `X_0`.
See `degreeOf_t_ne_of_ne`.

Secondly, we construct the following maps: let `I` be an ideal containing `f` and
let `φ : k[X_0,...X_{n-1}] ≃ₐ[k] k[X_1,...X_n][X]` be the natural isomorphism.

- `hom1 : k[X_0,...X_{n-1}] →ₐ[k[X_0,...X_{n-1}]] k[X_1,...X_n][X]/φ(T(I))`
- `eqv1 : k[X_1,...X_n][X]/φ(T(I)) ≃ₐ[k] k[X_0,...,X_n]/T(I)`
- `eqv2 : k[X_0,...,X_n]/T(I) ≃ₐ[k] k[X_0,...,X_n]/I`
- `hom2 : k[X_0,...X_(n-1)] →ₐ[k] k[X_0,...X_n]/I`

`hom1` is integral because `φ(T(I))` contains a monic polynomial. See `hom1_isIntegral`.
`hom2` is integral because it's the composition of integral maps. See `hom2_isIntegral`.

Finally We use induction to prove there is an injective map from `k[X_0,...,X_{s-1}]`
to `k[X_0,...,X_(n-1)]/I`.The case `n=0` is trivial.
For `n+1`, if `I = 0` there is nothing to do.
Otherwise, `hom2` induces a map `φ` by quotient kernel.
We use the inductive hypothesis on k[X_1,...,X_n] and the kernel of `hom2` to get `s, g`.
Composing `φ` and `g` we get the desired map since both `φ` and `g` are injective and integral.

## Reference
* <https://stacks.math.columbia.edu/tag/00OW>

## TODO
* In the final theorems, consider setting `s` equal to the Krull dimension of `R`.
-/

public section
open Polynomial MvPolynomial Ideal Nat RingHom List

variable {k : Type*} [Field k] {n : Nat} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) ->₀ Nat)

namespace NoetherNormalization

section equivT

/-- `up` is defined as `2 + f.totalDegree`. Any big enough number would work. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
/--
lemma `lt_up` / 引理 `lt_up`

English:
lemma lt_up
  given: (vlt : forall i, v i < up)
  statement: forall l in ofFn v, l < up
  proof: by
  grind

中文:
引理 lt_up
  条件: (vlt : 对任意 i, v i < up)
  结论: 对任意 l in ofFn v, l < up
  证明: by
  grind
-/
private lemma lt_up (vlt : forall i, v i < up) : forall l in ofFn v, l < up := by
  grind

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) => up ^ i.1

/--
Definition of `T1` / `T1` 的定义

English:
abbreviation T1
  signature: (c : k)
  body: aeval fun i => if i = 0 then X 0 else X i + c • X 0 ^ r i

中文:
缩写 T1
  签名: (c : k)
  定义体: aeval fun i => if i = 0 then X 0 else X i + c • X 0 ^ r i
-/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k ->ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i => if i = 0 then X 0 else X i + c • X 0 ^ r i

/--
lemma `t1_comp_t1_neg` / 引理 `t1_comp_t1_neg`

English:
lemma t1_comp_t1_neg
  given: (c : k)
  statement: (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _
  proof: by
  rw [comp_aeval]; rw [← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

中文:
引理 t1_comp_t1_neg
  条件: (c : k)
  结论: (T1 f c).comp (T1 f (-c)) = 代数态射.id _ _
  证明: by
  rw [comp_aeval]; rw [← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp
-/
private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval]; rw [← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev T
  body: AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

中文:
缩写 noncomputable
  签名: abbrev T
  定义体: AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))
-/
private noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

/--
lemma `sum_r_mul_ne` / 引理 `sum_r_mul_ne`

English:
lemma sum_r_mul_ne
  given: (vlt : forall i, v i < up) (wlt : forall i, w i < up) (ne : v != w)
  proof: by
  intro h
refine ne Finsupp.ext congrFun ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

中文:
引理 sum_r_mul_ne
  条件: (vlt : 对任意 i, v i < up) (wlt : 对任意 i, w i < up) (ne : v != w)
  证明: by
  intro h
refine ne Finsupp.ext congrFun ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h
-/
private lemma sum_r_mul_ne (vlt : forall i, v i < up) (wlt : forall i, w i < up) (ne : v != w) :
    ∑ x : Fin (n + 1), r x * v x != ∑ x : Fin (n + 1), r x * w x := by
  intro h
refine ne Finsupp.ext congrFun ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using! h

/--
lemma `degreeOf_zero_t` / 引理 `degreeOf_zero_t`

English:
lemma degreeOf_zero_t
  given: {a : k} (ha : a != 0)
  statement: ((T f) (monomial v a)).degreeOf 0 =
  proof: by
  rw [← natDegree_finSuccEquiv]; rw [monomial_eq]; rw [Finsupp.prod_pow v fun a => X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_a

中文:
引理 degreeOf_zero_t
  条件: {a : k} (ha : a != 0)
  结论: ((T f) (monomial v a)).degreeOf 0 =
  证明: by
  rw [← natDegree_finSuccEquiv]; rw [monomial_eq]; rw [Finsupp.prod_pow v fun a => X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_a
-/
private lemma degreeOf_zero_t {a : k} (ha : a != 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv]; rw [monomial_eq]; rw [Finsupp.prod_pow v fun a => X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ != 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ => h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ => h i)),
    natDegree_prod _ _ (fun i _ => h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ => by
    rw [add_comm (Polynomial.C _)]; rw [natDegree_X_pow_add_C]; rw [mul_comm])

/--
lemma `degreeOf_t_ne_of_ne` / 引理 `degreeOf_t_ne_of_ne`

English:
lemma degreeOf_t_ne_of_ne
  given: (hv : v in f.support) (hw : w in f.support) (ne : v != w)
  proof: by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv]; rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i => ?_) (fun i => ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

中文:
引理 degreeOf_t_ne_of_ne
  条件: (hv : v in f.support) (hw : w in f.support) (ne : v != w)
  证明: by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv]; rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i => ?_) (fun i => ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)
-/
private lemma degreeOf_t_ne_of_ne (hv : v in f.support) (hw : w in f.support) (ne : v != w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 !=
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv]; rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i => ?_) (fun i => ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

/--
lemma `leadingCoeff_finSuccEquiv_t` / 引理 `leadingCoeff_finSuccEquiv_t`

English:
lemma leadingCoeff_finSuccEquiv_t
  proof: by
  rw [monomial_eq]; rw [Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply]; rw [algHom_C]; rw [algebraMap_eq]; rw [finSuccEquiv_apply]; rw [eval₂Hom_C]; rw [coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_a

中文:
引理 leadingCoeff_finSuccEquiv_t
  证明: by
  rw [monomial_eq]; rw [Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply]; rw [algHom_C]; rw [algebraMap_eq]; rw [finSuccEquiv_apply]; rw [eval₂Hom_C]; rw [coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_a
-/
private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq]; rw [Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply]; rw [algHom_C]; rw [algebraMap_eq]; rw [finSuccEquiv_apply]; rw [eval₂Hom_C]; rw [coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : forall j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j => by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i => pow_zero _

/--
lemma `T_leadingcoeff_isUnit` / 引理 `T_leadingcoeff_isUnit`

English:
lemma T_leadingcoeff_isUnit
  given: (fne : f != 0)
  proof: by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v => (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w => (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : forall x in f.support \ {v}, (finS

中文:
引理 T_leadingcoeff_isUnit
  条件: (fne : f != 0)
  证明: by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v => (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w => (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : forall x in f.support \ {v}, (finS
-/
private lemma T_leadingcoeff_isUnit (fne : f != 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v => (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w => (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : forall x in f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
apply degree_lt_degree lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
using degreeOf_t_ne_of_ne f _ _ h1 vin ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x in f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
apply leadingCoeff_add_of_degree_lt (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v != 0 := by simpa [h] using mem_support_iff.mp vin
replace h2 : (finSuccEquiv k n ((T f) (h v))) != 0 := fun eq => h2
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x => h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end equivT

section intmaps

variable (I : Ideal (MvPolynomial (Fin (n + 1)) k))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev hom1
  body: (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

中文:
缩写 noncomputable
  签名: abbrev hom1
  定义体: (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))
-/
private noncomputable abbrev hom1 : MvPolynomial (Fin n) k ->ₐ[MvPolynomial (Fin n) k]
    (MvPolynomial (Fin n) k)[X] ⧸ (I.map <| T f).map (finSuccEquiv k n) :=
  (Quotient.mkₐ (MvPolynomial (Fin n) k) (map (finSuccEquiv k n) (map (T f) I))).comp
  (Algebra.ofId (MvPolynomial (Fin n) k) ((MvPolynomial (Fin n) k)[X]))

/--
lemma `hom1_isIntegral` / 引理 `hom1_isIntegral`

English:
lemma hom1_isIntegral
  given: (fne : f != 0) (fi : f in I)
  statement: (hom1 f I).IsIntegral
  proof: by
  obtain u := T_leadingcoeff_isUnit f fne
exact (monic_of_isUnit_leadingCoeff_inv_smul u).quotient_isIntegral
Submodule.smul_of_tower_mem _ u.unit⁻¹.val mem_map_of_mem _ mem_map_of_mem _ fi

中文:
引理 hom1_is整数egral
  条件: (fne : f != 0) (fi : f in I)
  结论: (hom1 f I).是整
  证明: by
  obtain u := T_leadingcoeff_isUnit f fne
exact (monic_of_isUnit_leadingCoeff_inv_smul u).quotient_isIntegral
Submodule.smul_of_tower_mem _ u.unit⁻¹.val mem_map_of_mem _ mem_map_of_mem _ fi
-/
private lemma hom1_isIntegral (fne : f != 0) (fi : f in I) : (hom1 f I).IsIntegral := by
  obtain u := T_leadingcoeff_isUnit f fne
exact (monic_of_isUnit_leadingCoeff_inv_smul u).quotient_isIntegral
Submodule.smul_of_tower_mem _ u.unit⁻¹.val mem_map_of_mem _ mem_map_of_mem _ fi

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev eqv1
  body: quotientEquivAlg
((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm by
  set g := (finSuccEquiv k n)
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by 

中文:
缩写 noncomputable
  签名: abbrev eqv1
  定义体: quotientEquivAlg
((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm by
  set g := (finSuccEquiv k n)
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by 
-/
private noncomputable abbrev eqv1 :
    ((MvPolynomial (Fin n) k)[X] ⧸ (I.map (T f)).map (finSuccEquiv k n)) ≃ₐ[k]
    MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f) := quotientEquivAlg
((I.map (T f)).map (finSuccEquiv k n)) (I.map (T f)) (finSuccEquiv k n).symm by
  set g := (finSuccEquiv k n)
  have : g.symm.toRingEquiv.toRingHom.comp g = RingHom.id _ :=
    g.toRingEquiv.symm_toRingHom_comp_toRingHom
  calc
    _ = Ideal.map ((RingHom.id _).comp <| T f) I := by rw [id_comp, Ideal.map_coe]
    _ = (I.map (T f)).map (RingHom.id _) := by simp only [← Ideal.map_map, Ideal.map_coe]
    _ = (I.map (T f)).map (g.symm.toAlgHom.toRingHom.comp g) :=
      congrFun (congrArg Ideal.map this.symm) (I.map (T f))
    _ = _ := by simp [← Ideal.map_map, Ideal.map_coe]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev eqv2
  body: quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm by
  calc
    _ = I.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this]; rw [Ideal.map_id]
    _ = _ 

中文:
缩写 noncomputable
  签名: abbrev eqv2
  定义体: quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm by
  calc
    _ = I.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this]; rw [Ideal.map_id]
    _ = _ 
-/
private noncomputable abbrev eqv2 :
    (MvPolynomial (Fin (n + 1)) k ⧸ I.map (T f)) ≃ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
quotientEquivAlg (R₁ := k) (I.map (T f)) I (T f).symm by
  calc
    _ = I.map ((T f).symm.toRingEquiv.toRingHom.comp (T f)) := by
      have : (T f).symm.toRingEquiv.toRingHom.comp (T f) = RingHom.id _ :=
        RingEquiv.symm_toRingHom_comp_toRingHom _
      rw [this]; rw [Ideal.map_id]
    _ = _ := by
      rw [← Ideal.map_map]; rw [Ideal.map_coe]; rw [Ideal.map_coe]
      exact congrArg _ rfl

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def hom2
  body: (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

中文:
定义 noncomputable
  签名: def hom2
  定义体: (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))
-/
private noncomputable def hom2 : MvPolynomial (Fin n) k ->ₐ[k] MvPolynomial (Fin (n + 1)) k ⧸ I :=
  (eqv2 f I).toAlgHom.comp ((eqv1 f I).toAlgHom.comp ((hom1 f I).restrictScalars k))

/--
lemma `hom2_isIntegral` / 引理 `hom2_isIntegral`

English:
lemma hom2_isIntegral
  given: (fne : f != 0) (fi : f in I)
  statement: (hom2 f I).IsIntegral
  proof: ((hom1_isIntegral f I fne fi).trans _ _ <| isIntegral_of_surjective _ (eqv1 f I).surjective).trans
_ _ isIntegral_of_surjective _ (eqv2 f I).surjective

中文:
引理 hom2_is整数egral
  条件: (fne : f != 0) (fi : f in I)
  结论: (hom2 f I).是整
  证明: ((hom1_isIntegral f I fne fi).trans _ _ <| isIntegral_of_surjective _ (eqv1 f I).surjective).trans
_ _ isIntegral_of_surjective _ (eqv2 f I).surjective
-/
private lemma hom2_isIntegral (fne : f != 0) (fi : f in I) : (hom2 f I).IsIntegral :=
  ((hom1_isIntegral f I fne fi).trans _ _ <| isIntegral_of_surjective _ (eqv1 f I).surjective).trans
_ _ isIntegral_of_surjective _ (eqv2 f I).surjective

end intmaps
end NoetherNormalization

section mainthm

open NoetherNormalization

/--
theorem `exists_integral_inj_algHom_of_quotient` / 定理 `exists_integral_inj_algHom_of_quotient`

English:
theorem exists_integral_inj_algHom_of_quotient
  statement: (I : Ideal (MvPolynomial (Fin n) k))
  proof: by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, Quotient.mkₐ k I, fun a b hab => ?_,
      isIntegral_of_surjective _ (Quotient.mkₐ_surjective k I)⟩
    rw [Quotient.mkₐ_eq_mk]; rw [Ideal.Quotient.eq] at hab
    by_contra ne
    have eq := eq_C_of_isEmpty (a - b)
have ne : coeff 0 (a - b) !

中文:
定理 存在_integral_inj_algHom_of_quotient
  结论: (I : 理想 (多元多项式 (有限集 n) k))
  证明: by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, Quotient.mkₐ k I, fun a b hab => ?_,
      isIntegral_of_surjective _ (Quotient.mkₐ_surjective k I)⟩
    rw [Quotient.mkₐ_eq_mk]; rw [Ideal.Quotient.eq] at hab
    by_contra ne
    have eq := eq_C_of_isEmpty (a - b)
have ne : coeff 0 (a - b) !

Depends on / 依赖: Ideal.Quotient.eq, MvPolynomia, MvPolynomial, MvPolynomial.smul_eq_C_mul, Quotient, Quotient.mk, eq_C_of_isEmpty, isIntegral_of_surjective, isUnit, isUnit_iff_exists, isUnit_iff_exists.mp, le_rfl, map_mul, map_zero, ne.isUnit, smul_eq_C_mul, sub_ne_zero_of_ne
-/
theorem exists_integral_inj_algHom_of_quotient (I : Ideal (MvPolynomial (Fin n) k))
    (hi : I != ⊤) : exists s <= n, exists g : (MvPolynomial (Fin s) k) ->ₐ[k] ((MvPolynomial (Fin n) k) ⧸ I),
    Function.Injective g ∧ g.IsIntegral := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, Quotient.mkₐ k I, fun a b hab => ?_,
      isIntegral_of_surjective _ (Quotient.mkₐ_surjective k I)⟩
    rw [Quotient.mkₐ_eq_mk]; rw [Ideal.Quotient.eq] at hab
    by_contra ne
    have eq := eq_C_of_isEmpty (a - b)
have ne : coeff 0 (a - b) != 0 := fun h => h ▸ eq ▸ sub_ne_zero_of_ne ne map_zero _
    obtain ⟨c, _, eqr⟩ := isUnit_iff_exists.mp ne.isUnit
    have one : c • (a - b) = 1 := by
      rw [MvPolynomial.smul_eq_C_mul]; rw [eq]; rw [← map_mul]; rw [eqr]; rw [MvPolynomial.C_1]
    exact hi ((eq_top_iff_one I).mpr (one ▸ I.smul_of_tower_mem c hab))
  | succ d hd =>
    by_cases eqi : I = 0
    · have bij : Function.Bijective (Quotient.mkₐ k I) :=
        (Quotient.mk_bijective_iff_eq_bot I).mpr eqi
      exact ⟨d + 1, le_rfl, _, bij.1, isIntegral_of_surjective _ bij.2⟩
    · obtain ⟨f, fi, fne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot eqi
set ϕ := kerLiftAlg hom2 f I
      have := Quotient.nontrivial_iff.mpr hi
      obtain ⟨s, _, g, injg, intg⟩ := hd (ker <| hom2 f I) (ker_ne_top <| hom2 f I)
      have comp : (kerLiftAlg (hom2 f I)).comp (Quotient.mkₐ k <| ker <| hom2 f I) = (hom2 f I) :=
        AlgHom.ext fun a => by
          simp only [AlgHom.coe_comp, Quotient.mkₐ_eq_mk, Function.comp_apply, kerLiftAlg_mk]
      exact ⟨s, by lia, ϕ.comp g, (ϕ.coe_comp g) ▸ (kerLiftAlg_injective _).comp injg,
intg.trans _ _ (comp ▸ hom2_isIntegral f I fne fi).tower_top _ _⟩

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [a : Algebra k R]
  [fin : Algebra.FiniteType k R]

/-- **Noether normalization lemma**
For a finitely generated algebra `A` over a field `k`,
there exists a natural number `s` and an injective homomorphism
from `k[X_0, X_1, ..., X_(s-1)]` to `A` such that `A` is integral over `k[X_0, X_1, ..., X_(s-1)]`.
-/
@[stacks 00OW]
/--
theorem `exists_integral_inj_algHom_of_fg` / 定理 `exists_integral_inj_algHom_of_fg`

English:
theorem exists_integral_inj_algHom_of_fg
  statement: exists s, exists g : (MvPolynomial (Fin s) k) ->ₐ[k] R,
  proof: by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  obtain ⟨s, _, g, injg, intg⟩ := exists_integral_inj_algHom_of_quotient (ker f) (ker_ne_top _)
  use s, ϕ.toAlgHom.comp g
  simp only [AlgHom.coe_comp, AlgEquiv.coe_to

中文:
定理 存在_integral_inj_algHom_of_fg
  结论: 存在 s, 存在 g : (多元多项式 (有限集 s) k) ->ₐ[k] R,
  证明: by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  obtain ⟨s, _, g, injg, intg⟩ := exists_integral_inj_algHom_of_quotient (ker f) (ker_ne_top _)
  use s, ϕ.toAlgHom.comp g
  simp only [AlgHom.coe_comp, AlgEquiv.coe_to

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, AlgHom.toRingHom_eq_coe, Algebra, Algebra.FiniteType.iff_quotient_mvPolynomial, EmbeddingLike, EmbeddingLike.comp_injective, FiniteType, coe_comp, coe_toAlgHom, comp_injective, exists_integral_inj_algHom_of_quotient, iff_quotient_mvPolynomial, intg.trans, isIntegral_of_surjective, ker_ne_top, quotientKerAlgEquivOfSurjective, surjective
-/
theorem exists_integral_inj_algHom_of_fg : exists s, exists g : (MvPolynomial (Fin s) k) ->ₐ[k] R,
    Function.Injective g ∧ g.IsIntegral := by
  obtain ⟨n, f, fsurj⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp fin
  set ϕ := quotientKerAlgEquivOfSurjective fsurj
  obtain ⟨s, _, g, injg, intg⟩ := exists_integral_inj_algHom_of_quotient (ker f) (ker_ne_top _)
  use s, ϕ.toAlgHom.comp g
  simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, EmbeddingLike.comp_injective,
    AlgHom.toRingHom_eq_coe]
  exact ⟨injg, intg.trans _ _ (isIntegral_of_surjective _ ϕ.surjective)⟩

/--
theorem `exists_finite_inj_algHom_of_fg` / 定理 `exists_finite_inj_algHom_of_fg`

English:
theorem exists_finite_inj_algHom_of_fg
  statement: exists s, exists g : (MvPolynomial (Fin s) k) ->ₐ[k] R,
  proof: by
  obtain ⟨s, g, ⟨inj, int⟩⟩ := exists_integral_inj_algHom_of_fg k R
  have h : algebraMap k R = g.toRingHom.comp (algebraMap k (MvPolynomial (Fin s) k)) := by
    algebraize [g.toRingHom]
    rw [IsScalarTower.algebraMap_eq k (MvPolynomial (Fin s) k)]; rw [algebraMap_toAlgebra']
  exact ⟨s, g, in

中文:
定理 存在_finite_inj_algHom_of_fg
  结论: 存在 s, 存在 g : (多元多项式 (有限集 s) k) ->ₐ[k] R,
  证明: by
  obtain ⟨s, g, ⟨inj, int⟩⟩ := exists_integral_inj_algHom_of_fg k R
  have h : algebraMap k R = g.toRingHom.comp (algebraMap k (MvPolynomial (Fin s) k)) := by
    algebraize [g.toRingHom]
    rw [IsScalarTower.algebraMap_eq k (MvPolynomial (Fin s) k)]; rw [algebraMap_toAlgebra']
  exact ⟨s, g, in

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, MvPolynomial, RingHom, RingHom.finiteType_algebraMap.mpr, algebraMap, algebraMap_eq, algebraMap_toAlgebra, algebraize, exists_integral_inj_algHom_of_fg, finiteType_algebraMap, g.toRingHom, g.toRingHom.comp, int.to_finite, of_comp_finiteType, toRingHom, to_finite
-/
theorem exists_finite_inj_algHom_of_fg : exists s, exists g : (MvPolynomial (Fin s) k) ->ₐ[k] R,
    Function.Injective g ∧ g.Finite := by
  obtain ⟨s, g, ⟨inj, int⟩⟩ := exists_integral_inj_algHom_of_fg k R
  have h : algebraMap k R = g.toRingHom.comp (algebraMap k (MvPolynomial (Fin s) k)) := by
    algebraize [g.toRingHom]
    rw [IsScalarTower.algebraMap_eq k (MvPolynomial (Fin s) k)]; rw [algebraMap_toAlgebra']
  exact ⟨s, g, inj, int.to_finite
    (h ▸ RingHom.finiteType_algebraMap.mpr fin).of_comp_finiteType⟩

end mainthm
