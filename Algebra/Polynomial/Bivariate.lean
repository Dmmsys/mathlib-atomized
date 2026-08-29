/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# Bivariate polynomials

This file introduces the notation `R[X][Y]` for the polynomial ring `R[X][X]` in two variables,
and the notation `Y` for the second variable, in the `Polynomial.Bivariate` scope.

It also defines `Polynomial.evalEval` for the evaluation of a bivariate polynomial at a point
on the affine plane, which is a ring homomorphism (`Polynomial.evalEvalRingHom`), as well as
the abbreviation `CC` to view a constant in the base ring `R` as a bivariate polynomial.
-/

@[expose] public section

/-- The notation `Y` for `X` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max "Y" => Polynomial.X (R := Polynomial _)

/-- The notation `R[X][Y]` for `R[X][X]` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max R "[X][Y]" => Polynomial (Polynomial R)

open scoped Polynomial.Bivariate

namespace Polynomial

noncomputable section

variable {R S : Type*}

section Semiring

variable [Semiring R]

/--
Definition of `evalEval` / `evalEval` 的定义

English:
abbreviation evalEval
  signature: (x y : R) (p : R[X][Y])
  body: eval x (eval (C y) p)

中文:
缩写 evalEval
  签名: (x y : R) (p : R[X][Y])
  定义体: eval x (eval (C y) p)
-/
abbrev evalEval (x y : R) (p : R[X][Y]) : R := eval x (eval (C y) p)

/--
Definition of `CC` / `CC` 的定义

English:
abbreviation CC
  signature: (r : R)
  body: C (C r)

中文:
缩写 CC
  签名: (r : R)
  定义体: C (C r)
-/
abbrev CC (r : R) : R[X][Y] := C (C r)

/--
lemma `evalEval_C` / 引理 `evalEval_C`

English:
lemma evalEval_C
  given: (x y : R) (p : R[X])
  statement: (C p).evalEval x y = p.eval x
  proof: by
  rw [evalEval]; rw [eval_C]

中文:
引理 evalEval_C
  条件: (x y : R) (p : R[X])
  结论: (C p).evalEval x y = p.eval x
  证明: by
  rw [evalEval]; rw [eval_C]

Depends on / 依赖: evalEval, eval_C
-/
lemma evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval]; rw [eval_C]

/--
lemma `evalEval_map_C` / 引理 `evalEval_map_C`

English:
lemma evalEval_map_C
  given: (x y : R) (p : R[X])
  statement: (p.map C).evalEval x y = p.eval y
  proof: by
  rw [evalEval]; rw [eval_map_apply]; rw [eval_C]

@[simp]

中文:
引理 evalEval_map_C
  条件: (x y : R) (p : R[X])
  结论: (p.map C).evalEval x y = p.eval y
  证明: by
  rw [evalEval]; rw [eval_map_apply]; rw [eval_C]

@[simp]

Depends on / 依赖: Equiv.piCongrLeft, MulEquiv, MulEquiv.symm, RingEquiv, RingEquiv.symm, _symm, evalEval, eval_C, eval_map_apply, piCongrLeft
-/
lemma evalEval_map_C (x y : R) (p : R[X]) : (p.map C).evalEval x y = p.eval y := by
  rw [evalEval]; rw [eval_map_apply]; rw [eval_C]

@[simp]
/--
lemma `evalEval_CC` / 引理 `evalEval_CC`

English:
lemma evalEval_CC
  given: (x y : R) (p : R)
  statement: (CC p).evalEval x y = p
  proof: by
  rw [evalEval_C]; rw [eval_C]

@[simp]

中文:
引理 evalEval_CC
  条件: (x y : R) (p : R)
  结论: (CC p).evalEval x y = p
  证明: by
  rw [evalEval_C]; rw [eval_C]

@[simp]

Depends on / 依赖: evalEval_C, eval_C
-/
lemma evalEval_CC (x y : R) (p : R) : (CC p).evalEval x y = p := by
  rw [evalEval_C]; rw [eval_C]

@[simp]
/--
lemma `evalEval_zero` / 引理 `evalEval_zero`

English:
lemma evalEval_zero
  given: (x y : R)
  statement: (0 : R[X][Y]).evalEval x y = 0
  proof: by
  simp only [evalEval, eval_zero]

@[simp]

中文:
引理 evalEval_zero
  条件: (x y : R)
  结论: (0 : R[X][Y]).evalEval x y = 0
  证明: by
  simp only [evalEval, eval_zero]

@[simp]

Depends on / 依赖: evalEval, eval_zero
-/
lemma evalEval_zero (x y : R) : (0 : R[X][Y]).evalEval x y = 0 := by
  simp only [evalEval, eval_zero]

@[simp]
/--
lemma `evalEval_one` / 引理 `evalEval_one`

English:
lemma evalEval_one
  given: (x y : R)
  statement: (1 : R[X][Y]).evalEval x y = 1
  proof: by
  simp only [evalEval, eval_one]

@[simp]

中文:
引理 evalEval_one
  条件: (x y : R)
  结论: (1 : R[X][Y]).evalEval x y = 1
  证明: by
  simp only [evalEval, eval_one]

@[simp]

Depends on / 依赖: evalEval, eval_one
-/
lemma evalEval_one (x y : R) : (1 : R[X][Y]).evalEval x y = 1 := by
  simp only [evalEval, eval_one]

@[simp]
/--
lemma `evalEval_natCast` / 引理 `evalEval_natCast`

English:
lemma evalEval_natCast
  given: (x y : R) (n : Nat)
  statement: (n : R[X][Y]).evalEval x y = n
  proof: by
  simp only [evalEval, eval_natCast]

@[simp]

中文:
引理 evalEval_natCast
  条件: (x y : R) (n : 自然数)
  结论: (n : R[X][Y]).evalEval x y = n
  证明: by
  simp only [evalEval, eval_natCast]

@[simp]

Depends on / 依赖: evalEval, eval_natCast
-/
lemma evalEval_natCast (x y : R) (n : Nat) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_natCast]

@[simp]
/--
lemma `evalEval_X` / 引理 `evalEval_X`

English:
lemma evalEval_X
  given: (x y : R)
  statement: X.evalEval x y = y
  proof: by
  rw [evalEval]; rw [eval_X]; rw [eval_C]

@[simp]

中文:
引理 evalEval_X
  条件: (x y : R)
  结论: X.evalEval x y = y
  证明: by
  rw [evalEval]; rw [eval_X]; rw [eval_C]

@[simp]

Depends on / 依赖: evalEval, eval_C, eval_X
-/
lemma evalEval_X (x y : R) : X.evalEval x y = y := by
  rw [evalEval]; rw [eval_X]; rw [eval_C]

@[simp]
/--
lemma `evalEval_add` / 引理 `evalEval_add`

English:
lemma evalEval_add
  given: (x y : R) (p q : R[X][Y])
  proof: by
  simp only [evalEval, eval_add]

中文:
引理 evalEval_add
  条件: (x y : R) (p q : R[X][Y])
  证明: by
  simp only [evalEval, eval_add]

Depends on / 依赖: evalEval, eval_add
-/
lemma evalEval_add (x y : R) (p q : R[X][Y]) :
    (p + q).evalEval x y = p.evalEval x y + q.evalEval x y := by
  simp only [evalEval, eval_add]

/--
lemma `evalEval_sum` / 引理 `evalEval_sum`

English:
lemma evalEval_sum
  given: (x y : R) (p : R[X]) (f : Nat -> R -> R[X][Y])
  proof: by
  simp only [evalEval, eval, eval₂_sum]

中文:
引理 evalEval_sum
  条件: (x y : R) (p : R[X]) (f : 自然数 -> R -> R[X][Y])
  证明: by
  simp only [evalEval, eval, eval₂_sum]

Depends on / 依赖: evalEval
-/
lemma evalEval_sum (x y : R) (p : R[X]) (f : Nat -> R -> R[X][Y]) :
    (p.sum f).evalEval x y = p.sum fun n a => (f n a).evalEval x y := by
  simp only [evalEval, eval, eval₂_sum]

/--
lemma `evalEval_finsetSum` / 引理 `evalEval_finsetSum`

English:
lemma evalEval_finsetSum
  given: {ι : Type*} (s : Finset ι) (x y : R) (f : ι -> R[X][Y])
  proof: by
  simp only [evalEval, eval_finsetSum]

@[deprecated (since := "2026-04-08")] alias evalEval_finset_sum := evalEval_finsetSum

@[simp]

中文:
引理 evalEval_finsetSum
  条件: {ι : 类型} (s : 有限集 ι) (x y : R) (f : ι -> R[X][Y])
  证明: by
  simp only [evalEval, eval_finsetSum]

@[deprecated (since := "2026-04-08")] alias evalEval_finset_sum := evalEval_finsetSum

@[simp]

Depends on / 依赖: evalEval, eval_finsetSum
-/
lemma evalEval_finsetSum {ι : Type*} (s : Finset ι) (x y : R) (f : ι -> R[X][Y]) :
    (∑ i in s, f i).evalEval x y = ∑ i in s, (f i).evalEval x y := by
  simp only [evalEval, eval_finsetSum]

@[deprecated (since := "2026-04-08")] alias evalEval_finset_sum := evalEval_finsetSum

@[simp]
/--
lemma `evalEval_smul` / 引理 `evalEval_smul`

English:
lemma evalEval_smul
  statement: [DistribSMul S R] [IsScalarTower S R R] (x y : R) (s : S)
  proof: by
  simp only [evalEval, eval_smul]

中文:
引理 evalEval_smul
  结论: [分配标量乘法 S R] [标量塔 S R R] (x y : R) (s : S)
  证明: by
  simp only [evalEval, eval_smul]

Depends on / 依赖: evalEval, eval_smul
-/
lemma evalEval_smul [DistribSMul S R] [IsScalarTower S R R] (x y : R) (s : S)
    (p : R[X][Y]) : (s • p).evalEval x y = s • p.evalEval x y := by
  simp only [evalEval, eval_smul]

/--
lemma `evalEval_surjective` / 引理 `evalEval_surjective`

English:
lemma evalEval_surjective
  given: (x y : R)
  statement: Function.Surjective evalEval x y
  proof: fun y => ⟨CC y, evalEval_CC ..⟩

中文:
引理 evalEval_surjective
  条件: (x y : R)
  结论: 函数.满射 evalEval x y
  证明: fun y => ⟨CC y, evalEval_CC ..⟩

Depends on / 依赖: evalEval_CC
-/
lemma evalEval_surjective (x y : R) : Function.Surjective evalEval x y :=
  fun y => ⟨CC y, evalEval_CC ..⟩

end Semiring

section Ring

variable [Ring R]

@[simp]
/--
lemma `evalEval_neg` / 引理 `evalEval_neg`

English:
lemma evalEval_neg
  given: (x y : R) (p : R[X][Y])
  statement: (-p).evalEval x y = -p.evalEval x y
  proof: by
  simp only [evalEval, eval_neg]

@[simp]

中文:
引理 evalEval_neg
  条件: (x y : R) (p : R[X][Y])
  结论: (-p).evalEval x y = -p.evalEval x y
  证明: by
  simp only [evalEval, eval_neg]

@[simp]

Depends on / 依赖: evalEval, eval_neg
-/
lemma evalEval_neg (x y : R) (p : R[X][Y]) : (-p).evalEval x y = -p.evalEval x y := by
  simp only [evalEval, eval_neg]

@[simp]
/--
lemma `evalEval_sub` / 引理 `evalEval_sub`

English:
lemma evalEval_sub
  given: (x y : R) (p q : R[X][Y])
  proof: by
  simp only [evalEval, eval_sub]

@[simp]

中文:
引理 evalEval_sub
  条件: (x y : R) (p q : R[X][Y])
  证明: by
  simp only [evalEval, eval_sub]

@[simp]

Depends on / 依赖: evalEval, eval_sub
-/
lemma evalEval_sub (x y : R) (p q : R[X][Y]) :
    (p - q).evalEval x y = p.evalEval x y - q.evalEval x y := by
  simp only [evalEval, eval_sub]

@[simp]
/--
lemma `evalEval_intCast` / 引理 `evalEval_intCast`

English:
lemma evalEval_intCast
  given: (x y : R) (n : Int)
  statement: (n : R[X][Y]).evalEval x y = n
  proof: by
  simp only [evalEval, eval_intCast]

中文:
引理 evalEval_intCast
  条件: (x y : R) (n : 整数)
  结论: (n : R[X][Y]).evalEval x y = n
  证明: by
  simp only [evalEval, eval_intCast]

Depends on / 依赖: evalEval, eval_intCast
-/
lemma evalEval_intCast (x y : R) (n : Int) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_intCast]

end Ring

section CommSemiring

variable [CommSemiring R]

@[simp]
/--
lemma `evalEval_mul` / 引理 `evalEval_mul`

English:
lemma evalEval_mul
  given: (x y : R) (p q : R[X][Y])
  proof: by
  simp only [evalEval, eval_mul]

中文:
引理 evalEval_mul
  条件: (x y : R) (p q : R[X][Y])
  证明: by
  simp only [evalEval, eval_mul]

Depends on / 依赖: evalEval, eval_mul
-/
lemma evalEval_mul (x y : R) (p q : R[X][Y]) :
    (p * q).evalEval x y = p.evalEval x y * q.evalEval x y := by
  simp only [evalEval, eval_mul]

/--
lemma `evalEval_prod` / 引理 `evalEval_prod`

English:
lemma evalEval_prod
  given: {ι : Type*} (s : Finset ι) (x y : R) (p : ι -> R[X][Y])
  proof: by
  simp only [evalEval, eval_prod]

中文:
引理 evalEval_prod
  条件: {ι : 类型} (s : 有限集 ι) (x y : R) (p : ι -> R[X][Y])
  证明: by
  simp only [evalEval, eval_prod]

Depends on / 依赖: evalEval, eval_prod
-/
lemma evalEval_prod {ι : Type*} (s : Finset ι) (x y : R) (p : ι -> R[X][Y]) :
    (∏ j in s, p j).evalEval x y = ∏ j in s, (p j).evalEval x y := by
  simp only [evalEval, eval_prod]

/--
lemma `evalEval_list_prod` / 引理 `evalEval_list_prod`

English:
lemma evalEval_list_prod
  given: (x y : R) (l : List R[X][Y])
  proof: by
  simp only [evalEval, eval_list_prod, List.map_map]
  rfl -- todo: add the missing lemma

中文:
引理 evalEval_list_prod
  条件: (x y : R) (l : 列表 R[X][Y])
  证明: by
  simp only [evalEval, eval_list_prod, List.map_map]
  rfl -- todo: add the missing lemma

Depends on / 依赖: List.map_map, evalEval, eval_list_prod, map_map, missing
-/
lemma evalEval_list_prod (x y : R) (l : List R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp only [evalEval, eval_list_prod, List.map_map]
  rfl -- todo: add the missing lemma

/--
lemma `evalEval_multiset_prod` / 引理 `evalEval_multiset_prod`

English:
lemma evalEval_multiset_prod
  given: (x y : R) (l : Multiset R[X][Y])
  proof: by
  simp [evalEval, eval_multiset_prod, Multiset.map_map]

@[simp]

中文:
引理 evalEval_multiset_prod
  条件: (x y : R) (l : Multiset R[X][Y])
  证明: by
  simp [evalEval, eval_multiset_prod, Multiset.map_map]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_map, evalEval, eval_multiset_prod, map_map
-/
lemma evalEval_multiset_prod (x y : R) (l : Multiset R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simp [evalEval, eval_multiset_prod, Multiset.map_map]

@[simp]
/--
lemma `evalEval_pow` / 引理 `evalEval_pow`

English:
lemma evalEval_pow
  given: (x y : R) (p : R[X][Y]) (n : Nat)
  statement: (p ^ n).evalEval x y = p.evalEval x y ^ n
  proof: by
  simp only [evalEval, eval_pow]

中文:
引理 evalEval_pow
  条件: (x y : R) (p : R[X][Y]) (n : 自然数)
  结论: (p ^ n).evalEval x y = p.evalEval x y ^ n
  证明: by
  simp only [evalEval, eval_pow]

Depends on / 依赖: evalEval, eval_pow
-/
lemma evalEval_pow (x y : R) (p : R[X][Y]) (n : Nat) : (p ^ n).evalEval x y = p.evalEval x y ^ n := by
  simp only [evalEval, eval_pow]

/--
lemma `evalEval_dvd` / 引理 `evalEval_dvd`

English:
lemma evalEval_dvd
  given: (x y : R) {p q : R[X][Y]}
  statement: p ∣ q -> p.evalEval x y ∣ q.evalEval x y
  proof: eval_dvd ∘ eval_dvd

中文:
引理 evalEval_dvd
  条件: (x y : R) {p q : R[X][Y]}
  结论: p ∣ q -> p.evalEval x y ∣ q.evalEval x y
  证明: eval_dvd ∘ eval_dvd

Depends on / 依赖: eval_dvd
-/
lemma evalEval_dvd (x y : R) {p q : R[X][Y]} : p ∣ q -> p.evalEval x y ∣ q.evalEval x y :=
  eval_dvd ∘ eval_dvd

/--
lemma `coe_algebraMap_eq_CC` / 引理 `coe_algebraMap_eq_CC`

English:
lemma coe_algebraMap_eq_CC
  statement: algebraMap R R[X][Y] = CC (R := R)
  proof: rfl

中文:
引理 coe_algebraMap_eq_CC
  结论: algebraMap R R[X][Y] = CC (R := R)
  证明: rfl
-/
lemma coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl

/--
Definition of `evalEvalRingHom` / `evalEvalRingHom` 的定义

English:
abbreviation evalEvalRingHom
  signature: (x y : R)
  body: (evalRingHom x).comp (evalRingHom <| C y)

中文:
缩写 evalEvalRingHom
  签名: (x y : R)
  定义体: (evalRingHom x).comp (evalRingHom <| C y)
-/
@[simps!] abbrev evalEvalRingHom (x y : R) : R[X][Y] ->+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)

/--
lemma `coe_evalEvalRingHom` / 引理 `coe_evalEvalRingHom`

English:
lemma coe_evalEvalRingHom
  given: (x y : R)
  statement: evalEvalRingHom x y = evalEval x y
  proof: rfl

中文:
引理 coe_evalEvalRingHom
  条件: (x y : R)
  结论: evalEvalRingHom x y = evalEval x y
  证明: rfl
-/
lemma coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

/--
lemma `evalEvalRingHom_eq` / 引理 `evalEvalRingHom_eq`

English:
lemma evalEvalRingHom_eq
  given: (x : R)
  statement: evalEvalRingHom x = eval₂RingHom (evalRingHom x)
  proof: by
  ext <;> simp

中文:
引理 evalEvalRingHom_eq
  条件: (x : R)
  结论: evalEvalRingHom x = eval₂RingHom (evalRingHom x)
  证明: by
  ext <;> simp
-/
lemma evalEvalRingHom_eq (x : R) : evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

/--
lemma `eval₂_evalRingHom` / 引理 `eval₂_evalRingHom`

English:
lemma eval₂_evalRingHom
  given: (x : R)
  statement: eval₂ (evalRingHom x) = evalEval x
  proof: by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

中文:
引理 eval₂_evalRingHom
  条件: (x : R)
  结论: eval₂ (evalRingHom x) = evalEval x
  证明: by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

Depends on / 依赖: coe_evalEvalRingHom, evalEvalRingHom_eq
-/
lemma eval₂_evalRingHom (x : R) : eval₂ (evalRingHom x) = evalEval x := by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

/--
lemma `map_evalRingHom_eval` / 引理 `map_evalRingHom_eval`

English:
lemma map_evalRingHom_eval
  given: (x y : R) (p : R[X][Y])
  proof: by
  rw [eval_map]; rw [eval₂_evalRingHom]

中文:
引理 map_evalRingHom_eval
  条件: (x y : R) (p : R[X][Y])
  证明: by
  rw [eval_map]; rw [eval₂_evalRingHom]

Depends on / 依赖: eval_map
-/
lemma map_evalRingHom_eval (x y : R) (p : R[X][Y]) :
    (p.map <| evalRingHom x).eval y = p.evalEval x y := by
  rw [eval_map]; rw [eval₂_evalRingHom]

end CommSemiring

section

variable [Semiring R] [Semiring S] (f : R ->+* S) (p : R[X][Y]) (q : R[X])

/--
lemma `map_mapRingHom_eval_map` / 引理 `map_mapRingHom_eval_map`

English:
lemma map_mapRingHom_eval_map
  statement: (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f
  proof: by
  rw [eval_map]; rw [← coe_mapRingHom]; rw [eval₂_hom]

中文:
引理 map_mapRingHom_eval_map
  结论: (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f
  证明: by
  rw [eval_map]; rw [← coe_mapRingHom]; rw [eval₂_hom]

Depends on / 依赖: coe_mapRingHom, eval_map
-/
lemma map_mapRingHom_eval_map : (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f := by
  rw [eval_map]; rw [← coe_mapRingHom]; rw [eval₂_hom]

/--
lemma `map_mapRingHom_eval_map_eval` / 引理 `map_mapRingHom_eval_map_eval`

English:
lemma map_mapRingHom_eval_map_eval
  given: (r : R)
  proof: by
  rw [map_mapRingHom_eval_map]; rw [eval_map]; rw [eval₂_hom]

中文:
引理 map_mapRingHom_eval_map_eval
  条件: (r : R)
  证明: by
  rw [map_mapRingHom_eval_map]; rw [eval_map]; rw [eval₂_hom]

Depends on / 依赖: eval_map, map_mapRingHom_eval_map
-/
lemma map_mapRingHom_eval_map_eval (r : R) :
    ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eval r) := by
  rw [map_mapRingHom_eval_map]; rw [eval_map]; rw [eval₂_hom]

/--
lemma `map_mapRingHom_evalEval` / 引理 `map_mapRingHom_evalEval`

English:
lemma map_mapRingHom_evalEval
  given: (x y : R)
  proof: by
  rw [evalEval]; rw [← map_mapRingHom_eval_map_eval]; rw [map_C]

中文:
引理 map_mapRingHom_evalEval
  条件: (x y : R)
  证明: by
  rw [evalEval]; rw [← map_mapRingHom_eval_map_eval]; rw [map_C]

Depends on / 依赖: evalEval, map_C, map_mapRingHom_eval_map_eval
-/
lemma map_mapRingHom_evalEval (x y : R) :
    (p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y) := by
  rw [evalEval]; rw [← map_mapRingHom_eval_map_eval]; rw [map_C]

end

variable [CommSemiring R] [CommSemiring S]

/--
lemma `eval₂RingHom_eval₂RingHom` / 引理 `eval₂RingHom_eval₂RingHom`

English:
lemma eval₂RingHom_eval₂RingHom
  given: (f : R ->+* S) (x y : S)
  proof: by
  ext <;> simp

中文:
引理 eval₂RingHom_eval₂RingHom
  条件: (f : R ->+* S) (x y : S)
  证明: by
  ext <;> simp
-/
lemma eval₂RingHom_eval₂RingHom (f : R ->+* S) (x y : S) :
    eval₂RingHom (eval₂RingHom f x) y =
      (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom f) := by
  ext <;> simp

/--
lemma `eval₂_eval₂RingHom_apply` / 引理 `eval₂_eval₂RingHom_apply`

English:
lemma eval₂_eval₂RingHom_apply
  given: (f : R ->+* S) (x y : S) (p : R[X][Y])
  proof: congr($(eval₂RingHom_eval₂RingHom f x y) p)

中文:
引理 eval₂_eval₂RingHom_apply
  条件: (f : R ->+* S) (x y : S) (p : R[X][Y])
  证明: congr($(eval₂RingHom_eval₂RingHom f x y) p)
-/
lemma eval₂_eval₂RingHom_apply (f : R ->+* S) (x y : S) (p : R[X][Y]) :
    eval₂ (eval₂RingHom f x) y p = (p.map <| mapRingHom f).evalEval x y :=
  congr($(eval₂RingHom_eval₂RingHom f x y) p)

/--
lemma `eval_C_X_comp_eval₂_map_C_X` / 引理 `eval_C_X_comp_eval₂_map_C_X`

English:
lemma eval_C_X_comp_eval₂_map_C_X
  proof: by
  ext <;> simp

中文:
引理 eval_C_X_comp_eval₂_map_C_X
  证明: by
  ext <;> simp
-/
lemma eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][Y])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][Y]) (C Y)) =
      .id _ := by
  ext <;> simp

/--
lemma `eval_C_X_eval₂_map_C_X` / 引理 `eval_C_X_eval₂_map_C_X`

English:
lemma eval_C_X_eval₂_map_C_X
  given: {p : R[X][Y]}
  proof: congr($eval_C_X_comp_eval₂_map_C_X p)

中文:
引理 eval_C_X_eval₂_map_C_X
  条件: {p : R[X][Y]}
  证明: congr($eval_C_X_comp_eval₂_map_C_X p)
-/
lemma eval_C_X_eval₂_map_C_X {p : R[X][Y]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][Y]) (C Y) p) = p :=
  congr($eval_C_X_comp_eval₂_map_C_X p)

end

section aevalAeval

noncomputable section

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

variable (R A) in
/-- Given valuations `x` and `y` of the variables in an `R`-algebra `A`, the bijection induced by
the unique `R`-algebra homomorphism from `R[X][Y]` to `A` sending `X` to `x` and `Y` to `y`. -/
@[simps! apply_apply symm_apply]
/--
Definition of `aevalAevalEquiv` / `aevalAevalEquiv` 的定义

English:
definition aevalAevalEquiv
  signature: : A × A ≃ (R[X][Y] ->ₐ[R] A) where
  body: aeval xy.fst
.restrictScalars R let := Polynomial.algebra; aeval (R := R[X]) (C xy.snd)
invFun f := ⟨f C X, f Y⟩
  left_inv f := by simp
  right_inv f := algHom_ext' (by ext; simp) (by simp)

中文:
定义 aevalAevalEquiv
  签名: : A × A ≃ (R[X][Y] ->ₐ[R] A) where
  定义体: aeval xy.fst
.restrictScalars R let := Polynomial.algebra; aeval (R := R[X]) (C xy.snd)
invFun f := ⟨f C X, f Y⟩
  left_inv f := by simp
  right_inv f := algHom_ext' (by ext; simp) (by simp)

Depends on / 依赖: xy.fst
-/
def aevalAevalEquiv : A × A ≃ (R[X][Y] ->ₐ[R] A) where
.comp .restrictScalars R toFun xy := aeval xy.fst
.restrictScalars R let := Polynomial.algebra; aeval (R := R[X]) (C xy.snd)
invFun f := ⟨f C X, f Y⟩
  left_inv f := by simp
  right_inv f := algHom_ext' (by ext; simp) (by simp)

/--
Definition of `aevalAeval` / `aevalAeval` 的定义

English:
abbreviation aevalAeval
  signature: (x y : A)
  body: aevalAevalEquiv R A ⟨x, y⟩

中文:
缩写 aevalAeval
  签名: (x y : A)
  定义体: aevalAevalEquiv R A ⟨x, y⟩

Depends on / 依赖: aevalAevalEquiv
-/
abbrev aevalAeval (x y : A) : R[X][Y] ->ₐ[R] A :=
  aevalAevalEquiv R A ⟨x, y⟩

/--
lemma `aevalAevalEquiv_apply` / 引理 `aevalAevalEquiv_apply`

English:
lemma aevalAevalEquiv_apply
  given: (xy : A × A)
  statement: aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2
  proof: rfl

中文:
引理 aevalAevalEquiv_apply
  条件: (xy : A × A)
  结论: aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2
  证明: rfl
-/
lemma aevalAevalEquiv_apply (xy : A × A) : aevalAevalEquiv R A xy = aevalAeval xy.1 xy.2 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `coe_aevalAeval_eq_evalEval` / 定理 `coe_aevalAeval_eq_evalEval`

English:
theorem coe_aevalAeval_eq_evalEval
  given: (x y : A)
  statement: ⇑(aevalAeval x y) = evalEval x y
  proof: by
  ext
  simp [aeval, aevalEquiv]

中文:
定理 coe_aevalAeval_eq_evalEval
  条件: (x y : A)
  结论: ⇑(aevalAeval x y) = evalEval x y
  证明: by
  ext
  simp [aeval, aevalEquiv]

Depends on / 依赖: aevalEquiv
-/
theorem coe_aevalAeval_eq_evalEval (x y : A) : ⇑(aevalAeval x y) = evalEval x y := by
  ext
  simp [aeval, aevalEquiv]

/--
lemma `aevalAeval_C` / 引理 `aevalAeval_C`

English:
lemma aevalAeval_C
  given: (x y : A) (p : R[X])
  statement: (C p).aevalAeval x y = aeval x p
  proof: by simp

中文:
引理 aevalAeval_C
  条件: (x y : A) (p : R[X])
  结论: (C p).aevalAeval x y = aeval x p
  证明: by simp
-/
lemma aevalAeval_C (x y : A) (p : R[X]) : (C p).aevalAeval x y = aeval x p := by simp

/--
lemma `aevalAeval_X` / 引理 `aevalAeval_X`

English:
lemma aevalAeval_X
  given: (x y : A)
  statement: (C X : R[X][Y]).aevalAeval x y = x
  proof: by rw [aevalAeval_C, aeval_X]

中文:
引理 aevalAeval_X
  条件: (x y : A)
  结论: (C X : R[X][Y]).aevalAeval x y = x
  证明: by rw [aevalAeval_C, aeval_X]

Depends on / 依赖: aevalAeval_C, aeval_X
-/
lemma aevalAeval_X (x y : A) : (C X : R[X][Y]).aevalAeval x y = x := by rw [aevalAeval_C, aeval_X]

/--
lemma `aevalAeval_Y` / 引理 `aevalAeval_Y`

English:
lemma aevalAeval_Y
  given: (x y : A)
  statement: (Y : R[X][Y]).aevalAeval x y = y
  proof: by simp

中文:
引理 aevalAeval_Y
  条件: (x y : A)
  结论: (Y : R[X][Y]).aevalAeval x y = y
  证明: by simp
-/
lemma aevalAeval_Y (x y : A) : (Y : R[X][Y]).aevalAeval x y = y := by simp

/--
Definition of `Bivariate.swap` / `Bivariate.swap` 的定义

English:
definition Bivariate.swap
  signature: : R[X][Y] ≃ₐ[R] R[X][Y]
  body: by
  apply AlgEquiv.ofAlgHom (aevalAeval (Y : R[X][Y]) (C X)) (aevalAeval (Y : R[X][Y]) (C X))
    <;> (ext n m <;> simp)

@[simp]

中文:
定义 Bivariate.swap
  签名: : R[X][Y] ≃ₐ[R] R[X][Y]
  定义体: by
  apply AlgEquiv.ofAlgHom (aevalAeval (Y : R[X][Y]) (C X)) (aevalAeval (Y : R[X][Y]) (C X))
    <;> (ext n m <;> simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, aevalAeval, ofAlgHom
-/
def Bivariate.swap : R[X][Y] ≃ₐ[R] R[X][Y] := by
  apply AlgEquiv.ofAlgHom (aevalAeval (Y : R[X][Y]) (C X)) (aevalAeval (Y : R[X][Y]) (C X))
    <;> (ext n m <;> simp)

@[simp]
/--
theorem `Bivariate.swap_symm` / 定理 `Bivariate.swap_symm`

English:
theorem Bivariate.swap_symm
  statement: swap.symm = (swap (R := R))
  proof: rfl

中文:
定理 Bivariate.swap_symm
  结论: swap.symm = (swap (R := R))
  证明: rfl
-/
theorem Bivariate.swap_symm : swap.symm = (swap (R := R)) := rfl

/--
theorem `Bivariate.swap_apply` / 定理 `Bivariate.swap_apply`

English:
theorem Bivariate.swap_apply
  given: (p : R[X][Y])
  statement: swap p = p.aevalAeval (A := R[X][Y]) Y (C X)
  proof: rfl

中文:
定理 Bivariate.swap_apply
  条件: (p : R[X][Y])
  结论: swap p = p.aevalAeval (A := R[X][Y]) Y (C X)
  证明: rfl
-/
theorem Bivariate.swap_apply (p : R[X][Y]) : swap p = p.aevalAeval (A := R[X][Y]) Y (C X) := rfl

attribute [local simp] Bivariate.swap_apply

/--
theorem `Bivariate.swap_X` / 定理 `Bivariate.swap_X`

English:
theorem Bivariate.swap_X
  statement: swap (R := R) (C X) = Y
  proof: by simp

中文:
定理 Bivariate.swap_X
  结论: swap (R := R) (C X) = Y
  证明: by simp
-/
theorem Bivariate.swap_X : swap (R := R) (C X) = Y := by simp

/--
theorem `Bivariate.swap_Y` / 定理 `Bivariate.swap_Y`

English:
theorem Bivariate.swap_Y
  statement: swap (R := R) Y = (C X)
  proof: by simp

中文:
定理 Bivariate.swap_Y
  结论: swap (R := R) Y = (C X)
  证明: by simp
-/
theorem Bivariate.swap_Y : swap (R := R) Y = (C X) := by simp

/--
theorem `Bivariate.swap_C_C` / 定理 `Bivariate.swap_C_C`

English:
theorem Bivariate.swap_C_C
  given: (r : R)
  statement: swap (C (C r)) = C (C r)
  proof: by simp

中文:
定理 Bivariate.swap_C_C
  条件: (r : R)
  结论: swap (C (C r)) = C (C r)
  证明: by simp
-/
theorem Bivariate.swap_C_C (r : R) : swap (C (C r)) = C (C r) := by simp

/--
theorem `Bivariate.swap_C` / 定理 `Bivariate.swap_C`

English:
theorem Bivariate.swap_C
  given: (f : R[X])
  statement: swap (C f) = f.map C
  proof: by
  simpa [← algebraMap_eq] using aeval_X_left_eq_map f

中文:
定理 Bivariate.swap_C
  条件: (f : R[X])
  结论: swap (C f) = f.map C
  证明: by
  simpa [← algebraMap_eq] using aeval_X_left_eq_map f

Depends on / 依赖: aeval_X_left_eq_map, algebraMap_eq
-/
theorem Bivariate.swap_C (f : R[X]) : swap (C f) = f.map C := by
  simpa [← algebraMap_eq] using aeval_X_left_eq_map f

/--
theorem `Bivariate.swap_swap_apply` / 定理 `Bivariate.swap_swap_apply`

English:
theorem Bivariate.swap_swap_apply
  given: (p : R[X][Y])
  statement: swap (swap p) = p
  proof: AlgEquiv.symm_apply_apply swap p

中文:
定理 Bivariate.swap_swap_apply
  条件: (p : R[X][Y])
  结论: swap (swap p) = p
  证明: AlgEquiv.symm_apply_apply swap p

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_apply_apply, symm_apply_apply
-/
theorem Bivariate.swap_swap_apply (p : R[X][Y]) : swap (swap p) = p :=
  AlgEquiv.symm_apply_apply swap p

/--
theorem `Bivariate.swap_map_C` / 定理 `Bivariate.swap_map_C`

English:
theorem Bivariate.swap_map_C
  given: (f : R[X])
  statement: swap (f.map C) = C f
  proof: by
  induction f using Polynomial.induction_on' with
  | add => aesop
  | monomial n a => rw [map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, swap_Y, C_mul, C_pow, Bivariate.swap_C_C]

中文:
定理 Bivariate.swap_map_C
  条件: (f : R[X])
  结论: swap (f.map C) = C f
  证明: by
  induction f using Polynomial.induction_on' with
  | add => aesop
  | monomial n a => rw [map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, swap_Y, C_mul, C_pow, Bivariate.swap_C_C]

Depends on / 依赖: Bivariate, Bivariate.swap_C_C, C_mul, C_mul_X_pow_eq_monomial, C_pow, Polynomial, Polynomial.induction_on, induction_on, map_monomial, map_mul, map_pow, monomial, swap_C_C, swap_Y
-/
theorem Bivariate.swap_map_C (f : R[X]) : swap (f.map C) = C f := by
  induction f using Polynomial.induction_on' with
  | add => aesop
  | monomial n a => rw [map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
    map_mul, map_pow, swap_Y, C_mul, C_pow, Bivariate.swap_C_C]

/--
theorem `Bivariate.swap_monomial` / 定理 `Bivariate.swap_monomial`

English:
theorem Bivariate.swap_monomial
  given: (n : Nat) (f : R[X])
  proof: by
  simp [← C_mul_X_pow_eq_monomial, aeval_X_left_eq_map]

中文:
定理 Bivariate.swap_monomial
  条件: (n : 自然数) (f : R[X])
  证明: by
  simp [← C_mul_X_pow_eq_monomial, aeval_X_left_eq_map]

Depends on / 依赖: C_mul_X_pow_eq_monomial, aeval_X_left_eq_map
-/
theorem Bivariate.swap_monomial (n : Nat) (f : R[X]) :
    swap (monomial n f) = f.map C * C (X ^ n) := by
  simp [← C_mul_X_pow_eq_monomial, aeval_X_left_eq_map]

/--
theorem `Bivariate.swap_monomial_monomial` / 定理 `Bivariate.swap_monomial_monomial`

English:
theorem Bivariate.swap_monomial_monomial
  given: (n m : Nat) (r : R)
  proof: by
  simp [← C_mul_X_pow_eq_monomial]; ac_rfl

中文:
定理 Bivariate.swap_monomial_monomial
  条件: (n m : 自然数) (r : R)
  证明: by
  simp [← C_mul_X_pow_eq_monomial]; ac_rfl

Depends on / 依赖: C_mul_X_pow_eq_monomial
-/
theorem Bivariate.swap_monomial_monomial (n m : Nat) (r : R) :
    swap (monomial n (monomial m r)) = (monomial m (monomial n r)) := by
  simp [← C_mul_X_pow_eq_monomial]; ac_rfl

/--
theorem `Bivariate.aevalAeval_swap` / 定理 `Bivariate.aevalAeval_swap`

English:
theorem Bivariate.aevalAeval_swap
  given: (x y : A) (p : R[X][Y])
  proof: by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
    simp
    induction a using Polynomial.induction_on' <;> aesop (add norm add_mul)

中文:
定理 Bivariate.aevalAeval_swap
  条件: (x y : A) (p : R[X][Y])
  证明: by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
    simp
    induction a using Polynomial.induction_on' <;> aesop (add norm add_mul)

Depends on / 依赖: Polynomial, Polynomial.induction_on, add_mul, induction_on, monomial
-/
theorem Bivariate.aevalAeval_swap (x y : A) (p : R[X][Y]) :
    aevalAeval x y (swap p) = aevalAeval y x p := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
    simp
    induction a using Polynomial.induction_on' <;> aesop (add norm add_mul)

attribute [local instance] Polynomial.algebra in
/--
theorem `Bivariate.aveal_eq_map_swap` / 定理 `Bivariate.aveal_eq_map_swap`

English:
theorem Bivariate.aveal_eq_map_swap
  given: (x : A) (p : R[X][Y])
  proof: by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
      simp
      induction a using Polynomial.induction_on'
        <;> aesop (add norm [add_mul, C_mul_X_pow_eq_monomial])

中文:
定理 Bivariate.aveal_eq_map_swap
  条件: (x : A) (p : R[X][Y])
  证明: by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
      simp
      induction a using Polynomial.induction_on'
        <;> aesop (add norm [add_mul, C_mul_X_pow_eq_monomial])

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.induction_on, add_mul, induction_on, monomial
-/
theorem Bivariate.aveal_eq_map_swap (x : A) (p : R[X][Y]) :
    aeval (C x) p = mapAlgHom (aeval x) (swap p) := by
  induction p using Polynomial.induction_on' with
  | add => aesop
  | monomial n a =>
      simp
      induction a using Polynomial.induction_on'
        <;> aesop (add norm [add_mul, C_mul_X_pow_eq_monomial])

end

end aevalAeval

namespace Bivariate
section MvPolynomial

variable {R : Type*} [CommSemiring R]

variable (R) in
/-- The equiv between `R[X][Y]` and `R[X, Y]`. -/
noncomputable
/--
Definition of `equivMvPolynomial` / `equivMvPolynomial` 的定义

English:
definition equivMvPolynomial
  signature: : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R
  body: .ofAlgHom (aevalAeval (.X 0) (.X 1)) (MvPolynomial.aeval ![.C X, X])
    (by ext i; fin_cases i <;> simp) (by ext <;> simp)

@[simp]

中文:
定义 equivMvPolynomial
  签名: : R[X][Y] ≃ₐ[R] 多元多项式 (有限集 2) R
  定义体: .ofAlgHom (aevalAeval (.X 0) (.X 1)) (MvPolynomial.aeval ![.C X, X])
    (by ext i; fin_cases i <;> simp) (by ext <;> simp)

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, aevalAeval, fin_cases, ofAlgHom
-/
def equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R :=
  .ofAlgHom (aevalAeval (.X 0) (.X 1)) (MvPolynomial.aeval ![.C X, X])
    (by ext i; fin_cases i <;> simp) (by ext <;> simp)

@[simp]
/--
lemma `equivMvPolynomial_C_C` / 引理 `equivMvPolynomial_C_C`

English:
lemma equivMvPolynomial_C_C
  given: {a}
  statement: equivMvPolynomial R (C (C a)) = .C a
  proof: by
  simp [equivMvPolynomial]

@[simp]

中文:
引理 equivMvPolynomial_C_C
  条件: {a}
  结论: equivMvPolynomial R (C (C a)) = .C a
  证明: by
  simp [equivMvPolynomial]

@[simp]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_C_C {a} : equivMvPolynomial R (C (C a)) = .C a := by
  simp [equivMvPolynomial]

@[simp]
/--
lemma `equivMvPolynomial_C_X` / 引理 `equivMvPolynomial_C_X`

English:
lemma equivMvPolynomial_C_X
  statement: equivMvPolynomial R (C X) = .X 0
  proof: by
  simp [equivMvPolynomial]

@[simp]

中文:
引理 equivMvPolynomial_C_X
  结论: equivMvPolynomial R (C X) = .X 0
  证明: by
  simp [equivMvPolynomial]

@[simp]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_C_X : equivMvPolynomial R (C X) = .X 0 := by
  simp [equivMvPolynomial]

@[simp]
/--
lemma `equivMvPolynomial_X` / 引理 `equivMvPolynomial_X`

English:
lemma equivMvPolynomial_X
  statement: equivMvPolynomial R X = .X 1
  proof: by
  simp [equivMvPolynomial]

@[simp]

中文:
引理 equivMvPolynomial_X
  结论: equivMvPolynomial R X = .X 1
  证明: by
  simp [equivMvPolynomial]

@[simp]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_X : equivMvPolynomial R X = .X 1 := by
  simp [equivMvPolynomial]

@[simp]
/--
lemma `equivMvPolynomial_symm_X_0` / 引理 `equivMvPolynomial_symm_X_0`

English:
lemma equivMvPolynomial_symm_X_0
  statement: (equivMvPolynomial R).symm (.X 0) = C X
  proof: by
  simp [equivMvPolynomial]

@[simp]

中文:
引理 equivMvPolynomial_symm_X_0
  结论: (equivMvPolynomial R).symm (.X 0) = C X
  证明: by
  simp [equivMvPolynomial]

@[simp]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_symm_X_0 : (equivMvPolynomial R).symm (.X 0) = C X := by
  simp [equivMvPolynomial]

@[simp]
/--
lemma `equivMvPolynomial_symm_X_1` / 引理 `equivMvPolynomial_symm_X_1`

English:
lemma equivMvPolynomial_symm_X_1
  statement: (equivMvPolynomial R).symm (.X 1) = X
  proof: by
  simp [equivMvPolynomial]

@[simp]

中文:
引理 equivMvPolynomial_symm_X_1
  结论: (equivMvPolynomial R).symm (.X 1) = X
  证明: by
  simp [equivMvPolynomial]

@[simp]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_symm_X_1 : (equivMvPolynomial R).symm (.X 1) = X := by
  simp [equivMvPolynomial]

@[simp]
/--
lemma `equivMvPolynomial_symm_C` / 引理 `equivMvPolynomial_symm_C`

English:
lemma equivMvPolynomial_symm_C
  given: (a : R)
  statement: (equivMvPolynomial R).symm (.C a) = C (C a)
  proof: by
  simp [equivMvPolynomial]

中文:
引理 equivMvPolynomial_symm_C
  条件: (a : R)
  结论: (equivMvPolynomial R).symm (.C a) = C (C a)
  证明: by
  simp [equivMvPolynomial]

Depends on / 依赖: equivMvPolynomial
-/
lemma equivMvPolynomial_symm_C (a : R) : (equivMvPolynomial R).symm (.C a) = C (C a) := by
  simp [equivMvPolynomial]

/--
lemma `pderiv_zero_equivMvPolynomial` / 引理 `pderiv_zero_equivMvPolynomial`

English:
lemma pderiv_zero_equivMvPolynomial
  given: {R : Type*} [CommRing R] (p : R[X][Y])
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [map_nsmul]

中文:
引理 pderiv_zero_equivMvPolynomial
  条件: {R : 类型} [交换环 R] (p : R[X][Y])
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [map_nsmul]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.induction_on, induction_on, map_nsmul, monomial, simp_rw
-/
lemma pderiv_zero_equivMvPolynomial {R : Type*} [CommRing R] (p : R[X][Y]) :
    (equivMvPolynomial R p).pderiv 0 = equivMvPolynomial R
      (PolynomialModule.equivPolynomialSelf (derivative'.mapCoeffs p)) := by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [map_nsmul]

/--
lemma `pderiv_one_equivMvPolynomial` / 引理 `pderiv_one_equivMvPolynomial`

English:
lemma pderiv_one_equivMvPolynomial
  given: (p : R[X][Y])
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [derivative_pow]

中文:
引理 pderiv_one_equivMvPolynomial
  条件: (p : R[X][Y])
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [derivative_pow]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.induction_on, derivative_pow, induction_on, monomial, simp_rw
-/
lemma pderiv_one_equivMvPolynomial (p : R[X][Y]) :
    (equivMvPolynomial R p).pderiv 1 = equivMvPolynomial R (derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial n p =>
  induction p using Polynomial.induction_on' with
  | add p q _ _ => aesop
  | monomial m a =>
    simp_rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [derivative_pow]

end MvPolynomial

end Bivariate

end Polynomial

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)

/--
Definition of `evalEval` / `evalEval` 的定义

English:
definition evalEval
  signature: : AdjoinRoot p ->+* R
  body: lift (evalRingHom x) y eval₂_evalRingHom x ▸ h

中文:
定义 evalEval
  签名: : AdjoinRoot p ->+* R
  定义体: lift (evalRingHom x) y eval₂_evalRingHom x ▸ h
-/
@[simps!] noncomputable def evalEval : AdjoinRoot p ->+* R :=
lift (evalRingHom x) y eval₂_evalRingHom x ▸ h

/--
lemma `evalEval_mk` / 引理 `evalEval_mk`

English:
lemma evalEval_mk
  given: (g : R[X][Y])
  statement: evalEval h (mk p g) = g.evalEval x y
  proof: by
  rw [evalEval]; rw [lift_mk]; rw [eval₂_evalRingHom]

中文:
引理 evalEval_mk
  条件: (g : R[X][Y])
  结论: evalEval h (mk p g) = g.evalEval x y
  证明: by
  rw [evalEval]; rw [lift_mk]; rw [eval₂_evalRingHom]

Depends on / 依赖: evalEval, lift_mk
-/
lemma evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y := by
  rw [evalEval]; rw [lift_mk]; rw [eval₂_evalRingHom]

end AdjoinRoot
