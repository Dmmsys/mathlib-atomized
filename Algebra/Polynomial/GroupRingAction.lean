/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `MulSemiringAction` to `Polynomial`.
-/

@[expose] public section


variable (M : Type*) [Monoid M]

open Polynomial

namespace Polynomial

variable (R : Type*) [Semiring R]

variable {M} in
-- In this statement, we use `HSMul.hSMul m` as LHS instead of `(m • ·)`
-- to avoid a spurious lambda-expression that complicates rewriting with this lemma.
/--
theorem `smul_eq_map` / 定理 `smul_eq_map`

English:
theorem smul_eq_map
  given: [MulSemiringAction M R] (m : M)
  proof: by
  ext
  simp

中文:
定理 smul_eq_map
  条件: [MulSemiring作用 M R] (m : M)
  证明: by
  ext
  simp
-/
theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulSemiringAction
  signature: M R] : MulSemiringAction M R[X]
  body: { Polynomial.distribMulAction with
    smul_one := fun m =>
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ =>
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

中文:
实例 [MulSemiring作用
  签名: M R] : MulSemiring作用 M R[X]
  定义体: { Polynomial.distribMulAction with
    smul_one := fun m =>
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ =>
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingHom, Polynomial, Polynomial.distribMulAction, Polynomial.map_mul, Polynomial.map_one, distribMulAction, map_mul, map_one, smul_eq_map, smul_mul, smul_one, toRingHom
-/
noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul_one := fun m =>
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ =>
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

variable {M R}
variable [MulSemiringAction M R]

@[simp]
/--
theorem `smul_X` / 定理 `smul_X`

English:
theorem smul_X
  given: (m : M)
  statement: (m • X : R[X]) = X
  proof: (smul_eq_map R m).symm ▸ map_X _

中文:
定理 smul_X
  条件: (m : M)
  结论: (m • X : R[X]) = X
  证明: (smul_eq_map R m).symm ▸ map_X _

Depends on / 依赖: map_X, smul_eq_map
-/
theorem smul_X (m : M) : (m • X : R[X]) = X :=
  (smul_eq_map R m).symm ▸ map_X _

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]

/--
theorem `smul_eval_smul` / 定理 `smul_eval_smul`

English:
theorem smul_eval_smul
  given: (m : M) (f : S[X]) (x : S)
  statement: (m • f).eval (m • x) = m • f.eval x
  proof: Polynomial.induction_on f (fun r => by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg => by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ => by
    rw [smul_mul']; rw [smul_pow']; rw [smul_C]; rw [smul_X]; rw [eval_mul]; rw [eval_C]; rw [eval_X_pow]; rw [eval_mul]; rw [eval_C];

中文:
定理 smul_eval_smul
  条件: (m : M) (f : S[X]) (x : S)
  结论: (m • f).eval (m • x) = m • f.eval x
  证明: Polynomial.induction_on f (fun r => by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg => by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ => by
    rw [smul_mul']; rw [smul_pow']; rw [smul_C]; rw [smul_X]; rw [eval_mul]; rw [eval_C]; rw [eval_X_pow]; rw [eval_mul]; rw [eval_C];

Depends on / 依赖: Polynomial, Polynomial.induction_on, eval_C, eval_X_pow, eval_add, eval_mul, induction_on, smul_C, smul_X, smul_add, smul_mul, smul_pow
-/
theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x :=
  Polynomial.induction_on f (fun r => by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg => by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ => by
    rw [smul_mul']; rw [smul_pow']; rw [smul_C]; rw [smul_X]; rw [eval_mul]; rw [eval_C]; rw [eval_X_pow]; rw [eval_mul]; rw [eval_C]; rw [eval_X_pow]; rw [smul_mul']; rw [smul_pow']

variable (G : Type*) [Group G]

/--
theorem `eval_smul'` / 定理 `eval_smul'`

English:
theorem eval_smul'
  given: [MulSemiringAction G S] (g : G) (f : S[X]) (x : S)
  proof: by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

中文:
定理 eval_smul'
  条件: [MulSemiring作用 G S] (g : G) (f : S[X]) (x : S)
  证明: by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

Depends on / 依赖: smul_eval_smul, smul_inv_smul
-/
theorem eval_smul' [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    f.eval (g • x) = g • (g⁻¹ • f).eval x := by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

/--
theorem `smul_eval` / 定理 `smul_eval`

English:
theorem smul_eval
  given: [MulSemiringAction G S] (g : G) (f : S[X]) (x : S)
  proof: by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

中文:
定理 smul_eval
  条件: [MulSemiring作用 G S] (g : G) (f : S[X]) (x : S)
  证明: by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

Depends on / 依赖: smul_eval_smul, smul_inv_smul
-/
theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by
  rw [← smul_eval_smul]; rw [smul_inv_smul]

end Polynomial

section CommRing

variable (G : Type*) [Group G] [Fintype G]
variable (R : Type*) [CommRing R] [MulSemiringAction G R]

open MulAction

/--
Definition of `prodXSubSMul` / `prodXSubSMul` 的定义

English:
definition prodXSubSMul
  signature: (x : R)
  body: letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g =>
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)

中文:
定义 prodXSubSMul
  签名: (x : R)
  定义体: letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g =>
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.univ, MulAction, MulAction.stabilizer, Polynomial, Polynomial.C, Polynomial.X, ofQuotientStabilizer, stabilizer
-/
noncomputable def prodXSubSMul (x : R) : R[X] :=
  letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g =>
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)

/--
theorem `prodXSubSMul.monic` / 定理 `prodXSubSMul.monic`

English:
theorem prodXSubSMul.monic
  given: (x : R)
  statement: (prodXSubSMul G R x).Monic
  proof: Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

中文:
定理 prodXSubSMul.monic
  条件: (x : R)
  结论: (prodXSubSMul G R x).Monic
  证明: Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

Depends on / 依赖: Polynomial, Polynomial.monic_X_sub_C, Polynomial.monic_prod_of_monic, monic_X_sub_C, monic_prod_of_monic
-/
theorem prodXSubSMul.monic (x : R) : (prodXSubSMul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

/--
theorem `prodXSubSMul.eval` / 定理 `prodXSubSMul.eval`

English:
theorem prodXSubSMul.eval
  given: (x : R)
  statement: (prodXSubSMul G R x).eval x = 0
  proof: letI := Classical.decEq R
(map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] ->* R) _ _).trans
Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) by simp

中文:
定理 prodXSubSMul.eval
  条件: (x : R)
  结论: (prodXSubSMul G R x).eval x = 0
  证明: letI := Classical.decEq R
(map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] ->* R) _ _).trans
Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) by simp

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.mem_univ, Finset.prod_eq_zero, Polynomial, Polynomial.aeval, QuotientGroup, QuotientGroup.mk, map_prod, mem_univ, prod_eq_zero, toMonoidHom, toRingHom, toRingHom.toMonoidHom
-/
theorem prodXSubSMul.eval (x : R) : (prodXSubSMul G R x).eval x = 0 :=
  letI := Classical.decEq R
(map_prod ((Polynomial.aeval x).toRingHom.toMonoidHom : R[X] ->* R) _ _).trans
Finset.prod_eq_zero (Finset.mem_univ <| QuotientGroup.mk 1) by simp

/--
theorem `prodXSubSMul.smul` / 定理 `prodXSubSMul.smul`

English:
theorem prodXSubSMul.smul
  given: (x : R) (g : G)
  statement: g • prodXSubSMul G R x = prodXSubSMul G R x
  proof: letI := Classical.decEq R
Finset.smul_prod'.trans
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' => by
      rw [ofQuotientStabilizer_smul]; rw [smul_sub]; rw [Polynomial.smul_X]; rw [Polynomial.smul_C]

中文:
定理 prodXSubSMul.smul
  条件: (x : R) (g : G)
  结论: g • prodXSubSMul G R x = prodXSubSMul G R x
  证明: letI := Classical.decEq R
Finset.smul_prod'.trans
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' => by
      rw [ofQuotientStabilizer_smul]; rw [smul_sub]; rw [Polynomial.smul_X]; rw [Polynomial.smul_C]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.smul_prod, Fintype, Fintype.prod_bijective, MulAction, MulAction.bijective, Polynomial, Polynomial.smul_C, Polynomial.smul_X, bijective, ofQuotientStabilizer_smul, prod_bijective, smul_C, smul_X, smul_prod, smul_sub
-/
theorem prodXSubSMul.smul (x : R) (g : G) : g • prodXSubSMul G R x = prodXSubSMul G R x :=
  letI := Classical.decEq R
Finset.smul_prod'.trans
    Fintype.prod_bijective _ (MulAction.bijective g) _ _ fun g' => by
      rw [ofQuotientStabilizer_smul]; rw [smul_sub]; rw [Polynomial.smul_X]; rw [Polynomial.smul_C]

/--
theorem `prodXSubSMul.coeff` / 定理 `prodXSubSMul.coeff`

English:
theorem prodXSubSMul.coeff
  given: (x : R) (g : G) (n : Nat)
  proof: by
  rw [← Polynomial.coeff_smul]; rw [prodXSubSMul.smul]

中文:
定理 prodXSubSMul.coeff
  条件: (x : R) (g : G) (n : 自然数)
  证明: by
  rw [← Polynomial.coeff_smul]; rw [prodXSubSMul.smul]

Depends on / 依赖: Polynomial, Polynomial.coeff_smul, coeff_smul, prodXSubSMul, prodXSubSMul.smul
-/
theorem prodXSubSMul.coeff (x : R) (g : G) (n : Nat) :
    g • (prodXSubSMul G R x).coeff n = (prodXSubSMul G R x).coeff n := by
  rw [← Polynomial.coeff_smul]; rw [prodXSubSMul.smul]

end CommRing

namespace MulSemiringActionHom

variable {M}
variable {P : Type*} [CommSemiring P] [MulSemiringAction M P]
variable {Q : Type*} [CommSemiring Q] [MulSemiringAction M Q]

open Polynomial

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def polynomial (g : P ->+*[M] Q)
  body: map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b => by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq => by
        rw [smul_add]; rw [Polynomial.map_add]; rw [ihp]; rw [ihq]; rw [Polynomial.map_add]; rw 

中文:
定义 noncomputable
  签名: def polynomial (g : P ->+*[M] Q)
  定义体: map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b => by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq => by
        rw [smul_add]; rw [Polynomial.map_add]; rw [ihp]; rw [ihq]; rw [Polynomial.map_add]; rw 
-/
protected noncomputable def polynomial (g : P ->+*[M] Q) : P[X] ->+*[M] Q[X] where
  toFun := map g
  map_smul' m p :=
    Polynomial.induction_on p
      (fun b => by rw [MonoidHom.id_apply, smul_C, map_C, coe_fn_coe, g.map_smul, map_C,
          coe_fn_coe, smul_C])
      (fun p q ihp ihq => by
        rw [smul_add]; rw [Polynomial.map_add]; rw [ihp]; rw [ihq]; rw [Polynomial.map_add]; rw [smul_add])
      fun n b _ => by rw [MonoidHom.id_apply, smul_mul', smul_C, smul_pow', smul_X,
        Polynomial.map_mul, map_C, Polynomial.map_pow,
        map_X, coe_fn_coe, g.map_smul, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X,
        smul_mul', smul_C, smul_pow', smul_X, coe_fn_coe]
  map_zero' := Polynomial.map_zero (g : P ->+* Q)
  map_add' _ _ := Polynomial.map_add (g : P ->+* Q)
  map_one' := Polynomial.map_one (g : P ->+* Q)
  map_mul' _ _ := Polynomial.map_mul (g : P ->+* Q)

@[simp]
/--
theorem `coe_polynomial` / 定理 `coe_polynomial`

English:
theorem coe_polynomial
  given: (g : P ->+*[M] Q)
  statement: (g.polynomial : P[X] -> Q[X]) = map g
  proof: rfl

中文:
定理 coe_polynomial
  条件: (g : P ->+*[M] Q)
  结论: (g.polynomial : P[X] -> Q[X]) = map g
  证明: rfl
-/
theorem coe_polynomial (g : P ->+*[M] Q) : (g.polynomial : P[X] -> Q[X]) = map g := rfl

end MulSemiringActionHom
