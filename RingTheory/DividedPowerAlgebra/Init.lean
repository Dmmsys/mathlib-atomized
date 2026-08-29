/-
Copyright (c) 2026 Antoine Chambert-Loir & María Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos—Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.RingTheory.Congruence.BigOperators
public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# The universal divided power algebra

Let `R` be a (commutative) semiring and `M` be an `R`-module. In this file we define `Γ_R(M)`,
the universal divided power algebra of `M`, as the ring quotient of the polynomial ring
in the variables `ℕ × M` by the relation `DividedPowerAlgebra.Rel`.

`DividedPowerAlgebra R M` satisfies a weak universal property for morphisms to rings with
divided powers (`DividedPowerAlgebra.lift`).

## Main definitions

* `DividedPowerAlgebra.Rel`: the type coding the basic relations that will give rise to the
  divided power algebra.

* `DividedPowerAlgebra R M`: the universal divided power algebra of the `R`-module `M`,
  defined as `RingCon.Quotient` of `DividedPowerAlgebra.ringCon R M`.

* `DividedPowerAlgebra.dp R n m`: for `n : ℕ` and `m : M`, this is the equivalence class of
  `MvPolynomial.X (⟨n, m⟩)` in `DividedPowerAlgebra R M`.

  When that algebra is endowed with its canonical divided power structure (to be defined),
  the image of `MvPolynomial.X (n, m)`, for any `n : ℕ` and `m : M`, is equal to
  the `n`th divided power of the image of `m`.

  The API will be setup so that it is never (never say never…) necessary to lift to `MvPolynomial`.

* `DividedPowerAlgebra.lift`: the weak universal property of `DividedPowerAlgebra R M`.

* `DividedPowerAlgebra.map`: the functoriality map between divided power algebras
  associated with a linear map of the underlying modules.
  Given an `R`-algebra `S`, an `S`-module `N` and an `R`-linear map `f : M →ₗ[R] N`,
  this is the map `DividedPowerAlgebra R M →ₐ[R] DividedPowerAlgebra S N`
  sending `dp R n m` to `dp S n (f m)`.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## TODO

* Show in upcoming files that `DividedPowerAlgebra R M` has divided powers.


-/

@[expose] public section

noncomputable section

open Finset Ideal MvPolynomial

variable (α R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace DividedPowerAlgebra

/--
Inductive type `Rel` / 归纳类型 `Rel`

English:
inductive Rel
  parameters: : MvPolynomial (Nat × M) R -> MvPolynomial (Nat × M) R -> Prop
  constructors (5):
    - rfl_zero: Rel 0 0 -- Needed for technical reasons.
    - zero: {a : M} : Rel (X (0, a)) 1
    - smul: {r : R} {n : Nat} {a : M} : Rel (X (n, r • a)) (r ^ n • X (n, a))
    - mul: {m n : Nat} {a : M} : Rel (X (m, a) * X (n, a)) (Nat.choose (m + n) m • X (m + n, a))
    - add: {n : Nat} {a b : M} : Rel (X (n, a + b)) ((Finset.antidiagonal n).sum fun k => X (k.1, a) * X (k.2, b))

中文:
归纳类型 关系
  参数: : 多元多项式 (自然数 × M) R -> 多元多项式 (自然数 × M) R -> 命题
  构造子 (5 个):
    - rfl_zero: 关系 0 0 -- Needed for technical reasons.
    - zero: {a : M} : 关系 (X (0, a)) 1
    - smul: {r : R} {n : 自然数} {a : M} : 关系 (X (n, r • a)) (r ^ n • X (n, a))
    - mul: {m n : 自然数} {a : M} : 关系 (X (m, a) * X (n, a)) (自然数.choose (m + n) m • X (m + n, a))
    - add: {n : 自然数} {a b : M} : 关系 (X (n, a + b)) ((有限集.antidiagonal n).求和 fun k => X (k.1, a) * X (k.2, b))
-/
inductive Rel : MvPolynomial (Nat × M) R -> MvPolynomial (Nat × M) R -> Prop
  | rfl_zero : Rel 0 0 -- Needed for technical reasons.
  | zero {a : M} : Rel (X (0, a)) 1
  | smul {r : R} {n : Nat} {a : M} : Rel (X (n, r • a)) (r ^ n • X (n, a))
  | mul {m n : Nat} {a : M} : Rel (X (m, a) * X (n, a)) (Nat.choose (m + n) m • X (m + n, a))
  | add {n : Nat} {a b : M} :
    Rel (X (n, a + b)) ((Finset.antidiagonal n).sum fun k => X (k.1, a) * X (k.2, b))

/--
Definition of `RelI` / `RelI` 的定义

English:
definition RelI
  signature: : Ideal (MvPolynomial (Nat × M) R)
  body: ofRel (DividedPowerAlgebra.Rel R M)

中文:
定义 RelI
  签名: : 理想 (多元多项式 (自然数 × M) R)
  定义体: ofRel (DividedPowerAlgebra.Rel R M)

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.Rel
-/
def RelI : Ideal (MvPolynomial (Nat × M) R) := ofRel (DividedPowerAlgebra.Rel R M)

/--
Definition of `ringCon` / `ringCon` 的定义

English:
definition ringCon
  signature: : RingCon (MvPolynomial (Nat × M) R)
  body: ringConGen (DividedPowerAlgebra.Rel R M)

中文:
定义 ringCon
  签名: : RingCon (多元多项式 (自然数 × M) R)
  定义体: ringConGen (DividedPowerAlgebra.Rel R M)

Depends on / 依赖: Algebra, Algebra.FiniteType, DividedPowerAlgebra, DividedPowerAlgebra.Rel, Finite, FiniteType, Module, Module.Finite, algebraize, example, expected, f.toAlgebra, provided, ringConGen, toAlgebra
-/
def ringCon : RingCon (MvPolynomial (Nat × M) R) := ringConGen (DividedPowerAlgebra.Rel R M)

end DividedPowerAlgebra

/-- The divided power algebra of a module M is defined as the ring quotient of the polynomial ring
  in the variables `ℕ × M` by the ring relation defined by `DividedPowerAlgebra.Rel`.
  We will later show that that `DividedPowerAlgebra R M` has divided powers.
  It satisfies a weak universal property for morphisms to rings with divided powers. -/
.Quotient abbrev DividedPowerAlgebra := DividedPowerAlgebra.ringCon R M

namespace DividedPowerAlgebra

open MvPolynomial

variable {R M}

/--
lemma `mkAlgHom_surjective` / 引理 `mkAlgHom_surjective`

English:
lemma mkAlgHom_surjective
  statement: Function.Surjective (RingCon.mkₐ R (ringCon R M))
  proof: Quotient.mk_surjective

@[simp]

中文:
引理 mkAlgHom_surjective
  结论: 函数.满射 (RingCon.mkₐ R (ringCon R M))
  证明: Quotient.mk_surjective

@[simp]

Depends on / 依赖: Algebra, Algebra.Flat.out, Finite, Module, Module.Finite, Quotient, Quotient.mk_surjective, algebraize, definitionally, example, f.toAlgebra, mk_surjective, parameter, properties, toAlgebra
-/
lemma mkAlgHom_surjective : Function.Surjective (RingCon.mkₐ R (ringCon R M)) :=
  Quotient.mk_surjective

@[simp]
/--
lemma `coe_C` / 引理 `coe_C`

English:
lemma coe_C
  given: (a : R)
  proof: by
  rw [← MvPolynomial.algebraMap_eq]; rw [RingCon.coe_algebraMap]

@[deprecated coe_C (since := "2026-06-19")]

中文:
引理 coe_C
  条件: (a : R)
  证明: by
  rw [← MvPolynomial.algebraMap_eq]; rw [RingCon.coe_algebraMap]

@[deprecated coe_C (since := "2026-06-19")]

Depends on / 依赖: DividedPowerAlgebra, MvPolynomial, MvPolynomial.algebraMap_eq, RingCon, RingCon.coe_algebraMap, algebraMap, algebraMap_eq, coe_algebraMap, infer_instance
-/
lemma coe_C (a : R) :
    ↑(C (σ := Nat × M) a) = algebraMap R (DividedPowerAlgebra R M) a := by
  rw [← MvPolynomial.algebraMap_eq]; rw [RingCon.coe_algebraMap]

@[deprecated coe_C (since := "2026-06-19")]
/--
lemma `mkAlgHom_C` / 引理 `mkAlgHom_C`

English:
lemma mkAlgHom_C
  given: (a : R)
  proof: by
  rw [← MvPolynomial.algebraMap_eq]; rw [AlgHom.commutes]

@[deprecated coe_C (since := "2026-06-19")]

中文:
引理 mkAlgHom_C
  条件: (a : R)
  证明: by
  rw [← MvPolynomial.algebraMap_eq]; rw [AlgHom.commutes]

@[deprecated coe_C (since := "2026-06-19")]

Depends on / 依赖: AlgHom, AlgHom.commutes, MvPolynomial, MvPolynomial.algebraMap_eq, algebraMap_eq, commutes
-/
lemma mkAlgHom_C (a : R) :
    RingCon.mkₐ R (ringCon R M) (C a) = algebraMap R (DividedPowerAlgebra R M) a := by
  rw [← MvPolynomial.algebraMap_eq]; rw [AlgHom.commutes]

@[deprecated coe_C (since := "2026-06-19")]
/--
lemma `mkRingHom_C` / 引理 `mkRingHom_C`

English:
lemma mkRingHom_C
  given: (a : R)
  proof: mkAlgHom_C _

中文:
引理 mkRingHom_C
  条件: (a : R)
  证明: mkAlgHom_C _

Depends on / 依赖: mkAlgHom_C
-/
lemma mkRingHom_C (a : R) :
    RingCon.mk' (ringCon R M) (C a) = algebraMap R (DividedPowerAlgebra R M) a :=
  mkAlgHom_C _

variable (R) in
/--
Definition of `dp` / `dp` 的定义

English:
definition dp
  signature: (n : Nat) (m : M)
  body: ↑(X (n, m) : MvPolynomial (Nat × M) R)

中文:
定义 dp
  签名: (n : 自然数) (m : M)
  定义体: ↑(X (n, m) : MvPolynomial (Nat × M) R)

Depends on / 依赖: MvPolynomial
-/
def dp (n : Nat) (m : M) : DividedPowerAlgebra R M := ↑(X (n, m) : MvPolynomial (Nat × M) R)

/--
theorem `dp_def` / 定理 `dp_def`

English:
theorem dp_def
  given: (n : Nat) (m : M)
  proof: rfl

中文:
定理 dp_def
  条件: (n : 自然数) (m : M)
  证明: rfl
-/
theorem dp_def (n : Nat) (m : M) :
  dp R n m = ↑(X (n, m) : MvPolynomial (Nat × M) R) := rfl

/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {P : DividedPowerAlgebra R M -> Prop} (f : DividedPowerAlgebra R M)
  proof: by
  induction f using Quot.induction_on with | _ F
  dsimp
  induction F using MvPolynomial.induction_on with
  | C a => exact h_C a
  | add g1 g2 hg1 hg2 =>
    rw [RingCon.coe_add]
    exact h_add _ _ hg1 hg2
  | mul_X g nm h =>
    rw [RingCon.coe_mul]
    exact h_dp _ _ _ h

@[elab_as_elim]

中文:
定理 induction_on'
  结论: {P : DividedPowerAlgebra R M -> 命题} (f : DividedPowerAlgebra R M)
  证明: by
  induction f using Quot.induction_on with | _ F
  dsimp
  induction F using MvPolynomial.induction_on with
  | C a => exact h_C a
  | add g1 g2 hg1 hg2 =>
    rw [RingCon.coe_add]
    exact h_add _ _ hg1 hg2
  | mul_X g nm h =>
    rw [RingCon.coe_mul]
    exact h_dp _ _ _ h

@[elab_as_elim]
-/
protected theorem induction_on' {P : DividedPowerAlgebra R M -> Prop} (f : DividedPowerAlgebra R M)
    (h_C : forall a, P (C a : MvPolynomial (Nat × M) R)) (h_add : forall f g, P f -> P g -> P (f + g))
    (h_dp : forall (f : DividedPowerAlgebra R M) (n : Nat) (m : M), P f -> P (f * dp R n m)) : P f := by
  induction f using Quot.induction_on with | _ F
  dsimp
  induction F using MvPolynomial.induction_on with
  | C a => exact h_C a
  | add g1 g2 hg1 hg2 =>
    rw [RingCon.coe_add]
    exact h_add _ _ hg1 hg2
  | mul_X g nm h =>
    rw [RingCon.coe_mul]
    exact h_dp _ _ _ h

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {P : DividedPowerAlgebra R M -> Prop} (f : DividedPowerAlgebra R M)
  proof: DividedPowerAlgebra.induction_on' f C add dp

中文:
定理 induction_on
  结论: {P : DividedPowerAlgebra R M -> 命题} (f : DividedPowerAlgebra R M)
  证明: DividedPowerAlgebra.induction_on' f C add dp
-/
protected theorem induction_on {P : DividedPowerAlgebra R M -> Prop} (f : DividedPowerAlgebra R M)
    (C : forall a, P (algebraMap R _ a)) (add : forall f g, P f -> P g -> P (f + g))
    (dp : forall (f : DividedPowerAlgebra R M) (n : Nat) (m : M), P f -> P (f * dp R n m)) : P f :=
  DividedPowerAlgebra.induction_on' f C add dp

/--
theorem `dp_zero` / 定理 `dp_zero`

English:
theorem dp_zero
  given: {m : M}
  statement: dp R 0 m = 1
  proof: by
  rw [dp_def]; rw [← RingCon.coe_one]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.zero

中文:
定理 dp_zero
  条件: {m : M}
  结论: dp R 0 m = 1
  证明: by
  rw [dp_def]; rw [← RingCon.coe_one]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.zero

Depends on / 依赖: Quotient, Quotient.sound, Rel.zero, RingCon, RingCon.coe_one, RingCon.le_ringConGen, coe_one, dp_def, le_ringConGen
-/
theorem dp_zero {m : M} : dp R 0 m = 1 := by
  rw [dp_def]; rw [← RingCon.coe_one]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.zero

/--
theorem `dp_smul` / 定理 `dp_smul`

English:
theorem dp_smul
  given: {r : R} {n : Nat} {m : M}
  statement: dp R n (r • m) = r ^ n • dp R n m
  proof: by
  rw [dp_def]; rw [dp_def]; rw [← RingCon.coe_smul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.smul

中文:
定理 dp_smul
  条件: {r : R} {n : 自然数} {m : M}
  结论: dp R n (r • m) = r ^ n • dp R n m
  证明: by
  rw [dp_def]; rw [dp_def]; rw [← RingCon.coe_smul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.smul

Depends on / 依赖: Quotient, Quotient.sound, Rel.smul, RingCon, RingCon.coe_smul, RingCon.le_ringConGen, coe_smul, dp_def, le_ringConGen
-/
theorem dp_smul {r : R} {n : Nat} {m : M} : dp R n (r • m) = r ^ n • dp R n m := by
  rw [dp_def]; rw [dp_def]; rw [← RingCon.coe_smul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.smul

/--
theorem `dp_null` / 定理 `dp_null`

English:
theorem dp_null
  given: {n : Nat}
  statement: dp R n (0 : M) = if n = 0 then 1 else 0
  proof: by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    rw [if_pos hn]; rw [hn]; rw [dp_zero]
  | inr hn =>
    rw [if_neg (ne_of_gt hn)]; rw [← zero_smul R (0 : M)]; rw [dp_smul]
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]; rw [zero_smul]

中文:
定理 dp_null
  条件: {n : 自然数}
  结论: dp R n (0 : M) = if n = 0 then 1 else 0
  证明: by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    rw [if_pos hn]; rw [hn]; rw [dp_zero]
  | inr hn =>
    rw [if_neg (ne_of_gt hn)]; rw [← zero_smul R (0 : M)]; rw [dp_smul]
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]; rw [zero_smul]

Depends on / 依赖: Nat.eq_zero_or_pos, Nat.pos_iff_ne_zero.mp, dp_smul, dp_zero, eq_zero_or_pos, if_neg, if_pos, ne_of_gt, pos_iff_ne_zero, zero_pow, zero_smul
-/
theorem dp_null {n : Nat} : dp R n (0 : M) = if n = 0 then 1 else 0 := by
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    rw [if_pos hn]; rw [hn]; rw [dp_zero]
  | inr hn =>
    rw [if_neg (ne_of_gt hn)]; rw [← zero_smul R (0 : M)]; rw [dp_smul]
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]; rw [zero_smul]

/--
theorem `dp_null_of_ne_zero` / 定理 `dp_null_of_ne_zero`

English:
theorem dp_null_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  statement: dp R n (0 : M) = 0
  proof: by
  rw [dp_null]; rw [if_neg hn]

中文:
定理 dp_null_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  结论: dp R n (0 : M) = 0
  证明: by
  rw [dp_null]; rw [if_neg hn]

Depends on / 依赖: dp_null, if_neg
-/
theorem dp_null_of_ne_zero {n : Nat} (hn : n != 0) : dp R n (0 : M) = 0 := by
  rw [dp_null]; rw [if_neg hn]

/--
theorem `dp_mul` / 定理 `dp_mul`

English:
theorem dp_mul
  given: {n p : Nat} {m : M}
  proof: by
  simp only [dp_def, ← RingCon.coe_mul, ← RingCon.coe_nsmul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.mul

中文:
定理 dp_mul
  条件: {n p : 自然数} {m : M}
  证明: by
  simp only [dp_def, ← RingCon.coe_mul, ← RingCon.coe_nsmul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.mul

Depends on / 依赖: NeZero, Quotient, Quotient.sound, Rel.mul, RingCon, RingCon.coe_mul, RingCon.coe_nsmul, RingCon.le_ringConGen, coe_mul, coe_nsmul, dp_def, le_ringConGen
-/
theorem dp_mul {n p : Nat} {m : M} :
    dp R n m * dp R p m = (n + p).choose n • dp R (n + p) m := by
  simp only [dp_def, ← RingCon.coe_mul, ← RingCon.coe_nsmul]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.mul

/--
theorem `dp_add` / 定理 `dp_add`

English:
theorem dp_add
  given: {n : Nat} {x y : M}
  proof: by
  simp_rw [dp_def, ← RingCon.coe_mul, ← RingCon.coe_finsetSum]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.add

中文:
定理 dp_add
  条件: {n : 自然数} {x y : M}
  证明: by
  simp_rw [dp_def, ← RingCon.coe_mul, ← RingCon.coe_finsetSum]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.add

Depends on / 依赖: Quotient, Quotient.sound, Rel.add, RingCon, RingCon.coe_finsetSum, RingCon.coe_mul, RingCon.le_ringConGen, coe_finsetSum, coe_mul, dp_def, le_ringConGen, simp_rw
-/
theorem dp_add {n : Nat} {x y : M} :
    dp R n (x + y) = (antidiagonal n).sum fun k => dp R k.1 x * dp R k.2 y := by
  simp_rw [dp_def, ← RingCon.coe_mul, ← RingCon.coe_finsetSum]
exact Quotient.sound RingCon.le_ringConGen _ _ Rel.add

/--
theorem `dp_sum` / 定理 `dp_sum`

English:
theorem dp_sum
  given: {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : Nat) (x : ι -> M)
  proof: DividedPowers.dpow_sum' (I := ⊤) _ (fun _ => dp_zero)
    (fun _ _ => dp_add) dp_null_of_ne_zero (fun _ _ => trivial)

中文:
定理 dp_sum
  条件: {ι : 类型} [DecidableEq ι] (s : 有限集 ι) (q : 自然数) (x : ι -> M)
  证明: DividedPowers.dpow_sum' (I := ⊤) _ (fun _ => dp_zero)
    (fun _ _ => dp_add) dp_null_of_ne_zero (fun _ _ => trivial)

Depends on / 依赖: DividedPowers, DividedPowers.dpow_sum, dp_add, dp_null_of_ne_zero, dp_zero, dpow_sum
-/
theorem dp_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : Nat) (x : ι -> M) :
    dp R q (s.sum x) =
      (Finset.sym s q).sum fun k => s.prod fun i => dp R (Multiset.count i k) (x i) :=
  DividedPowers.dpow_sum' (I := ⊤) _ (fun _ => dp_zero)
    (fun _ _ => dp_add) dp_null_of_ne_zero (fun _ _ => trivial)

/--
theorem `dp_sum_smul` / 定理 `dp_sum_smul`

English:
theorem dp_sum_smul
  given: {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : Nat) (a : ι -> R) (x : ι -> M)
  proof: by
  simp_rw [dp_sum, dp_smul, Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]

中文:
定理 dp_sum_smul
  条件: {ι : 类型} [DecidableEq ι] (s : 有限集 ι) (q : 自然数) (a : ι -> R) (x : ι -> M)
  证明: by
  simp_rw [dp_sum, dp_smul, Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.prod_mul_distrib, abs.map_pow, dp_smul, dp_sum, map_pow, map_prod, mul_comm, mul_sub_one, pow_two, prod_mul_distrib, simp_rw, smul_def
-/
theorem dp_sum_smul {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : Nat) (a : ι -> R) (x : ι -> M) :
    dp R q (s.sum fun i => a i • x i) =
      (Finset.sym s q).sum fun k =>
        (s.prod fun i => a i ^ Multiset.count i k) •
          s.prod fun i => dp R (Multiset.count i k) (x i) := by
  simp_rw [dp_sum, dp_smul, Algebra.smul_def, map_prod, ← Finset.prod_mul_distrib]

open Nat in
/--
lemma `prod_dp` / 引理 `prod_dp`

English:
lemma prod_dp
  given: {ι : Type*} {s : Finset ι} {n : ι -> Nat} {m : M}
  proof: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul, dp_zero]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (dp R (n _) m)]; rw [mul_assoc]; rw [dp_mul]; rw [← sum_insert hi]; rw [nsmul_eq_mul]; rw [← mul_assoc]
    congr 1
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

中文:
引理 prod_dp
  条件: {ι : 类型} {s : 有限集 ι} {n : ι -> 自然数} {m : M}
  证明: by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul, dp_zero]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (dp R (n _) m)]; rw [mul_assoc]; rw [dp_mul]; rw [← sum_insert hi]; rw [nsmul_eq_mul]; rw [← mul_assoc]
    congr 1
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

Depends on / 依赖: Finset, Finset.induction, cast_mul, cast_one, classical, dp_mul, dp_zero, insert, mul_assoc, mul_comm, multinomial_empty, multinomial_insert, nsmul_eq_mul, one_mul, prod_empty, prod_insert, sum_empty, sum_insert
-/
lemma prod_dp {ι : Type*} {s : Finset ι} {n : ι -> Nat} {m : M} :
    ∏ i in s, (dp R (n i) m) = (Nat.multinomial s n) * dp R (s.sum n) m := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul, dp_zero]
  | insert _ _ hi hrec =>
    rw [prod_insert hi]; rw [hrec]; rw [← mul_assoc]; rw [mul_comm (dp R (n _) m)]; rw [mul_assoc]; rw [dp_mul]; rw [← sum_insert hi]; rw [nsmul_eq_mul]; rw [← mul_assoc]
    congr 1
    rw [multinomial_insert hi]; rw [mul_comm]; rw [cast_mul]; rw [sum_insert hi]

open scoped Nat

/--
theorem `natFactorial_mul_dp_eq` / 定理 `natFactorial_mul_dp_eq`

English:
theorem natFactorial_mul_dp_eq
  given: (n : Nat) (x : M)
  proof: by
  induction n with
  | zero => simp [dp_zero]
  | succ n h =>
    rw [pow_succ]; rw [← h]; rw [mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [← Nat.cast_mul]
    simp [mul_comm _ (n + 1), Nat.factorial_succ]

中文:
定理 natFactorial_mul_dp_eq
  条件: (n : 自然数) (x : M)
  证明: by
  induction n with
  | zero => simp [dp_zero]
  | succ n h =>
    rw [pow_succ]; rw [← h]; rw [mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [← Nat.cast_mul]
    simp [mul_comm _ (n + 1), Nat.factorial_succ]

Depends on / 依赖: Nat.cast_mul, Nat.factorial_succ, cast_mul, dp_mul, dp_zero, factorial_succ, mul_assoc, mul_comm, nsmul_eq_mul, pow_succ
-/
theorem natFactorial_mul_dp_eq (n : Nat) (x : M) :
    n ! * dp R n x = (dp R 1 x) ^ n := by
  induction n with
  | zero => simp [dp_zero]
  | succ n h =>
    rw [pow_succ]; rw [← h]; rw [mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [← mul_assoc]; rw [← Nat.cast_mul]
    simp [mul_comm _ (n + 1), Nat.factorial_succ]

variable (R M) in
/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: : M ->ₗ[R] DividedPowerAlgebra R M where
  body: dp R 1 m
  map_add' _ _ := by simp [dp_add, Nat.antidiagonal_succ, dp_zero, add_comm]
  map_smul' _ _ := by simp [dp_smul, pow_one, RingHom.id_apply]

中文:
定义 embed
  签名: : M ->ₗ[R] DividedPowerAlgebra R M where
  定义体: dp R 1 m
  map_add' _ _ := by simp [dp_add, Nat.antidiagonal_succ, dp_zero, add_comm]
  map_smul' _ _ := by simp [dp_smul, pow_one, RingHom.id_apply]
-/
def embed : M ->ₗ[R] DividedPowerAlgebra R M where
  toFun m := dp R 1 m
  map_add' _ _ := by simp [dp_add, Nat.antidiagonal_succ, dp_zero, add_comm]
  map_smul' _ _ := by simp [dp_smul, pow_one, RingHom.id_apply]

/--
theorem `embed_def` / 定理 `embed_def`

English:
theorem embed_def
  given: (m : M)
  statement: embed R M m = dp R 1 m
  proof: rfl

中文:
定理 embed_def
  条件: (m : M)
  结论: embed R M m = dp R 1 m
  证明: rfl
-/
theorem embed_def (m : M) : embed R M m = dp R 1 m := rfl

/--
theorem `algHom_ext_iff` / 定理 `algHom_ext_iff`

English:
theorem algHom_ext_iff
  statement: {A : Type*} [CommSemiring A] [Algebra R A]
  proof: by
  refine ⟨fun h _ _ => by rw [h], fun h => ?_⟩
  rw [DFunLike.ext'_iff]
  apply Function.Surjective.injective_comp_right mkAlgHom_surjective
  simpa [← AlgHom.coe_comp] using MvPolynomial.algHom_ext fun ⟨n, m⟩ => h n m

@[ext]

中文:
定理 algHom_ext_iff
  结论: {A : 类型} [交换半环 A] [代数 R A]
  证明: by
  refine ⟨fun h _ _ => by rw [h], fun h => ?_⟩
  rw [DFunLike.ext'_iff]
  apply Function.Surjective.injective_comp_right mkAlgHom_surjective
  simpa [← AlgHom.coe_comp] using MvPolynomial.algHom_ext fun ⟨n, m⟩ => h n m

@[ext]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, DFunLike, DFunLike.ext, Function, Function.Surjective.injective_comp_right, MvPolynomial, MvPolynomial.algHom_ext, Surjective, _iff, algHom_ext, coe_comp, injective_comp_right, mkAlgHom_surjective
-/
theorem algHom_ext_iff {A : Type*} [CommSemiring A] [Algebra R A]
    {f g : DividedPowerAlgebra R M ->ₐ[R] A} :
    f = g ↔ forall n m, f (dp R n m) = g (dp R n m) := by
  refine ⟨fun h _ _ => by rw [h], fun h => ?_⟩
  rw [DFunLike.ext'_iff]
  apply Function.Surjective.injective_comp_right mkAlgHom_surjective
  simpa [← AlgHom.coe_comp] using MvPolynomial.algHom_ext fun ⟨n, m⟩ => h n m

@[ext]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  statement: {A : Type*} [CommSemiring A] [Algebra R A]
  proof: algHom_ext_iff.mpr h

中文:
定理 algHom_ext
  结论: {A : 类型} [交换半环 A] [代数 R A]
  证明: algHom_ext_iff.mpr h

Depends on / 依赖: algHom_ext_iff, algHom_ext_iff.mpr
-/
theorem algHom_ext {A : Type*} [CommSemiring A] [Algebra R A]
    {f g : DividedPowerAlgebra R M ->ₐ[R] A}
    (h : forall n m, f (dp R n m) = g (dp R n m)) : f = g :=
  algHom_ext_iff.mpr h

section

open Submodule

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι -> M}

/--
theorem `submodule_span_prod_dp_eq_top` / 定理 `submodule_span_prod_dp_eq_top`

English:
theorem submodule_span_prod_dp_eq_top
  given: (hv : span R (Set.range v) = ⊤)
  proof: by
  rw [eq_top_iff]
  intro p hp
  clear hp
  induction p using DividedPowerAlgebra.induction_on with
  | C r =>
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ (subset_span ⟨0, by simp⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | dp x k m hx =>
    have hm : m in span R (Set.range v) := by simp [hv, mem_top]
    induction hm using span_induction generalizing x k with
    | zero => rw [dp_null]; split_ifs <;> simp [hx]
    | smul r m hm h => simp [dp_smul, smul_mem _ _ (h x k hx)]
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      induction hx using span_induction with
      | zero => simp
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        simp only
        rw [← n.mul_prod_erase' i _ (fun i => dp_zero (m := v i))]; rw [mul_comm]; rw [← mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← nsmul_eq_mul]
        refine smul_of_tower_mem _ _ (mem_span_of_mem ⟨Finsupp.single i k + n, ?_⟩)
        simp only
        rw [← (Finsupp.single i k + n).mul_prod_erase' i _ (fun i => dp_zero (m := v i))]
        simp
      | add x y hxmem hymem hx hy =>
        rw [add_mul]
        exact Submodule.add_mem _ hx hy
      | smul r x hxmem hx =>
        rw [smul_mul_assoc]
        exact smul_mem _ _ hx
    | add m n hm_mem hn_mem hm hn =>
      rw [dp_add]; rw [mul_sum]
      apply sum_mem (fun c hc => ?_)
      rw [← mul_assoc]
      exact hn (x * dp R c.1 m) c.2 (hm x c.1 hx)

中文:
定理 submodule_span_prod_dp_eq_top
  条件: (hv : span R (集合.range v) = ⊤)
  证明: by
  rw [eq_top_iff]
  intro p hp
  clear hp
  induction p using DividedPowerAlgebra.induction_on with
  | C r =>
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ (subset_span ⟨0, by simp⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | dp x k m hx =>
    have hm : m in span R (Set.range v) := by simp [hv, mem_top]
    induction hm using span_induction generalizing x k with
    | zero => rw [dp_null]; split_ifs <;> simp [hx]
    | smul r m hm h => simp [dp_smul, smul_mem _ _ (h x k hx)]
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      induction hx using span_induction with
      | zero => simp
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        simp only
        rw [← n.mul_prod_erase' i _ (fun i => dp_zero (m := v i))]; rw [mul_comm]; rw [← mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← nsmul_eq_mul]
        refine smul_of_tower_mem _ _ (mem_span_of_mem ⟨Finsupp.single i k + n, ?_⟩)
        simp only
        rw [← (Finsupp.single i k + n).mul_prod_erase' i _ (fun i => dp_zero (m := v i))]
        simp
      | add x y hxmem hymem hx hy =>
        rw [add_mul]
        exact Submodule.add_mem _ hx hy
      | smul r x hxmem hx =>
        rw [smul_mul_assoc]
        exact smul_mem _ _ hx
    | add m n hm_mem hn_mem hm hn =>
      rw [dp_add]; rw [mul_sum]
      apply sum_mem (fun c hc => ?_)
      rw [← mul_assoc]
      exact hn (x * dp R c.1 m) c.2 (hm x c.1 hx)

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, DividedPowerAlgebra, DividedPowerAlgebra.induction_on, Set.range, Submodule, Submodule.add_mem, add_mem, algebraMap_eq_smul_one, dp_null, dp_smul, eq_top_iff, generalizing, induction_on, mem_top, smul_mem, span_induction, split_ifs, subset_span
-/
theorem submodule_span_prod_dp_eq_top (hv : span R (Set.range v) = ⊤) :
    span R (Set.range fun (n : ι ->₀ Nat) => n.prod fun i k => dp R k (v i)) = ⊤ := by
  rw [eq_top_iff]
  intro p hp
  clear hp
  induction p using DividedPowerAlgebra.induction_on with
  | C r =>
    simp only [Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ (subset_span ⟨0, by simp⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | dp x k m hx =>
    have hm : m in span R (Set.range v) := by simp [hv, mem_top]
    induction hm using span_induction generalizing x k with
    | zero => rw [dp_null]; split_ifs <;> simp [hx]
    | smul r m hm h => simp [dp_smul, smul_mem _ _ (h x k hx)]
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      induction hx using span_induction with
      | zero => simp
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        simp only
        rw [← n.mul_prod_erase' i _ (fun i => dp_zero (m := v i))]; rw [mul_comm]; rw [← mul_assoc]; rw [dp_mul]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← nsmul_eq_mul]
        refine smul_of_tower_mem _ _ (mem_span_of_mem ⟨Finsupp.single i k + n, ?_⟩)
        simp only
        rw [← (Finsupp.single i k + n).mul_prod_erase' i _ (fun i => dp_zero (m := v i))]
        simp
      | add x y hxmem hymem hx hy =>
        rw [add_mul]
        exact Submodule.add_mem _ hx hy
      | smul r x hxmem hx =>
        rw [smul_mul_assoc]
        exact smul_mem _ _ hx
    | add m n hm_mem hn_mem hm hn =>
      rw [dp_add]; rw [mul_sum]
      apply sum_mem (fun c hc => ?_)
      rw [← mul_assoc]
      exact hn (x * dp R c.1 m) c.2 (hm x c.1 hx)

/--
lemma `pow_dp` / 引理 `pow_dp`

English:
lemma pow_dp
  given: (n : Nat) (m : M) (k : Nat)
  proof: by
  rw [Multiset.multinomial_nsmul_singleton]; rw [← Fin.prod_const]; rw [prod_dp]
  simp [Nat.multinomial]

中文:
引理 pow_dp
  条件: (n : 自然数) (m : M) (k : 自然数)
  证明: by
  rw [Multiset.multinomial_nsmul_singleton]; rw [← Fin.prod_const]; rw [prod_dp]
  simp [Nat.multinomial]

Depends on / 依赖: Fin.prod_const, Multiset, Multiset.multinomial_nsmul_singleton, Nat.multinomial, mul_comm, mul_sub_one, multinomial, multinomial_nsmul_singleton, norm_pow, pow_two, prod_const, prod_dp
-/
lemma pow_dp (n : Nat) (m : M) (k : Nat) :
    (dp R n m) ^ k = (Multiset.multinomial (k • {n})) * dp R (k * n) m := by
  rw [Multiset.multinomial_nsmul_singleton]; rw [← Fin.prod_const]; rw [prod_dp]
  simp [Nat.multinomial]

end

section UniversalProperty

variable (R M)

variable {A : Type*} [CommSemiring A] [Algebra R A]

/--
theorem `lift'_imp` / 定理 `lift'_imp`

English:
theorem lift'_imp
  statement: {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
  proof: by
  rcases h <;>
  simp_all

中文:
定理 lift'_imp
  结论: {f : 自然数 × M -> A} (hf_zero : 对任意 m, f (0, m) = 1)
  证明: by
  rcases h <;>
  simp_all
-/
private theorem lift'_imp {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
    (hf_smul : forall (n : Nat) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : forall n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : forall n u v, f ⟨n, u + v⟩ = (antidiagonal n).sum fun (k, l) => f ⟨k, u⟩ * f ⟨l, v⟩)
    (p q : MvPolynomial (Nat × M) R) (h : (Rel R M) p q) :
    eval₂AlgHom R f p = eval₂AlgHom R f q := by
  rcases h <;>
  simp_all

variable {R M}

/--
Definition of `lift'` / `lift'` 的定义

English:
definition lift'
  signature: {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
  body: RingCon.liftₐ _ (eval₂AlgHom R f) by
    grw [ringCon, RingCon.ringConGen_le]
    exact lift'_imp R M hf_zero hf_smul hf_mul hf_add

@[simp]

中文:
定义 lift'
  签名: {f : 自然数 × M -> A} (hf_zero : 对任意 m, f (0, m) = 1)
  定义体: RingCon.liftₐ _ (eval₂AlgHom R f) by
    grw [ringCon, RingCon.ringConGen_le]
    exact lift'_imp R M hf_zero hf_smul hf_mul hf_add

@[simp]

Depends on / 依赖: RingCon, RingCon.lift, RingCon.ringConGen_le, _imp, factorial_succ, factorial_zero, hf_add, hf_mul, hf_smul, hf_zero, mul_pos, ringCon, ringConGen_le, succ_pos
-/
def lift' {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
    (hf_smul : forall (n : Nat) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : forall n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : forall n u v, f ⟨n, u + v⟩ = (antidiagonal n).sum fun (k, l) => f ⟨k, u⟩ * f ⟨l, v⟩) :
    DividedPowerAlgebra R M ->ₐ[R] A :=
RingCon.liftₐ _ (eval₂AlgHom R f) by
    grw [ringCon, RingCon.ringConGen_le]
    exact lift'_imp R M hf_zero hf_smul hf_mul hf_add

@[simp]
/--
theorem `lift'_apply` / 定理 `lift'_apply`

English:
theorem lift'_apply
  statement: {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
  proof: by
  simp [lift', aeval_eq_eval₂Hom]

@[simp]

中文:
定理 lift'_apply
  结论: {f : 自然数 × M -> A} (hf_zero : 对任意 m, f (0, m) = 1)
  证明: by
  simp [lift', aeval_eq_eval₂Hom]

@[simp]
-/
theorem lift'_apply {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
    (hf_smul : forall (n : Nat) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : forall n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : forall n u v, f ⟨n, u + v⟩ = (antidiagonal n).sum fun (k, l) => f ⟨k, u⟩ * f ⟨l, v⟩)
    (p : MvPolynomial (Nat × M) R) :
    lift' hf_zero hf_smul hf_mul hf_add ↑p = aeval f p := by
  simp [lift', aeval_eq_eval₂Hom]

@[simp]
/--
theorem `lift'_apply_dp` / 定理 `lift'_apply_dp`

English:
theorem lift'_apply_dp
  statement: {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
  proof: by
  rw [dp_def]; rw [lift'_apply hf_zero hf_smul hf_mul hf_add]; rw [aeval_X]

中文:
定理 lift'_apply_dp
  结论: {f : 自然数 × M -> A} (hf_zero : 对任意 m, f (0, m) = 1)
  证明: by
  rw [dp_def]; rw [lift'_apply hf_zero hf_smul hf_mul hf_add]; rw [aeval_X]
-/
theorem lift'_apply_dp {f : Nat × M -> A} (hf_zero : forall m, f (0, m) = 1)
    (hf_smul : forall (n : Nat) (r : R) (m : M), f ⟨n, r • m⟩ = r ^ n • f ⟨n, m⟩)
    (hf_mul : forall n p m, f ⟨n, m⟩ * f ⟨p, m⟩ = (n + p).choose n • f ⟨n + p, m⟩)
    (hf_add : forall n u v, f ⟨n, u + v⟩ = (antidiagonal n).sum fun (k, l) => f ⟨k, u⟩ * f ⟨l, v⟩)
    (n : Nat) (m : M) :
    lift' hf_zero hf_smul hf_mul hf_add (dp R n m) = f ⟨n, m⟩ := by
  rw [dp_def]; rw [lift'_apply hf_zero hf_smul hf_mul hf_add]; rw [aeval_X]

variable {I : Ideal A} (hI : DividedPowers I) (g : M ->ₗ[R] A) (hg : forall m, g m in I)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : DividedPowerAlgebra R M ->ₐ[R] A
  body: lift' (f := fun nm => hI.dpow nm.1 (g nm.2))
    (fun m => hI.dpow_zero (hg m))
    (fun n r m => by
      dsimp only
      rw [LinearMap.map_smulₛₗ]; rw [RingHom.id_apply]; rw [← algebraMap_smul A r (g m)]; rw [smul_eq_mul]; rw [hI.dpow_mul (hg m)]; rw [← smul_eq_mul]; rw [← map_pow]; rw [algebraMap_smul])
    (fun n p m => by rw [hI.mul_dpow (hg m), ← nsmul_eq_mul])
    (fun n u v => by simp [hI.dpow_add (hg u) (hg v)])

中文:
定义 lift
  签名: : DividedPowerAlgebra R M ->ₐ[R] A
  定义体: lift' (f := fun nm => hI.dpow nm.1 (g nm.2))
    (fun m => hI.dpow_zero (hg m))
    (fun n r m => by
      dsimp only
      rw [LinearMap.map_smulₛₗ]; rw [RingHom.id_apply]; rw [← algebraMap_smul A r (g m)]; rw [smul_eq_mul]; rw [hI.dpow_mul (hg m)]; rw [← smul_eq_mul]; rw [← map_pow]; rw [algebraMap_smul])
    (fun n p m => by rw [hI.mul_dpow (hg m), ← nsmul_eq_mul])
    (fun n u v => by simp [hI.dpow_add (hg u) (hg v)])

Depends on / 依赖: LinearMap, LinearMap.map_smul, RingHom, RingHom.id_apply, algebraMap_smul, dpow_add, dpow_mul, dpow_zero, hI.dpow, hI.dpow_add, hI.dpow_mul, hI.dpow_zero, hI.mul_dpow, id_apply, map_pow, mul_dpow, nsmul_eq_mul, smul_eq_mul
-/
def lift : DividedPowerAlgebra R M ->ₐ[R] A :=
  lift' (f := fun nm => hI.dpow nm.1 (g nm.2))
    (fun m => hI.dpow_zero (hg m))
    (fun n r m => by
      dsimp only
      rw [LinearMap.map_smulₛₗ]; rw [RingHom.id_apply]; rw [← algebraMap_smul A r (g m)]; rw [smul_eq_mul]; rw [hI.dpow_mul (hg m)]; rw [← smul_eq_mul]; rw [← map_pow]; rw [algebraMap_smul])
    (fun n p m => by rw [hI.mul_dpow (hg m), ← nsmul_eq_mul])
    (fun n u v => by simp [hI.dpow_add (hg u) (hg v)])

variable {g}

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (p : MvPolynomial (Nat × M) R)
  proof: by
  rw [lift]; rw [lift'_apply]

@[simp]

中文:
定理 lift_apply
  条件: (p : 多元多项式 (自然数 × M) R)
  证明: by
  rw [lift]; rw [lift'_apply]

@[simp]

Depends on / 依赖: _apply
-/
theorem lift_apply (p : MvPolynomial (Nat × M) R) :
    lift hI g hg ↑p = aeval (fun nm : Nat × M => hI.dpow nm.1 (g nm.2)) p := by
  rw [lift]; rw [lift'_apply]

@[simp]
/--
theorem `lift_apply_dp` / 定理 `lift_apply_dp`

English:
theorem lift_apply_dp
  given: (n : Nat) (m : M)
  proof: by rw [lift, lift'_apply_dp]

中文:
定理 lift_apply_dp
  条件: (n : 自然数) (m : M)
  证明: by rw [lift, lift'_apply_dp]

Depends on / 依赖: _apply_dp
-/
theorem lift_apply_dp (n : Nat) (m : M) :
    lift hI g hg (dp R n m) = hI.dpow n (g m) := by rw [lift, lift'_apply_dp]

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: {f : DividedPowerAlgebra R M ->ₐ[R] A}
  proof: algHom_ext (fun _ _ => by rw [lift_apply_dp, hf])

@[simp]

中文:
定理 lift_unique
  结论: {f : DividedPowerAlgebra R M ->ₐ[R] A}
  证明: algHom_ext (fun _ _ => by rw [lift_apply_dp, hf])

@[simp]

Depends on / 依赖: algHom_ext, lift_apply_dp
-/
theorem lift_unique {f : DividedPowerAlgebra R M ->ₐ[R] A}
    (hf : forall n m, f (dp R n m) = hI.dpow n (g m)) : f = lift hI g hg :=
  algHom_ext (fun _ _ => by rw [lift_apply_dp, hf])

@[simp]
/--
theorem `lift_embed_apply` / 定理 `lift_embed_apply`

English:
theorem lift_embed_apply
  given: (m : M)
  statement: lift hI g hg (embed R M m) = g m
  proof: by
  simp [embed_def, hI.dpow_one (hg m)]

@[simp]

中文:
定理 lift_embed_apply
  条件: (m : M)
  结论: lift hI g hg (embed R M m) = g m
  证明: by
  simp [embed_def, hI.dpow_one (hg m)]

@[simp]

Depends on / 依赖: dpow_one, embed_def, hI.dpow_one
-/
theorem lift_embed_apply (m : M) : lift hI g hg (embed R M m) = g m := by
  simp [embed_def, hI.dpow_one (hg m)]

@[simp]
/--
theorem `embed_comp_lift` / 定理 `embed_comp_lift`

English:
theorem embed_comp_lift
  statement: (lift hI g hg).toLinearMap.comp (embed R M) = g
  proof: by
  ext; simp

中文:
定理 embed_comp_lift
  结论: (lift hI g hg).toLinearMap.comp (embed R M) = g
  证明: by
  ext; simp
-/
theorem embed_comp_lift : (lift hI g hg).toLinearMap.comp (embed R M) = g := by
  ext; simp

end UniversalProperty

section Functoriality

section Map

variable {S : Type*} [CommSemiring S] {N : Type*} [AddCommMonoid N] [Module R N] [Module S N]
  (f : M ->ₗ[R] N)

namespace LinearMap

@[simp]
/--
lemma `dp_zero` / 引理 `dp_zero`

English:
lemma dp_zero
  given: {a : M}
  statement: dp S 0 (f a) = 1
  proof: DividedPowerAlgebra.dp_zero

中文:
引理 dp_zero
  条件: {a : M}
  结论: dp S 0 (f a) = 1
  证明: DividedPowerAlgebra.dp_zero

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.dp_zero, dp_zero
-/
lemma dp_zero {a : M} : dp S 0 (f a) = 1 := DividedPowerAlgebra.dp_zero

/--
lemma `dp_mul` / 引理 `dp_mul`

English:
lemma dp_mul
  given: {m n : Nat} {a : M}
  proof: DividedPowerAlgebra.dp_mul

中文:
引理 dp_mul
  条件: {m n : 自然数} {a : M}
  证明: DividedPowerAlgebra.dp_mul

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.dp_mul, dp_mul
-/
lemma dp_mul {m n : Nat} {a : M} :
    dp S m (f a) * dp S n (f a) = (Nat.choose (m + n) m) • dp S (m + n) (f a) :=
  DividedPowerAlgebra.dp_mul

/--
lemma `dp_add` / 引理 `dp_add`

English:
lemma dp_add
  given: {n : Nat} {a b : M}
  proof: by
  rw [map_add]; rw [DividedPowerAlgebra.dp_add]

中文:
引理 dp_add
  条件: {n : 自然数} {a b : M}
  证明: by
  rw [map_add]; rw [DividedPowerAlgebra.dp_add]

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.dp_add, dp_add, map_add
-/
lemma dp_add {n : Nat} {a b : M} :
    dp S n (f (a + b)) = (Finset.antidiagonal n).sum fun k => dp S k.1 (f a) * dp S k.2 (f b) := by
  rw [map_add]; rw [DividedPowerAlgebra.dp_add]

end LinearMap

section IsScalarTower

variable (S)

variable [Algebra R S] [IsScalarTower R S N]

/--
lemma `LinearMap.dp_smul` / 引理 `LinearMap.dp_smul`

English:
lemma LinearMap.dp_smul
  given: {n : Nat} {r : R} {a : M}
  statement: dp S n (f (r • a)) = r ^ n • dp S n (f a)
  proof: by
  rw [f.map_smul]; rw [algebra_compatible_smul S r (f a)]; rw [DividedPowerAlgebra.dp_smul]; rw [← map_pow]; rw [algebraMap_smul]

中文:
引理 线性映射.dp_smul
  条件: {n : 自然数} {r : R} {a : M}
  结论: dp S n (f (r • a)) = r ^ n • dp S n (f a)
  证明: by
  rw [f.map_smul]; rw [algebra_compatible_smul S r (f a)]; rw [DividedPowerAlgebra.dp_smul]; rw [← map_pow]; rw [algebraMap_smul]

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.dp_smul, algebraMap_smul, algebra_compatible_smul, dp_smul, f.map_smul, map_pow, map_smul
-/
lemma LinearMap.dp_smul {n : Nat} {r : R} {a : M} : dp S n (f (r • a)) = r ^ n • dp S n (f a) := by
  rw [f.map_smul]; rw [algebra_compatible_smul S r (f a)]; rw [DividedPowerAlgebra.dp_smul]; rw [← map_pow]; rw [algebraMap_smul]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : DividedPowerAlgebra R M ->ₐ[R] DividedPowerAlgebra S N
  body: DividedPowerAlgebra.lift' (f := fun nm => dp S nm.fst (f nm.snd))
    (fun _ => LinearMap.dp_zero f)
    (fun _ _ _ => LinearMap.dp_smul S f)
    (fun _ _ _ => LinearMap.dp_mul f)
    (fun _ _ _ => LinearMap.dp_add f)

@[simp]

中文:
定义 map
  签名: : DividedPowerAlgebra R M ->ₐ[R] DividedPowerAlgebra S N
  定义体: DividedPowerAlgebra.lift' (f := fun nm => dp S nm.fst (f nm.snd))
    (fun _ => LinearMap.dp_zero f)
    (fun _ _ _ => LinearMap.dp_smul S f)
    (fun _ _ _ => LinearMap.dp_mul f)
    (fun _ _ _ => LinearMap.dp_add f)

@[simp]

Depends on / 依赖: DividedPowerAlgebra, DividedPowerAlgebra.lift, LinearMap, LinearMap.dp_add, LinearMap.dp_mul, LinearMap.dp_smul, LinearMap.dp_zero, dp_add, dp_mul, dp_smul, dp_zero, nm.fst, nm.snd
-/
def map : DividedPowerAlgebra R M ->ₐ[R] DividedPowerAlgebra S N :=
  DividedPowerAlgebra.lift' (f := fun nm => dp S nm.fst (f nm.snd))
    (fun _ => LinearMap.dp_zero f)
    (fun _ _ _ => LinearMap.dp_smul S f)
    (fun _ _ _ => LinearMap.dp_mul f)
    (fun _ _ _ => LinearMap.dp_add f)

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {p : MvPolynomial (Nat × M) R}
  proof: by
  rw [map]; rw [lift'_apply]

@[simp]

中文:
定理 map_apply
  条件: {p : 多元多项式 (自然数 × M) R}
  证明: by
  rw [map]; rw [lift'_apply]

@[simp]

Depends on / 依赖: _apply
-/
theorem map_apply {p : MvPolynomial (Nat × M) R} :
    map S f ↑p = aeval (fun nm => dp S nm.fst (f nm.snd)) p := by
  rw [map]; rw [lift'_apply]

@[simp]
/--
theorem `map_apply_dp` / 定理 `map_apply_dp`

English:
theorem map_apply_dp
  given: {n : Nat} {a : M}
  statement: map S f (dp R n a) = dp S n (f a)
  proof: by
  rw [map]; rw [lift'_apply_dp]

@[simp]

中文:
定理 map_apply_dp
  条件: {n : 自然数} {a : M}
  结论: map S f (dp R n a) = dp S n (f a)
  证明: by
  rw [map]; rw [lift'_apply_dp]

@[simp]

Depends on / 依赖: _apply_dp
-/
theorem map_apply_dp {n : Nat} {a : M} : map S f (dp R n a) = dp S n (f a) := by
  rw [map]; rw [lift'_apply_dp]

@[simp]
/--
theorem `map_embed_apply` / 定理 `map_embed_apply`

English:
theorem map_embed_apply
  given: {m : M}
  statement: map S f (embed R M m) = embed S N (f m)
  proof: by
  simp [embed_def, map_apply_dp]

中文:
定理 map_embed_apply
  条件: {m : M}
  结论: map S f (embed R M m) = embed S N (f m)
  证明: by
  simp [embed_def, map_apply_dp]

Depends on / 依赖: embed_def, map_apply_dp
-/
theorem map_embed_apply {m : M} : map S f (embed R M m) = embed S N (f m) := by
  simp [embed_def, map_apply_dp]

/--
theorem `lift_comp_embed` / 定理 `lift_comp_embed`

English:
theorem lift_comp_embed
  proof: by
  ext; simp

中文:
定理 lift_comp_embed
  证明: by
  ext; simp
-/
theorem lift_comp_embed :
    (map S f).toLinearMap.comp (embed R M) = ((embed S N).restrictScalars R).comp f := by
  ext; simp

/--
theorem `lift_surjective` / 定理 `lift_surjective`

English:
theorem lift_surjective
  given: {f : M ->ₗ[R] N} (hf : Function.Surjective f)
  proof: by
  rw [← AlgHom.range_eq_top]; rw [← Algebra.map_top (map R f)]; rw [eq_top_iff]; rw [← (AlgHom.range_eq_top (RingCon.mkₐ R (ringCon R N))).mpr mkAlgHom_surjective]; rw [← Algebra.map_top]; rw [(Subalgebra.gc_map_comap _).le_iff_le]; rw [← MvPolynomial.adjoin_range_X]; rw [Algebra.adjoin_le_iff]
  intro
  simp only [Set.mem_range, Prod.exists]
  rintro ⟨n, m, rfl⟩
  obtain ⟨l, rfl⟩ := hf m
  simp only [Algebra.map_top, Subalgebra.coe_comap, AlgHom.coe_range, Set.mem_preimage,
    Set.mem_range, RingCon.mkₐ_apply]
  use dp R n l
  rw [map_apply_dp]; rw [dp]

中文:
定理 lift_surjective
  条件: {f : M ->ₗ[R] N} (hf : 函数.满射 f)
  证明: by
  rw [← AlgHom.range_eq_top]; rw [← Algebra.map_top (map R f)]; rw [eq_top_iff]; rw [← (AlgHom.range_eq_top (RingCon.mkₐ R (ringCon R N))).mpr mkAlgHom_surjective]; rw [← Algebra.map_top]; rw [(Subalgebra.gc_map_comap _).le_iff_le]; rw [← MvPolynomial.adjoin_range_X]; rw [Algebra.adjoin_le_iff]
  intro
  simp only [Set.mem_range, Prod.exists]
  rintro ⟨n, m, rfl⟩
  obtain ⟨l, rfl⟩ := hf m
  simp only [Algebra.map_top, Subalgebra.coe_comap, AlgHom.coe_range, Set.mem_preimage,
    Set.mem_range, RingCon.mkₐ_apply]
  use dp R n l
  rw [map_apply_dp]; rw [dp]

Depends on / 依赖: AlgHom, AlgHom.coe_range, AlgHom.range_eq_top, Algebra, Algebra.adjoin_le_iff, Algebra.map_top, MvPolynomial, MvPolynomial.adjoin_range_X, Prod.exists, RingCon, RingCon.mk, Set.mem_preimage, Set.mem_range, Subalgebra, Subalgebra.coe_comap, Subalgebra.gc_map_comap, adjoin_le_iff, adjoin_range_X, coe_comap, coe_range
-/
theorem lift_surjective {f : M ->ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (map R f) := by
  rw [← AlgHom.range_eq_top]; rw [← Algebra.map_top (map R f)]; rw [eq_top_iff]; rw [← (AlgHom.range_eq_top (RingCon.mkₐ R (ringCon R N))).mpr mkAlgHom_surjective]; rw [← Algebra.map_top]; rw [(Subalgebra.gc_map_comap _).le_iff_le]; rw [← MvPolynomial.adjoin_range_X]; rw [Algebra.adjoin_le_iff]
  intro
  simp only [Set.mem_range, Prod.exists]
  rintro ⟨n, m, rfl⟩
  obtain ⟨l, rfl⟩ := hf m
  simp only [Algebra.map_top, Subalgebra.coe_comap, AlgHom.coe_range, Set.mem_preimage,
    Set.mem_range, RingCon.mkₐ_apply]
  use dp R n l
  rw [map_apply_dp]; rw [dp]

end IsScalarTower

end Map

variable (S : Type*) [CommSemiring S] {N : Type*} [AddCommMonoid N] [Module R N] [Module S N]
  (f : M ->ₗ[R] N)

section IsScalarTower

variable [Algebra R S] [IsScalarTower R S N] {P : Type*} [AddCommMonoid P] [Module R P]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: by
  rw [algHom_ext_iff]
  intros; simp [map_apply_dp]

@[simp]

中文:
引理 map_comp
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: by
  rw [algHom_ext_iff]
  intros; simp [map_apply_dp]

@[simp]

Depends on / 依赖: algHom_ext_iff, intros, map_apply_dp
-/
lemma map_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) :
    map R (g.comp f) = (map R g).comp (map R f) := by
  rw [algHom_ext_iff]
  intros; simp [map_apply_dp]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map R (LinearMap.id (R := R) (M := M)) = AlgHom.id R _
  proof: by
  rw [algHom_ext_iff]
  intros
  simp [map_apply_dp]

中文:
引理 map_id
  结论: map R (线性映射.id (R := R) (M := M)) = 代数态射.id R _
  证明: by
  rw [algHom_ext_iff]
  intros
  simp [map_apply_dp]

Depends on / 依赖: AlgHom, AlgHom.id, algHom_ext_iff, intros, map_apply_dp
-/
lemma map_id : map R (LinearMap.id (R := R) (M := M)) = AlgHom.id R _ := by
  rw [algHom_ext_iff]
  intros
  simp [map_apply_dp]

/-- The functoriality map between divided power algebras associated with a linear equivalence of
  the underlying modules. Given an `R`-algebra `S`, an `S`-module `N` and an `R`-linear equivalence
  `f : M →ₗ[R] N`, this is the map `DividedPowerAlgebra R M →ₐ[R] DividedPowerAlgebra S N`
  sending `dp R n m` to `dp S n (f m)`. -/
@[simps!]
/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (g : M ≃ₗ[R] N)
  body: AlgEquiv.ofAlgHom (map R g.toLinearMap) (map R g.symm.toLinearMap)
    (by simp [← map_comp, map_id]) (by simp [← map_comp, map_id])

中文:
定义 mapEquiv
  签名: (g : M ≃ₗ[R] N)
  定义体: AlgEquiv.ofAlgHom (map R g.toLinearMap) (map R g.symm.toLinearMap)
    (by simp [← map_comp, map_id]) (by simp [← map_comp, map_id])

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, g.symm.toLinearMap, g.toLinearMap, map_comp, map_id, ofAlgHom, toLinearMap
-/
def mapEquiv (g : M ≃ₗ[R] N) :
    DividedPowerAlgebra R M ≃ₐ[R] DividedPowerAlgebra R N :=
  AlgEquiv.ofAlgHom (map R g.toLinearMap) (map R g.symm.toLinearMap)
    (by simp [← map_comp, map_id]) (by simp [← map_comp, map_id])

/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: (g : M ≃ₗ[R] N)
  statement: (mapEquiv g).symm = mapEquiv g.symm
  proof: rfl

中文:
定理 mapEquiv_symm
  条件: (g : M ≃ₗ[R] N)
  结论: (mapEquiv g).symm = mapEquiv g.symm
  证明: rfl
-/
theorem mapEquiv_symm (g : M ≃ₗ[R] N) : (mapEquiv g).symm = mapEquiv g.symm := rfl

/--
theorem `LinearEquiv.coe_lift` / 定理 `LinearEquiv.coe_lift`

English:
theorem LinearEquiv.coe_lift
  given: (g : M ≃ₗ[R] N)
  statement: mapEquiv g = map R g.toLinearMap
  proof: rfl

中文:
定理 线性等价.coe_lift
  条件: (g : M ≃ₗ[R] N)
  结论: mapEquiv g = map R g.toLinearMap
  证明: rfl
-/
theorem LinearEquiv.coe_lift (g : M ≃ₗ[R] N) : mapEquiv g = map R g.toLinearMap := rfl

/--
theorem `LinearEquiv.coe_lift_symm` / 定理 `LinearEquiv.coe_lift_symm`

English:
theorem LinearEquiv.coe_lift_symm
  given: (g : M ≃ₗ[R] N)
  proof: rfl

中文:
定理 线性等价.coe_lift_symm
  条件: (g : M ≃ₗ[R] N)
  证明: rfl
-/
theorem LinearEquiv.coe_lift_symm (g : M ≃ₗ[R] N) :
    (mapEquiv g).symm = map R g.symm.toLinearMap := rfl

/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  statement: mapEquiv (LinearEquiv.refl R M) = AlgEquiv.refl
  proof: AlgEquiv.coe_toAlgHom_injective map_id

中文:
定理 mapEquiv_refl
  结论: mapEquiv (线性等价.refl R M) = 代数等价.refl
  证明: AlgEquiv.coe_toAlgHom_injective map_id

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, coe_toAlgHom_injective, map_id
-/
theorem mapEquiv_refl : mapEquiv (LinearEquiv.refl R M) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective map_id

/--
theorem `mapEquiv_trans` / 定理 `mapEquiv_trans`

English:
theorem mapEquiv_trans
  given: (g : M ≃ₗ[R] N) (h : N ≃ₗ[R] P)
  proof: AlgEquiv.coe_toAlgHom_injective (map_comp _ _).symm

中文:
定理 mapEquiv_trans
  条件: (g : M ≃ₗ[R] N) (h : N ≃ₗ[R] P)
  证明: AlgEquiv.coe_toAlgHom_injective (map_comp _ _).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom_injective, coe_toAlgHom_injective, map_comp
-/
theorem mapEquiv_trans (g : M ≃ₗ[R] N) (h : N ≃ₗ[R] P) :
    (mapEquiv g).trans (mapEquiv h) = mapEquiv (g.trans h) :=
  AlgEquiv.coe_toAlgHom_injective (map_comp _ _).symm

end IsScalarTower

end Functoriality

end DividedPowerAlgebra
