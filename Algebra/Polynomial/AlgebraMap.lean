/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monomial

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.

## Main definitions

- `Polynomial.aeval`: given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
  the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

- `Polynomial.mapAlgHom` : given `φ : S →ₐ[R] S'`, `mapAlgHom φ` applies `φ` on the
  coefficients of a polynomial in `S[X]`.

-/

@[expose] public section

assert_not_exists Ideal

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : Nat}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {p q r : R[X]}

/--
Instance `algebraOfAlgebra` / 实例 `algebraOfAlgebra`

English:
instance algebraOfAlgebra
  signature: : Algebra R A[X] where
  body: toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul]; rw [toFinsupp_mul]; rw [toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert! Algebra.commutes' r p.toFinsupp
  algebraMap := C.comp (algebraMap R A)

@[simp]

中文:
实例 algebraOfAlgebra
  签名: : 代数 R A[X] where
  定义体: toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul]; rw [toFinsupp_mul]; rw [toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert! Algebra.commutes' r p.toFinsupp
  algebraMap := C.comp (algebraMap R A)

@[simp]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, C.comp, RingHom, RingHom.comp_apply, RingHom.toFun_eq_coe, algebraMap, commutes, comp_apply, convert, p.toFinsupp, simp_rw, smul_def, toFinsupp, toFinsupp_C, toFinsupp_injective, toFinsupp_mul, toFinsupp_smul, toFun_eq_coe
-/
instance algebraOfAlgebra : Algebra R A[X] where
  smul_def' r p :=
toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul]; rw [toFinsupp_mul]; rw [toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
toFinsupp_injective by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert! Algebra.commutes' r p.toFinsupp
  algebraMap := C.comp (algebraMap R A)

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (r : R)
  statement: algebraMap R A[X] r = C (algebraMap R A r)
  proof: rfl

@[simp]

中文:
定理 algebraMap_apply
  条件: (r : R)
  结论: algebraMap R A[X] r = C (algebraMap R A r)
  证明: rfl

@[simp]
-/
theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl

@[simp]
/--
theorem `toFinsupp_algebraMap` / 定理 `toFinsupp_algebraMap`

English:
theorem toFinsupp_algebraMap
  given: (r : R)
  statement: (algebraMap R A[X] r).toFinsupp = algebraMap R _ r
  proof: show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl

中文:
定理 toFinsupp_algebraMap
  条件: (r : R)
  结论: (algebraMap R A[X] r).toFinsupp = algebraMap R _ r
  证明: show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl

Depends on / 依赖: algebraMap, toFinsupp, toFinsupp_C
-/
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  show toFinsupp (C (algebraMap _ _ r)) = _ by
    rw [toFinsupp_C]
    rfl

/--
theorem `ofFinsupp_algebraMap` / 定理 `ofFinsupp_algebraMap`

English:
theorem ofFinsupp_algebraMap
  given: (r : R)
  statement: (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r
  proof: toFinsupp_injective (toFinsupp_algebraMap _).symm

中文:
定理 ofFinsupp_algebraMap
  条件: (r : R)
  结论: (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r
  证明: toFinsupp_injective (toFinsupp_algebraMap _).symm

Depends on / 依赖: toFinsupp_algebraMap, toFinsupp_injective
-/
theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm

/--
theorem `C_eq_algebraMap` / 定理 `C_eq_algebraMap`

English:
theorem C_eq_algebraMap
  given: (r : R)
  statement: C r = algebraMap R R[X] r
  proof: rfl

@[simp]

中文:
定理 C_eq_algebraMap
  条件: (r : R)
  结论: C r = algebraMap R R[X] r
  证明: rfl

@[simp]
-/
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  rfl

@[simp]
/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: algebraMap R R[X] = C
  proof: rfl

中文:
定理 algebraMap_eq
  结论: algebraMap R R[X] = C
  证明: rfl
-/
theorem algebraMap_eq : algebraMap R R[X] = C :=
  rfl

/-- `Polynomial.C` as an `AlgHom`. -/
@[simps! apply]
/--
Definition of `CAlgHom` / `CAlgHom` 的定义

English:
definition CAlgHom
  signature: : A ->ₐ[R] A[X] where
  body: C
  commutes' _ := rfl

中文:
定义 CAlgHom
  签名: : A ->ₐ[R] A[X] where
  定义体: C
  commutes' _ := rfl
-/
def CAlgHom : A ->ₐ[R] A[X] where
  toRingHom := C
  commutes' _ := rfl

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
/--
theorem `algHom_ext'` / 定理 `algHom_ext'`

English:
theorem algHom_ext'
  statement: {f g : A[X] ->ₐ[R] B}
  proof: AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

中文:
定理 algHom_ext'
  结论: {f g : A[X] ->ₐ[R] B}
  证明: AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, AlgHom.toRingHom, coe_ringHom_injective, congr_arg, ringHom_ext, toRingHom
-/
theorem algHom_ext' {f g : A[X] ->ₐ[R] B}
    (hC : f.comp CAlgHom = g.comp CAlgHom)
    (hX : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

set_option backward.defeqAttrib.useBackward true in
variable (R) in
open AddMonoidAlgebra in
/-- Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
/--
Definition of `toFinsuppIsoAlg` / `toFinsuppIsoAlg` 的定义

English:
definition toFinsuppIsoAlg
  signature: : R[X] ≃ₐ[R] R[Nat]
  body: { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

中文:
定义 toFinsuppIsoAlg
  签名: : R[X] ≃ₐ[R] R[自然数]
  定义体: { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

Depends on / 依赖: commutes, toFinsuppIso
-/
def toFinsuppIsoAlg : R[X] ≃ₐ[R] R[Nat] :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

/--
Instance `subalgebraNontrivial` / 实例 `subalgebraNontrivial`

English:
instance subalgebraNontrivial
  signature: [Nontrivial A]
  body: ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply]
      intro x
      rw [ext_iff]; rw [not_forall]
      refine ⟨1, ?_⟩
      simp⟩⟩

@[simp]

中文:
实例 subalgebraNontrivial
  签名: [非平凡 A]
  定义体: ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply]
      intro x
      rw [ext_iff]; rw [not_forall]
      refine ⟨1, ?_⟩
      simp⟩⟩

@[simp]

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.mem_top, Set.mem_range, SetLike, SetLike.ext_iff, algebraMap_apply, ext_iff, iff_true, mem_bot, mem_range, mem_top, not_exists, not_forall
-/
instance subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X]) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne]; rw [SetLike.ext_iff]; rw [not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply]
      intro x
      rw [ext_iff]; rw [not_forall]
      refine ⟨1, ?_⟩
      simp⟩⟩

@[simp]
/--
theorem `algHom_eval₂_algebraMap` / 定理 `algHom_eval₂_algebraMap`

English:
theorem algHom_eval₂_algebraMap
  statement: {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  proof: by
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, AlgHom.commutes]

@[simp]

中文:
定理 algHom_eval₂_algebraMap
  结论: {R A B : 类型} [交换半环 R] [半环 A] [半环 B]
  证明: by
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, AlgHom.commutes]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.commutes, commutes, map_mul, map_pow, map_sum, sum_def
-/
theorem algHom_eval₂_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (p : R[X]) (f : A ->ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, AlgHom.commutes]

@[simp]
/--
theorem `eval₂_algebraMap_X` / 定理 `eval₂_algebraMap_X`

English:
theorem eval₂_algebraMap_X
  statement: {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
  proof: by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow]
  simp [Polynomial.C_eq_algebraMap]

中文:
定理 eval₂_algebraMap_X
  结论: {R A : 类型} [交换半环 R] [半环 A] [代数 R A] (p : R[X])
  证明: by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow]
  simp [Polynomial.C_eq_algebraMap]

Depends on / 依赖: C_eq_algebraMap, Polynomial, Polynomial.C_eq_algebraMap, Polynomial.sum_C_mul_X_pow_eq, conv_rhs, map_mul, map_pow, map_sum, sum_C_mul_X_pow_eq, sum_def
-/
theorem eval₂_algebraMap_X {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
    (f : R[X] ->ₐ[R] A) : eval₂ (algebraMap R A) (f X) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow]
  simp [Polynomial.C_eq_algebraMap]

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[simp]
/--
theorem `ringHom_eval₂_intCastRingHom` / 定理 `ringHom_eval₂_intCastRingHom`

English:
theorem ringHom_eval₂_intCastRingHom
  statement: {R S : Type*} [Ring R] [Ring S] (p : Int[X]) (f : R ->+* S)
  proof: algHom_eval₂_algebraMap p f.toIntAlgHom r

@[simp]

中文:
定理 ringHom_eval₂_intCastRingHom
  结论: {R S : 类型} [环 R] [环 S] (p : 整数[X]) (f : R ->+* S)
  证明: algHom_eval₂_algebraMap p f.toIntAlgHom r

@[simp]

Depends on / 依赖: f.toIntAlgHom, toIntAlgHom
-/
theorem ringHom_eval₂_intCastRingHom {R S : Type*} [Ring R] [Ring S] (p : Int[X]) (f : R ->+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  algHom_eval₂_algebraMap p f.toIntAlgHom r

@[simp]
/--
theorem `eval₂_intCastRingHom_X` / 定理 `eval₂_intCastRingHom_X`

English:
theorem eval₂_intCastRingHom_X
  given: {R : Type*} [Ring R] (p : Int[X]) (f : Int[X] ->+* R)
  proof: eval₂_algebraMap_X p f.toIntAlgHom

中文:
定理 eval₂_intCastRingHom_X
  条件: {R : 类型} [环 R] (p : 整数[X]) (f : 整数[X] ->+* R)
  证明: eval₂_algebraMap_X p f.toIntAlgHom

Depends on / 依赖: f.toIntAlgHom, toIntAlgHom
-/
theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : Int[X]) (f : Int[X] ->+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  eval₂_algebraMap_X p f.toIntAlgHom

/-- `Polynomial.eval₂` as an `AlgHom` for noncommutative algebras.

This is `Polynomial.eval₂RingHom'` for `AlgHom`s. -/
@[simps!]
/--
Definition of `eval₂AlgHom` / `eval₂AlgHom` 的定义

English:
definition eval₂AlgHom
  signature: (f : A ->ₐ[R] B) (b : B) (hf : forall a, Commute (f a) b)
  body: eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)

中文:
定义 eval₂AlgHom
  签名: (f : A ->ₐ[R] B) (b : B) (hf : 对任意 a, Commute (f a) b)
  定义体: eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)
-/
def eval₂AlgHom (f : A ->ₐ[R] B) (b : B) (hf : forall a, Commute (f a) b) : A[X] ->ₐ[R] B where
  toRingHom := eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)

section Map

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (f : A ->ₐ[R] B)
  body: mapRingHom f.toRingHom
  commutes' := by simp

@[simp]

中文:
定义 mapAlgHom
  签名: (f : A ->ₐ[R] B)
  定义体: mapRingHom f.toRingHom
  commutes' := by simp

@[simp]

Depends on / 依赖: f.toRingHom, mapRingHom, toRingHom
-/
def mapAlgHom (f : A ->ₐ[R] B) : Polynomial A ->ₐ[R] Polynomial B where
  toRingHom := mapRingHom f.toRingHom
  commutes' := by simp

@[simp]
/--
theorem `coe_mapAlgHom` / 定理 `coe_mapAlgHom`

English:
theorem coe_mapAlgHom
  given: (f : A ->ₐ[R] B)
  statement: ⇑(mapAlgHom f) = map f
  proof: rfl

@[simp]

中文:
定理 coe_mapAlgHom
  条件: (f : A ->ₐ[R] B)
  结论: ⇑(mapAlgHom f) = map f
  证明: rfl

@[simp]
-/
theorem coe_mapAlgHom (f : A ->ₐ[R] B) : ⇑(mapAlgHom f) = map f :=
  rfl

@[simp]
/--
theorem `mapAlgHom_id` / 定理 `mapAlgHom_id`

English:
theorem mapAlgHom_id
  statement: mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A)
  proof: AlgHom.ext fun _x => map_id

@[simp]

中文:
定理 mapAlgHom_id
  结论: mapAlgHom (代数态射.id R A) = 代数态射.id R (多项式 A)
  证明: AlgHom.ext fun _x => map_id

@[simp]

Depends on / 依赖: AlgHom, AlgHom.ext, map_id
-/
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) :=
  AlgHom.ext fun _x => map_id

@[simp]
/--
theorem `mapAlgHom_coe_ringHom` / 定理 `mapAlgHom_coe_ringHom`

English:
theorem mapAlgHom_coe_ringHom
  given: (f : A ->ₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 mapAlgHom_coe_ringHom
  条件: (f : A ->ₐ[R] B)
  证明: rfl

@[simp]
-/
theorem mapAlgHom_coe_ringHom (f : A ->ₐ[R] B) :
    ↑(mapAlgHom f : _ ->ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A ->+* Polynomial B) :=
  rfl

@[simp]
/--
theorem `mapAlgHom_comp` / 定理 `mapAlgHom_comp`

English:
theorem mapAlgHom_comp
  given: (C : Type*) [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B)
  proof: by
  ext <;> simp

中文:
定理 mapAlgHom_comp
  条件: (C : 类型) [半环 C] [代数 R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B)
  证明: by
  ext <;> simp
-/
theorem mapAlgHom_comp (C : Type*) [Semiring C] [Algebra R C] (f : B ->ₐ[R] C) (g : A ->ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by
  ext <;> simp

/--
theorem `mapAlgHom_eq_eval₂AlgHom_CAlgHom` / 定理 `mapAlgHom_eq_eval₂AlgHom_CAlgHom`

English:
theorem mapAlgHom_eq_eval₂AlgHom_CAlgHom
  given: (f : A ->ₐ[R] B)
  statement: mapAlgHom f = eval₂AlgHom
  proof: by
  rfl

中文:
定理 mapAlgHom_eq_eval₂AlgHom_CAlgHom
  条件: (f : A ->ₐ[R] B)
  结论: mapAlgHom f = eval₂AlgHom
  证明: by
  rfl
-/
theorem mapAlgHom_eq_eval₂AlgHom_CAlgHom (f : A ->ₐ[R] B) : mapAlgHom f = eval₂AlgHom
    (CAlgHom.comp f) X (fun a => (commute_X (C (f a))).symm) := by
  rfl

/--
lemma `coeff_mapAlgHom_apply` / 引理 `coeff_mapAlgHom_apply`

English:
lemma coeff_mapAlgHom_apply
  given: (f : A ->ₐ[R] B) (p : A[X]) (n : Nat)
  proof: by
  simp

中文:
引理 coeff_mapAlgHom_apply
  条件: (f : A ->ₐ[R] B) (p : A[X]) (n : 自然数)
  证明: by
  simp
-/
lemma coeff_mapAlgHom_apply (f : A ->ₐ[R] B) (p : A[X]) (n : Nat) :
    coeff (mapAlgHom f p) n = f (coeff p n) := by
  simp

/--
lemma `lcoeff_comp_mapAlgHom_eq` / 引理 `lcoeff_comp_mapAlgHom_eq`

English:
lemma lcoeff_comp_mapAlgHom_eq
  given: (f : A ->ₐ[R] B) (n : Nat)
  proof: by
  ext f; simp

中文:
引理 lcoeff_comp_mapAlgHom_eq
  条件: (f : A ->ₐ[R] B) (n : 自然数)
  证明: by
  ext f; simp
-/
lemma lcoeff_comp_mapAlgHom_eq (f : A ->ₐ[R] B) (n : Nat) :
    (lcoeff B n).restrictScalars R ∘ₗ (mapAlgHom f).toLinearMap =
      f.toLinearMap ∘ₗ (lcoeff A n).restrictScalars R := by
  ext f; simp

/--
lemma `mapAlgHom_monomial` / 引理 `mapAlgHom_monomial`

English:
lemma mapAlgHom_monomial
  given: (f : A ->ₐ[R] B) (n : Nat) (a : A)
  proof: by simp

中文:
引理 mapAlgHom_monomial
  条件: (f : A ->ₐ[R] B) (n : 自然数) (a : A)
  证明: by simp
-/
lemma mapAlgHom_monomial (f : A ->ₐ[R] B) (n : Nat) (a : A) :
    mapAlgHom f (monomial n a) = monomial n (f a) := by simp

/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (f : A ≃ₐ[R] B)
  body: AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[simp]

中文:
定义 mapAlgEquiv
  签名: (f : A ≃ₐ[R] B)
  定义体: AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, f.symm.toAlgHom, f.toAlgHom, mapAlgHom, ofAlgHom, toAlgHom
-/
def mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B :=
  AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[simp]
/--
theorem `coe_mapAlgEquiv` / 定理 `coe_mapAlgEquiv`

English:
theorem coe_mapAlgEquiv
  given: (f : A ≃ₐ[R] B)
  statement: ⇑(mapAlgEquiv f) = map f
  proof: rfl

@[simp]

中文:
定理 coe_mapAlgEquiv
  条件: (f : A ≃ₐ[R] B)
  结论: ⇑(mapAlgEquiv f) = map f
  证明: rfl

@[simp]
-/
theorem coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f :=
  rfl

@[simp]
/--
theorem `mapAlgEquiv_id` / 定理 `mapAlgEquiv_id`

English:
theorem mapAlgEquiv_id
  statement: mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl
  proof: AlgEquiv.ext fun _x => map_id

@[simp]

中文:
定理 mapAlgEquiv_id
  结论: mapAlgEquiv (@代数等价.refl R A _ _ _) = 代数等价.refl
  证明: AlgEquiv.ext fun _x => map_id

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, NoZeroDivisors, NoZeroDivisors.to_isCancelMulZero, map_id, to_isCancelMulZero
-/
theorem mapAlgEquiv_id : mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl :=
  AlgEquiv.ext fun _x => map_id

@[simp]
/--
theorem `mapAlgEquiv_coe_ringHom` / 定理 `mapAlgEquiv_coe_ringHom`

English:
theorem mapAlgEquiv_coe_ringHom
  given: (f : A ≃ₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 mapAlgEquiv_coe_ringHom
  条件: (f : A ≃ₐ[R] B)
  证明: rfl

@[simp]
-/
theorem mapAlgEquiv_coe_ringHom (f : A ≃ₐ[R] B) :
    ↑(mapAlgEquiv f : _ ≃ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A ->+* Polynomial B) :=
  rfl

@[simp]
/--
theorem `mapAlgEquiv_toAlgHom` / 定理 `mapAlgEquiv_toAlgHom`

English:
theorem mapAlgEquiv_toAlgHom
  given: (f : A ≃ₐ[R] B)
  proof: rfl

@[simp]

中文:
定理 mapAlgEquiv_toAlgHom
  条件: (f : A ≃ₐ[R] B)
  证明: rfl

@[simp]

Depends on / 依赖: IsDomain, IsDomain.to_noZeroDivisors, Semiring, to_noZeroDivisors
-/
theorem mapAlgEquiv_toAlgHom (f : A ≃ₐ[R] B) :
    (mapAlgEquiv f : Polynomial A ->ₐ[R] Polynomial B) = mapAlgHom f := rfl

@[simp]
/--
theorem `mapAlgEquiv_comp` / 定理 `mapAlgEquiv_comp`

English:
theorem mapAlgEquiv_comp
  given: (C : Type*) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C)
  proof: by
  ext
  simp

中文:
定理 mapAlgEquiv_comp
  条件: (C : 类型) [半环 C] [代数 R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C)
  证明: by
  ext
  simp
-/
theorem mapAlgEquiv_comp (C : Type*) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (mapAlgEquiv f).trans (mapAlgEquiv g) = mapAlgEquiv (f.trans g) := by
  ext
  simp

end Map

end CommSemiring

section aeval

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

variable (R A) in
/-- Given a valuation `x` of the variable in an `R`-algebra `A`, the bijection induced by the unique
`R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
@[simps! symm_apply]
/--
Definition of `aevalEquiv` / `aevalEquiv` 的定义

English:
definition aevalEquiv
  signature: : A ≃ (R[X] ->ₐ[R] A) where
  body: eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)
  invFun f := f X
  left_inv := eval₂_X _
right_inv _ := algHom_ext' (Subsingleton.elim ..) eval₂_X ..

中文:
定义 aevalEquiv
  签名: : A ≃ (R[X] ->ₐ[R] A) where
  定义体: eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)
  invFun f := f X
  left_inv := eval₂_X _
right_inv _ := algHom_ext' (Subsingleton.elim ..) eval₂_X ..

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.ofId, commutes
-/
def aevalEquiv : A ≃ (R[X] ->ₐ[R] A) where
  toFun x := eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)
  invFun f := f X
  left_inv := eval₂_X _
right_inv _ := algHom_ext' (Subsingleton.elim ..) eval₂_X ..

/--
Definition of `aeval` / `aeval` 的定义

English:
definition aeval
  signature: : R[X] ->ₐ[R] A
  body: aevalEquiv R A x

中文:
定义 aeval
  签名: : R[X] ->ₐ[R] A
  定义体: aevalEquiv R A x

Depends on / 依赖: aevalEquiv
-/
def aeval : R[X] ->ₐ[R] A :=
  aevalEquiv R A x

/--
lemma `aevalEquiv_apply` / 引理 `aevalEquiv_apply`

English:
lemma aevalEquiv_apply
  given: (x : A)
  statement: aevalEquiv R A x = aeval x
  proof: rfl

中文:
引理 aevalEquiv_apply
  条件: (x : A)
  结论: aevalEquiv R A x = aeval x
  证明: rfl
-/
lemma aevalEquiv_apply (x : A) : aevalEquiv R A x = aeval x :=
  rfl

/--
Definition of `mapAlg` / `mapAlg` 的定义

English:
definition mapAlg
  signature: (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S]
  body: @aeval _ S[X] _ _ _ (X : S[X])

@[ext 1200]

中文:
定义 mapAlg
  签名: (R : 类型u) [交换半环 R] (S : 类型v) [半环 S] [代数 R S]
  定义体: @aeval _ S[X] _ _ _ (X : S[X])

@[ext 1200]
-/
def mapAlg (R : Type u) [CommSemiring R] (S : Type v) [Semiring S] [Algebra R S] :
    R[X] ->ₐ[R] S[X] :=
  @aeval _ S[X] _ _ _ (X : S[X])

@[ext 1200]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
  proof: algHom_ext' (Subsingleton.elim ..) hX

中文:
定理 algHom_ext
  条件: {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
  证明: algHom_ext' (Subsingleton.elim ..) hX

Depends on / 依赖: Subsingleton, Subsingleton.elim, algHom_ext
-/
theorem algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X) :
    f = g :=
  algHom_ext' (Subsingleton.elim ..) hX

/--
theorem `aeval_def` / 定理 `aeval_def`

English:
theorem aeval_def
  given: (p : R[X])
  statement: aeval x p = eval₂ (algebraMap R A) x p
  proof: rfl

@[simp]

中文:
定理 aeval_def
  条件: (p : R[X])
  结论: aeval x p = eval₂ (algebraMap R A) x p
  证明: rfl

@[simp]
-/
theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  rfl

@[simp]
/--
lemma `eval_map_algebraMap` / 引理 `eval_map_algebraMap`

English:
lemma eval_map_algebraMap
  given: (P : R[X]) (b : B)
  proof: by
  rw [aeval_def]; rw [eval_map]

中文:
引理 eval_map_algebraMap
  条件: (P : R[X]) (b : B)
  证明: by
  rw [aeval_def]; rw [eval_map]

Depends on / 依赖: aeval_def, eval_map
-/
lemma eval_map_algebraMap (P : R[X]) (b : B) :
    (map (algebraMap R B) P).eval b = aeval b P := by
  rw [aeval_def]; rw [eval_map]

/--
theorem `mapAlg_eq_map` / 定理 `mapAlg_eq_map`

English:
theorem mapAlg_eq_map
  given: (S : Type v) [Semiring S] [Algebra R S] (p : R[X])
  proof: by
  rfl

中文:
定理 mapAlg_eq_map
  条件: (S : 类型v) [半环 S] [代数 R S] (p : R[X])
  证明: by
  rfl
-/
theorem mapAlg_eq_map (S : Type v) [Semiring S] [Algebra R S] (p : R[X]) :
    mapAlg R S p = map (algebraMap R S) p := by
  rfl

/--
theorem `aeval_zero` / 定理 `aeval_zero`

English:
theorem aeval_zero
  statement: aeval x (0 : R[X]) = 0
  proof: map_zero (aeval x)

@[simp]

中文:
定理 aeval_zero
  结论: aeval x (0 : R[X]) = 0
  证明: map_zero (aeval x)

@[simp]

Depends on / 依赖: map_zero
-/
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  map_zero (aeval x)

@[simp]
/--
theorem `aeval_X` / 定理 `aeval_X`

English:
theorem aeval_X
  statement: aeval x (X : R[X]) = x
  proof: eval₂_X _ x

@[simp]

中文:
定理 aeval_X
  结论: aeval x (X : R[X]) = x
  证明: eval₂_X _ x

@[simp]
-/
theorem aeval_X : aeval x (X : R[X]) = x :=
  eval₂_X _ x

@[simp]
/--
theorem `aeval_C` / 定理 `aeval_C`

English:
theorem aeval_C
  given: (r : R)
  statement: aeval x (C r) = algebraMap R A r
  proof: eval₂_C _ x

@[simp]

中文:
定理 aeval_C
  条件: (r : R)
  结论: aeval x (C r) = algebraMap R A r
  证明: eval₂_C _ x

@[simp]
-/
theorem aeval_C (r : R) : aeval x (C r) = algebraMap R A r :=
  eval₂_C _ x

@[simp]
/--
theorem `aeval_monomial` / 定理 `aeval_monomial`

English:
theorem aeval_monomial
  given: {n : Nat} {r : R}
  statement: aeval x (monomial n r) = algebraMap _ _ r * x ^ n
  proof: eval₂_monomial _ _

中文:
定理 aeval_monomial
  条件: {n : 自然数} {r : R}
  结论: aeval x (monomial n r) = algebraMap _ _ r * x ^ n
  证明: eval₂_monomial _ _
-/
theorem aeval_monomial {n : Nat} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  eval₂_monomial _ _

/--
theorem `aeval_X_pow` / 定理 `aeval_X_pow`

English:
theorem aeval_X_pow
  given: {n : Nat}
  statement: aeval x ((X : R[X]) ^ n) = x ^ n
  proof: eval₂_X_pow _ _

中文:
定理 aeval_X_pow
  条件: {n : 自然数}
  结论: aeval x ((X : R[X]) ^ n) = x ^ n
  证明: eval₂_X_pow _ _
-/
theorem aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _

/--
theorem `aeval_add` / 定理 `aeval_add`

English:
theorem aeval_add
  statement: aeval x (p + q) = aeval x p + aeval x q
  proof: map_add _ _ _

中文:
定理 aeval_add
  结论: aeval x (p + q) = aeval x p + aeval x q
  证明: map_add _ _ _

Depends on / 依赖: map_add
-/
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  map_add _ _ _

/--
theorem `aeval_one` / 定理 `aeval_one`

English:
theorem aeval_one
  statement: aeval x (1 : R[X]) = 1
  proof: map_one _

中文:
定理 aeval_one
  结论: aeval x (1 : R[X]) = 1
  证明: map_one _

Depends on / 依赖: map_one
-/
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  map_one _

/--
theorem `aeval_natCast` / 定理 `aeval_natCast`

English:
theorem aeval_natCast
  given: (n : Nat)
  statement: aeval x (n : R[X]) = n
  proof: map_natCast _ _

中文:
定理 aeval_natCast
  条件: (n : 自然数)
  结论: aeval x (n : R[X]) = n
  证明: map_natCast _ _

Depends on / 依赖: map_natCast
-/
theorem aeval_natCast (n : Nat) : aeval x (n : R[X]) = n :=
  map_natCast _ _

/--
theorem `aeval_mul` / 定理 `aeval_mul`

English:
theorem aeval_mul
  statement: aeval x (p * q) = aeval x p * aeval x q
  proof: map_mul _ _ _

中文:
定理 aeval_mul
  结论: aeval x (p * q) = aeval x p * aeval x q
  证明: map_mul _ _ _

Depends on / 依赖: map_mul
-/
theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  map_mul _ _ _

/--
theorem `comp_eq_aeval` / 定理 `comp_eq_aeval`

English:
theorem comp_eq_aeval
  statement: p.comp q = aeval q p
  proof: rfl

中文:
定理 comp_eq_aeval
  结论: p.comp q = aeval q p
  证明: rfl
-/
theorem comp_eq_aeval : p.comp q = aeval q p := rfl

/--
theorem `aeval_comp` / 定理 `aeval_comp`

English:
theorem aeval_comp
  given: {A : Type*} [Semiring A] [Algebra R A] (x : A)
  proof: eval₂_comp' x p q

@[gcongr]

中文:
定理 aeval_comp
  条件: {A : 类型} [半环 A] [代数 R A] (x : A)
  证明: eval₂_comp' x p q

@[gcongr]
-/
theorem aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) :
    aeval x (p.comp q) = aeval (aeval x q) p :=
  eval₂_comp' x p q

@[gcongr]
/--
theorem `aeval_dvd` / 定理 `aeval_dvd`

English:
theorem aeval_dvd
  given: (h : p ∣ q)
  statement: p.aeval x ∣ q.aeval x
  proof: _root_.map_dvd (aeval x) h

中文:
定理 aeval_dvd
  条件: (h : p ∣ q)
  结论: p.aeval x ∣ q.aeval x
  证明: _root_.map_dvd (aeval x) h

Depends on / 依赖: _root_, _root_.map_dvd, map_dvd
-/
theorem aeval_dvd (h : p ∣ q) : p.aeval x ∣ q.aeval x := _root_.map_dvd (aeval x) h

section IsScalarTower

variable {A : Type*} (B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/--
theorem `mapAlg_comp` / 定理 `mapAlg_comp`

English:
theorem mapAlg_comp
  given: (p : A[X])
  statement: (mapAlg A C) p = (mapAlg B C) (mapAlg A B p)
  proof: by
  simp [mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B C]

中文:
定理 mapAlg_comp
  条件: (p : A[X])
  结论: (mapAlg A C) p = (mapAlg B C) (mapAlg A B p)
  证明: by
  simp [mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B C]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, mapAlg_eq_map, map_map
-/
theorem mapAlg_comp (p : A[X]) : (mapAlg A C) p = (mapAlg B C) (mapAlg A B p) := by
  simp [mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B C]

/--
theorem `coeff_zero_of_isScalarTower` / 定理 `coeff_zero_of_isScalarTower`

English:
theorem coeff_zero_of_isScalarTower
  given: (p : A[X])
  proof: by
  rw [mapAlg_eq_map]; rw [coeff_map]; rw [IsScalarTower.algebraMap_eq A B C]; rw [RingHom.comp_apply]

中文:
定理 coeff_zero_of_isScalarTower
  条件: (p : A[X])
  证明: by
  rw [mapAlg_eq_map]; rw [coeff_map]; rw [IsScalarTower.algebraMap_eq A B C]; rw [RingHom.comp_apply]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, RingHom, RingHom.comp_apply, algebraMap_eq, coeff_map, comp_apply, mapAlg_eq_map
-/
theorem coeff_zero_of_isScalarTower (p : A[X]) :
    (algebraMap B C) ((algebraMap A B) (p.coeff 0)) = (mapAlg A C p).coeff 0 := by
  rw [mapAlg_eq_map]; rw [coeff_map]; rw [IsScalarTower.algebraMap_eq A B C]; rw [RingHom.comp_apply]

end IsScalarTower

/-- Two polynomials `p` and `q` such that `p(q(X))=X` and `q(p(X))=X`
  induces an automorphism of the polynomial algebra. -/
@[simps! apply]
/--
Definition of `algEquivOfCompEqX` / `algEquivOfCompEqX` 的定义

English:
definition algEquivOfCompEqX
  signature: (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X)
  body: by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ => by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

@[simp]

中文:
定义 algEquivOfCompEqX
  签名: (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X)
  定义体: by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ => by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.ext, comp_assoc, comp_eq_aeval, ofAlgHom
-/
def algEquivOfCompEqX (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) : R[X] ≃ₐ[R] R[X] := by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ => by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

@[simp]
/--
theorem `algEquivOfCompEqX_eq_iff` / 定理 `algEquivOfCompEqX_eq_iff`

English:
theorem algEquivOfCompEqX_eq_iff
  statement: (p q p' q' : R[X])
  proof: ⟨fun h => by simpa using congr($h X), fun h => by ext1; simp [h]⟩

@[simp]

中文:
定理 algEquivOfCompEqX_eq_iff
  结论: (p q p' q' : R[X])
  证明: ⟨fun h => by simpa using congr($h X), fun h => by ext1; simp [h]⟩

@[simp]
-/
theorem algEquivOfCompEqX_eq_iff (p q p' q' : R[X])
    (hpq : p.comp q = X) (hqp : q.comp p = X) (hpq' : p'.comp q' = X) (hqp' : q'.comp p' = X) :
    algEquivOfCompEqX p q hpq hqp = algEquivOfCompEqX p' q' hpq' hqp' ↔ p = p' :=
  ⟨fun h => by simpa using congr($h X), fun h => by ext1; simp [h]⟩

@[simp]
/--
theorem `algEquivOfCompEqX_symm` / 定理 `algEquivOfCompEqX_symm`

English:
theorem algEquivOfCompEqX_symm
  given: (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X)
  proof: rfl

中文:
定理 algEquivOfCompEqX_symm
  条件: (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X)
  证明: rfl

Depends on / 依赖: CommRing, toCommRing
-/
theorem algEquivOfCompEqX_symm (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) :
    (algEquivOfCompEqX p q hpq hqp).symm = algEquivOfCompEqX q p hqp hpq := rfl

/-- The automorphism of the polynomial algebra given by `p(X) ↦ p(a * X + b)`,
  with inverse `p(X) ↦ p(a⁻¹ * (X - b))`. -/
@[simps!]
/--
Definition of `algEquivCMulXAddC` / `algEquivCMulXAddC` 的定义

English:
definition algEquivCMulXAddC
  signature: {R : Type*} [CommRing R] (a b : R) [Invertible a]
  body: algEquivOfCompEqX (C a * X + C b) (C ⅟a * (X - C b))
    (by simp [← C_mul, ← mul_assoc]) (by simp [← C_mul, ← mul_assoc])

中文:
定义 algEquivCMulXAddC
  签名: {R : 类型} [交换环 R] (a b : R) [可逆 a]
  定义体: algEquivOfCompEqX (C a * X + C b) (C ⅟a * (X - C b))
    (by simp [← C_mul, ← mul_assoc]) (by simp [← C_mul, ← mul_assoc])

Depends on / 依赖: C_mul, algEquivOfCompEqX, mul_assoc
-/
def algEquivCMulXAddC {R : Type*} [CommRing R] (a b : R) [Invertible a] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (C a * X + C b) (C ⅟a * (X - C b))
    (by simp [← C_mul, ← mul_assoc]) (by simp [← C_mul, ← mul_assoc])

/--
theorem `algEquivCMulXAddC_symm_eq` / 定理 `algEquivCMulXAddC_symm_eq`

English:
theorem algEquivCMulXAddC_symm_eq
  given: {R : Type*} [CommRing R] (a b : R) [Invertible a]
  proof: by
  ext p : 1
  simp only [algEquivCMulXAddC_symm_apply, neg_mul, algEquivCMulXAddC_apply, map_neg, map_mul]
  congr
  simp [mul_add, sub_eq_add_neg]

中文:
定理 algEquivCMulXAddC_symm_eq
  条件: {R : 类型} [交换环 R] (a b : R) [可逆 a]
  证明: by
  ext p : 1
  simp only [algEquivCMulXAddC_symm_apply, neg_mul, algEquivCMulXAddC_apply, map_neg, map_mul]
  congr
  simp [mul_add, sub_eq_add_neg]

Depends on / 依赖: algEquivCMulXAddC_apply, algEquivCMulXAddC_symm_apply, map_mul, map_neg, mul_add, neg_mul, sub_eq_add_neg
-/
theorem algEquivCMulXAddC_symm_eq {R : Type*} [CommRing R] (a b : R) [Invertible a] :
    (algEquivCMulXAddC a b).symm = algEquivCMulXAddC (⅟a) (-⅟a * b) := by
  ext p : 1
  simp only [algEquivCMulXAddC_symm_apply, neg_mul, algEquivCMulXAddC_apply, map_neg, map_mul]
  congr
  simp [mul_add, sub_eq_add_neg]

/-- The automorphism of the polynomial algebra given by `p(X) ↦ p(X+t)`,
  with inverse `p(X) ↦ p(X-t)`. -/
@[simps! apply]
/--
Definition of `algEquivAevalXAddC` / `algEquivAevalXAddC` 的定义

English:
definition algEquivAevalXAddC
  signature: {R : Type*} [CommRing R] (t : R)
  body: algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

@[simp]

中文:
定义 algEquivAevalXAddC
  签名: {R : 类型} [交换环 R] (t : R)
  定义体: algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

@[simp]

Depends on / 依赖: algEquivOfCompEqX
-/
def algEquivAevalXAddC {R : Type*} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

@[simp]
/--
theorem `algEquivAevalXAddC_eq_iff` / 定理 `algEquivAevalXAddC_eq_iff`

English:
theorem algEquivAevalXAddC_eq_iff
  given: {R : Type*} [CommRing R] (t t' : R)
  proof: by
  simp [algEquivAevalXAddC]

@[simp]

中文:
定理 algEquivAevalXAddC_eq_iff
  条件: {R : 类型} [交换环 R] (t t' : R)
  证明: by
  simp [algEquivAevalXAddC]

@[simp]

Depends on / 依赖: algEquivAevalXAddC
-/
theorem algEquivAevalXAddC_eq_iff {R : Type*} [CommRing R] (t t' : R) :
    algEquivAevalXAddC t = algEquivAevalXAddC t' ↔ t = t' := by
  simp [algEquivAevalXAddC]

@[simp]
/--
theorem `algEquivAevalXAddC_symm` / 定理 `algEquivAevalXAddC_symm`

English:
theorem algEquivAevalXAddC_symm
  given: {R : Type*} [CommRing R] (t : R)
  proof: by
  simp [algEquivAevalXAddC, sub_eq_add_neg]

中文:
定理 algEquivAevalXAddC_symm
  条件: {R : 类型} [交换环 R] (t : R)
  证明: by
  simp [algEquivAevalXAddC, sub_eq_add_neg]

Depends on / 依赖: algEquivAevalXAddC, sub_eq_add_neg
-/
theorem algEquivAevalXAddC_symm {R : Type*} [CommRing R] (t : R) :
    (algEquivAevalXAddC t).symm = algEquivAevalXAddC (-t) := by
  simp [algEquivAevalXAddC, sub_eq_add_neg]

/-- The involutive automorphism of the polynomial algebra given by `p(X) ↦ p(-X)`. -/
@[simps!]
/--
Definition of `algEquivAevalNegX` / `algEquivAevalNegX` 的定义

English:
definition algEquivAevalNegX
  signature: {R : Type*} [CommRing R]
  body: algEquivOfCompEqX (-X) (-X) (by simp) (by simp)

中文:
定义 algEquivAevalNegX
  签名: {R : 类型} [交换环 R]
  定义体: algEquivOfCompEqX (-X) (-X) (by simp) (by simp)

Depends on / 依赖: algEquivOfCompEqX
-/
def algEquivAevalNegX {R : Type*} [CommRing R] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (-X) (-X) (by simp) (by simp)

/--
theorem `comp_neg_X_comp_neg_X` / 定理 `comp_neg_X_comp_neg_X`

English:
theorem comp_neg_X_comp_neg_X
  given: {R : Type*} [CommRing R] (p : R[X])
  proof: by
  rw [comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]

中文:
定理 comp_neg_X_comp_neg_X
  条件: {R : 类型} [交换环 R] (p : R[X])
  证明: by
  rw [comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]

Depends on / 依赖: X_comp, comp_X, comp_assoc, neg_comp, neg_neg
-/
theorem comp_neg_X_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) :
    (p.comp (-X)).comp (-X) = p := by
  rw [comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]

/--
theorem `aeval_algHom` / 定理 `aeval_algHom`

English:
theorem aeval_algHom
  given: (f : A ->ₐ[R] B) (x : A)
  statement: aeval (f x) = f.comp (aeval x)
  proof: algHom_ext by simp only [aeval_X, AlgHom.comp_apply]

@[simp]

中文:
定理 aeval_algHom
  条件: (f : A ->ₐ[R] B) (x : A)
  结论: aeval (f x) = f.comp (aeval x)
  证明: algHom_ext by simp only [aeval_X, AlgHom.comp_apply]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, aeval_X, algHom_ext, comp_apply
-/
theorem aeval_algHom (f : A ->ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
algHom_ext by simp only [aeval_X, AlgHom.comp_apply]

@[simp]
/--
theorem `aeval_X_left` / 定理 `aeval_X_left`

English:
theorem aeval_X_left
  statement: aeval (X : R[X]) = AlgHom.id R R[X]
  proof: algHom_ext aeval_X X

中文:
定理 aeval_X_left
  结论: aeval (X : R[X]) = 代数态射.id R R[X]
  证明: algHom_ext aeval_X X

Depends on / 依赖: aeval_X, algHom_ext
-/
theorem aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X] :=
algHom_ext aeval_X X

/--
theorem `aeval_X_left_apply` / 定理 `aeval_X_left_apply`

English:
theorem aeval_X_left_apply
  given: (p : R[X])
  statement: aeval X p = p
  proof: AlgHom.congr_fun (@aeval_X_left R _) p

中文:
定理 aeval_X_left_apply
  条件: (p : R[X])
  结论: aeval X p = p
  证明: AlgHom.congr_fun (@aeval_X_left R _) p

Depends on / 依赖: AlgHom, AlgHom.congr_fun, aeval_X_left, congr_fun
-/
theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
  AlgHom.congr_fun (@aeval_X_left R _) p

/--
lemma `aeval_X_left_eq_map` / 引理 `aeval_X_left_eq_map`

English:
lemma aeval_X_left_eq_map
  given: [CommSemiring S] [Algebra R S] (p : R[X])
  proof: rfl

中文:
引理 aeval_X_left_eq_map
  条件: [交换半环 S] [代数 R S] (p : R[X])
  证明: rfl
-/
lemma aeval_X_left_eq_map [CommSemiring S] [Algebra R S] (p : R[X]) :
    aeval X p = map (algebraMap R S) p :=
  rfl

/--
theorem `eval_unique` / 定理 `eval_unique`

English:
theorem eval_unique
  given: (φ : R[X] ->ₐ[R] A) (p)
  statement: φ p = eval₂ (algebraMap R A) (φ X) p
  proof: by
  rw [← aeval_def]; rw [aeval_algHom]; rw [aeval_X_left]; rw [AlgHom.comp_id]

中文:
定理 eval_unique
  条件: (φ : R[X] ->ₐ[R] A) (p)
  结论: φ p = eval₂ (algebraMap R A) (φ X) p
  证明: by
  rw [← aeval_def]; rw [aeval_algHom]; rw [aeval_X_left]; rw [AlgHom.comp_id]

Depends on / 依赖: AlgHom, AlgHom.comp_id, aeval_X_left, aeval_algHom, aeval_def, comp_id
-/
theorem eval_unique (φ : R[X] ->ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p := by
  rw [← aeval_def]; rw [aeval_algHom]; rw [aeval_X_left]; rw [AlgHom.comp_id]

/--
theorem `aeval_algHom_apply` / 定理 `aeval_algHom_apply`

English:
theorem aeval_algHom_apply
  statement: {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
  proof: by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add]; rw [hp]; rw [hq]; rw [← map_add]; rw [← map_add]

中文:
定理 aeval_algHom_apply
  结论: {F : 类型} [函数状 F A B] [代数态射类 F R A B]
  证明: by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add]; rw [hp]; rw [hq]; rw [← map_add]; rw [← map_add]

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, Polynomial, Polynomial.induction_on, commutes, induction_on, map_add
-/
theorem aeval_algHom_apply {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (x : A) (p : R[X]) :
    aeval (f x) p = f (aeval x p) := by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add]; rw [hp]; rw [hq]; rw [← map_add]; rw [← map_add]

/--
theorem `aeval_op_apply` / 定理 `aeval_op_apply`

English:
theorem aeval_op_apply
  given: (x : A) (p : R[X])
  proof: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c => simp [aeval_monomial, MulOpposite.op_pow, Algebra.commutes]

中文:
定理 aeval_op_apply
  条件: (x : A) (p : R[X])
  证明: by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c => simp [aeval_monomial, MulOpposite.op_pow, Algebra.commutes]

Depends on / 依赖: Algebra, Algebra.commutes, MulOpposite, MulOpposite.op_pow, Polynomial, Polynomial.induction_on, aeval_monomial, commutes, induction_on, map_add, monomial, op_pow
-/
theorem aeval_op_apply (x : A) (p : R[X]) :
    aeval (MulOpposite.op x) p = MulOpposite.op (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c => simp [aeval_monomial, MulOpposite.op_pow, Algebra.commutes]

/--
theorem `aeval_smul` / 定理 `aeval_smul`

English:
theorem aeval_smul
  statement: (f : R[X]) {G : Type*} [Monoid G] [MulSemiringAction G A] [SMulCommClass G R A]
  proof: by
  rw [← MulSemiringAction.toAlgHom_apply R]; rw [aeval_algHom_apply]; rw [MulSemiringAction.toAlgHom_apply]

@[simp]

中文:
定理 aeval_smul
  结论: (f : R[X]) {G : 类型} [幺半群 G] [MulSemiring作用 G A] [标量交换类 G R A]
  证明: by
  rw [← MulSemiringAction.toAlgHom_apply R]; rw [aeval_algHom_apply]; rw [MulSemiringAction.toAlgHom_apply]

@[simp]

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toAlgHom_apply, aeval_algHom_apply, toAlgHom_apply
-/
theorem aeval_smul (f : R[X]) {G : Type*} [Monoid G] [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) (x : A) : f.aeval (g • x) = g • (f.aeval x) := by
  rw [← MulSemiringAction.toAlgHom_apply R]; rw [aeval_algHom_apply]; rw [MulSemiringAction.toAlgHom_apply]

@[simp]
/--
lemma `coe_aeval_mk_apply` / 引理 `coe_aeval_mk_apply`

English:
lemma coe_aeval_mk_apply
  given: {S : Subalgebra R A} (h : x in S)
  proof: (aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm

中文:
引理 coe_aeval_mk_apply
  条件: {S : 子代数 R A} (h : x in S)
  证明: (aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm

Depends on / 依赖: S.val, aeval_algHom_apply
-/
lemma coe_aeval_mk_apply {S : Subalgebra R A} (h : x in S) :
    (aeval (⟨x, h⟩ : S) p : A) = aeval x p :=
  (aeval_algHom_apply S.val (⟨x, h⟩ : S) p).symm

/--
theorem `aeval_algEquiv` / 定理 `aeval_algEquiv`

English:
theorem aeval_algEquiv
  given: (f : A ≃ₐ[R] B) (x : A)
  statement: aeval (f x) = (f : A ->ₐ[R] B).comp (aeval x)
  proof: aeval_algHom (f : A ->ₐ[R] B) x

中文:
定理 aeval_algEquiv
  条件: (f : A ≃ₐ[R] B) (x : A)
  结论: aeval (f x) = (f : A ->ₐ[R] B).comp (aeval x)
  证明: aeval_algHom (f : A ->ₐ[R] B) x

Depends on / 依赖: aeval_algHom
-/
theorem aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A ->ₐ[R] B).comp (aeval x) :=
  aeval_algHom (f : A ->ₐ[R] B) x

/--
theorem `aeval_algebraMap_apply_eq_algebraMap_eval` / 定理 `aeval_algebraMap_apply_eq_algebraMap_eval`

English:
theorem aeval_algebraMap_apply_eq_algebraMap_eval
  given: (x : R) (p : R[X])
  proof: aeval_algHom_apply (Algebra.ofId R A) x p

中文:
定理 aeval_algebraMap_apply_eq_algebraMap_eval
  条件: (x : R) (p : R[X])
  证明: aeval_algHom_apply (Algebra.ofId R A) x p

Depends on / 依赖: Algebra, Algebra.ofId, aeval_algHom_apply
-/
theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_algHom_apply (Algebra.ofId R A) x p

/--
theorem `aeval_prod` / 定理 `aeval_prod`

English:
theorem aeval_prod
  given: (x : A × B)
  statement: aeval (R := R) x = (aeval x.1).prod (aeval x.2)
  proof: aeval_algHom (.fst R A B) x ▸ aeval_algHom (.snd R A B) x ▸
    (aeval x).prod_comp (.fst R A B) (.snd R A B)

中文:
定理 aeval_prod
  条件: (x : A × B)
  结论: aeval (R := R) x = (aeval x.1).乘积 (aeval x.2)
  证明: aeval_algHom (.fst R A B) x ▸ aeval_algHom (.snd R A B) x ▸
    (aeval x).prod_comp (.fst R A B) (.snd R A B)
-/
theorem aeval_prod (x : A × B) : aeval (R := R) x = (aeval x.1).prod (aeval x.2) :=
  aeval_algHom (.fst R A B) x ▸ aeval_algHom (.snd R A B) x ▸
    (aeval x).prod_comp (.fst R A B) (.snd R A B)

/--
theorem `aeval_prod_apply` / 定理 `aeval_prod_apply`

English:
theorem aeval_prod_apply
  given: (x : A × B) (p : Polynomial R)
  proof: by simp [aeval_prod]

中文:
定理 aeval_prod_apply
  条件: (x : A × B) (p : 多项式 R)
  证明: by simp [aeval_prod]

Depends on / 依赖: aeval_prod
-/
theorem aeval_prod_apply (x : A × B) (p : Polynomial R) :
    p.aeval x = (p.aeval x.1, p.aeval x.2) := by simp [aeval_prod]

section Pi

variable {I : Type*} {A : I -> Type*} [forall i, Semiring (A i)] [forall i, Algebra R (A i)]
variable (x : Π i, A i) (p : R[X])

/--
theorem `aeval_pi` / 定理 `aeval_pi`

English:
theorem aeval_pi
  given: (x : Π i, A i)
  statement: aeval (R := R) x = AlgHom.pi (fun i => aeval (x i))
  proof: (funext fun i => aeval_algHom (Pi.evalAlgHom R A i) x) ▸
    (AlgHom.pi_comp (Pi.evalAlgHom R A) (aeval x))

中文:
定理 aeval_pi
  条件: (x : Π i, A i)
  结论: aeval (R := R) x = 代数态射.pi (fun i => aeval (x i))
  证明: (funext fun i => aeval_algHom (Pi.evalAlgHom R A i) x) ▸
    (AlgHom.pi_comp (Pi.evalAlgHom R A) (aeval x))

Depends on / 依赖: AlgHom, AlgHom.pi
-/
theorem aeval_pi (x : Π i, A i) : aeval (R := R) x = AlgHom.pi (fun i => aeval (x i)) :=
  (funext fun i => aeval_algHom (Pi.evalAlgHom R A i) x) ▸
    (AlgHom.pi_comp (Pi.evalAlgHom R A) (aeval x))

/--
theorem `aeval_pi_apply₂` / 定理 `aeval_pi_apply₂`

English:
theorem aeval_pi_apply₂
  given: (j : I)
  statement: p.aeval x j = p.aeval (x j)
  proof: aeval_pi (R := R) x ▸ AlgHom.pi_apply (fun i => aeval (x i)) p j

中文:
定理 aeval_pi_apply₂
  条件: (j : I)
  结论: p.aeval x j = p.aeval (x j)
  证明: aeval_pi (R := R) x ▸ AlgHom.pi_apply (fun i => aeval (x i)) p j

Depends on / 依赖: AlgHom, AlgHom.pi_apply, aeval_pi, pi_apply
-/
theorem aeval_pi_apply₂ (j : I) : p.aeval x j = p.aeval (x j) :=
  aeval_pi (R := R) x ▸ AlgHom.pi_apply (fun i => aeval (x i)) p j

/--
theorem `aeval_pi_apply` / 定理 `aeval_pi_apply`

English:
theorem aeval_pi_apply
  statement: p.aeval x = fun j => p.aeval (x j)
  proof: funext fun j => aeval_pi_apply₂ x p j

中文:
定理 aeval_pi_apply
  结论: p.aeval x = fun j => p.aeval (x j)
  证明: funext fun j => aeval_pi_apply₂ x p j
-/
theorem aeval_pi_apply : p.aeval x = fun j => p.aeval (x j) :=
  funext fun j => aeval_pi_apply₂ x p j

end Pi

@[simp]
/--
theorem `coe_aeval_eq_eval` / 定理 `coe_aeval_eq_eval`

English:
theorem coe_aeval_eq_eval
  given: (r : R)
  statement: (aeval r : R[X] -> R) = eval r
  proof: rfl

@[simp]

中文:
定理 coe_aeval_eq_eval
  条件: (r : R)
  结论: (aeval r : R[X] -> R) = eval r
  证明: rfl

@[simp]
-/
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] -> R) = eval r :=
  rfl

@[simp]
/--
theorem `coe_aeval_eq_evalRingHom` / 定理 `coe_aeval_eq_evalRingHom`

English:
theorem coe_aeval_eq_evalRingHom
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 coe_aeval_eq_evalRingHom
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem coe_aeval_eq_evalRingHom (x : R) :
    ((aeval x : R[X] ->ₐ[R] R) : R[X] ->+* R) = evalRingHom x :=
  rfl

@[simp]
/--
theorem `aeval_fn_apply` / 定理 `aeval_fn_apply`

English:
theorem aeval_fn_apply
  given: {X : Type*} (g : R[X]) (f : X -> R) (x : X)
  proof: (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

@[norm_cast]

中文:
定理 aeval_fn_apply
  条件: {X : 类型} (g : R[X]) (f : X -> R) (x : X)
  证明: (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

@[norm_cast]

Depends on / 依赖: Pi.evalAlgHom, aeval_algHom_apply, evalAlgHom
-/
theorem aeval_fn_apply {X : Type*} (g : R[X]) (f : X -> R) (x : X) :
    ((aeval f) g) x = aeval (f x) g :=
  (aeval_algHom_apply (Pi.evalAlgHom R (fun _ => R) x) f g).symm

@[norm_cast]
/--
theorem `aeval_subalgebra_coe` / 定理 `aeval_subalgebra_coe`

English:
theorem aeval_subalgebra_coe
  statement: (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
  proof: (aeval_algHom_apply s.val f g).symm

中文:
定理 aeval_subalgebra_coe
  结论: (g : R[X]) {A : 类型} [半环 A] [代数 R A] (s : 子代数 R A)
  证明: (aeval_algHom_apply s.val f g).symm

Depends on / 依赖: aeval_algHom_apply, s.val
-/
theorem aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
    (f : s) : (aeval f g : A) = aeval (f : A) g :=
  (aeval_algHom_apply s.val f g).symm

/--
theorem `coeff_zero_eq_aeval_zero` / 定理 `coeff_zero_eq_aeval_zero`

English:
theorem coeff_zero_eq_aeval_zero
  given: (p : R[X])
  statement: p.coeff 0 = aeval 0 p
  proof: by
  simp [coeff_zero_eq_eval_zero]

中文:
定理 coeff_zero_eq_aeval_zero
  条件: (p : R[X])
  结论: p.coeff 0 = aeval 0 p
  证明: by
  simp [coeff_zero_eq_eval_zero]

Depends on / 依赖: coeff_zero_eq_eval_zero
-/
theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]

/--
theorem `coeff_zero_eq_aeval_zero'` / 定理 `coeff_zero_eq_aeval_zero'`

English:
theorem coeff_zero_eq_aeval_zero'
  given: (p : R[X])
  statement: algebraMap R A (p.coeff 0) = aeval (0 : A) p
  proof: by
  simp [aeval_def]

中文:
定理 coeff_zero_eq_aeval_zero'
  条件: (p : R[X])
  结论: algebraMap R A (p.coeff 0) = aeval (0 : A) p
  证明: by
  simp [aeval_def]

Depends on / 依赖: aeval_def
-/
theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by
  simp [aeval_def]

/--
theorem `map_aeval_eq_aeval_map` / 定理 `map_aeval_eq_aeval_map`

English:
theorem map_aeval_eq_aeval_map
  statement: {S T U : Type*} [Semiring S] [CommSemiring T] [Semiring U]
  proof: by
  conv_rhs => rw [← eval_map_algebraMap]
  rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [aeval_def]; rw [eval_map]

中文:
定理 map_aeval_eq_aeval_map
  结论: {S T U : 类型} [半环 S] [交换半环 T] [半环 U]
  证明: by
  conv_rhs => rw [← eval_map_algebraMap]
  rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [aeval_def]; rw [eval_map]

Depends on / 依赖: aeval_def, conv_rhs, eval_map, eval_map_algebraMap, map_map
-/
theorem map_aeval_eq_aeval_map {S T U : Type*} [Semiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra T U] {φ : R ->+* T} {ψ : S ->+* U}
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) :
    ψ (aeval a p) = aeval (ψ a) (p.map φ) := by
  conv_rhs => rw [← eval_map_algebraMap]
  rw [map_map]; rw [h]; rw [← map_map]; rw [eval_map]; rw [eval₂_at_apply]; rw [aeval_def]; rw [eval_map]

/--
theorem `aeval_eq_aeval_map` / 定理 `aeval_eq_aeval_map`

English:
theorem aeval_eq_aeval_map
  statement: [Semiring S] [CommSemiring T] [Algebra R S]
  proof: map_aeval_eq_aeval_map (by rwa [RingHom.id_comp]) p a

中文:
定理 aeval_eq_aeval_map
  结论: [半环 S] [交换半环 T] [代数 R S]
  证明: map_aeval_eq_aeval_map (by rwa [RingHom.id_comp]) p a

Depends on / 依赖: RingHom, RingHom.id_comp, id_comp, map_aeval_eq_aeval_map
-/
theorem aeval_eq_aeval_map [Semiring S] [CommSemiring T] [Algebra R S]
    [Algebra T S] {φ : R ->+* T} (h : (algebraMap T S).comp φ = (algebraMap R S))
    (p : R[X]) (a : S) : aeval a p = aeval a (p.map φ) :=
  map_aeval_eq_aeval_map (by rwa [RingHom.id_comp]) p a

/--
theorem `aeval_eq_zero_of_dvd_aeval_eq_zero` / 定理 `aeval_eq_zero_of_dvd_aeval_eq_zero`

English:
theorem aeval_eq_zero_of_dvd_aeval_eq_zero
  given: {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0)
  proof: zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

中文:
定理 aeval_eq_zero_of_dvd_aeval_eq_zero
  条件: {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0)
  证明: zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

Depends on / 依赖: aeval_dvd, zero_dvd_iff, zero_dvd_iff.mp
-/
theorem aeval_eq_zero_of_dvd_aeval_eq_zero {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0) :
    aeval x q = 0 := zero_dvd_iff.mp (h₂ ▸ aeval_dvd _ h₁)

section Semiring

variable [Semiring S] {f : R ->+* S}

/--
theorem `aeval_eq_sum_range` / 定理 `aeval_eq_sum_range`

English:
theorem aeval_eq_sum_range
  given: [Algebra R S] {p : R[X]} (x : S)
  proof: by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

中文:
定理 aeval_eq_sum_range
  条件: [代数 R S] {p : R[X]} (x : S)
  证明: by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, simp_rw, smul_def
-/
theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

/--
theorem `aeval_eq_sum_range'` / 定理 `aeval_eq_sum_range'`

English:
theorem aeval_eq_sum_range'
  given: [Algebra R S] {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : S)
  proof: by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

中文:
定理 aeval_eq_sum_range'
  条件: [代数 R S] {p : R[X]} {n : 自然数} (hn : p.natDegree < n) (x : S)
  证明: by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

Depends on / 依赖: Algebra, Algebra.smul_def, algebraMap, simp_rw, smul_def
-/
theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : Nat} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i in Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

/--
theorem `isRoot_of_eval₂_map_eq_zero` / 定理 `isRoot_of_eval₂_map_eq_zero`

English:
theorem isRoot_of_eval₂_map_eq_zero
  given: (hf : Function.Injective f) {r : R}
  proof: by
  intro h
  apply hf
  rw [← eval₂_hom]; rw [h]; rw [f.map_zero]

中文:
定理 isRoot_of_eval₂_map_eq_zero
  条件: (hf : 函数.单射 f) {r : R}
  证明: by
  intro h
  apply hf
  rw [← eval₂_hom]; rw [h]; rw [f.map_zero]

Depends on / 依赖: f.map_zero, map_zero
-/
theorem isRoot_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} :
    eval₂ f (f r) p = 0 -> p.IsRoot r := by
  intro h
  apply hf
  rw [← eval₂_hom]; rw [h]; rw [f.map_zero]

/--
theorem `isRoot_of_aeval_algebraMap_eq_zero` / 定理 `isRoot_of_aeval_algebraMap_eq_zero`

English:
theorem isRoot_of_aeval_algebraMap_eq_zero
  statement: [Algebra R S] [FaithfulSMul R S] {p : R[X]} {r : R}
  proof: isRoot_of_eval₂_map_eq_zero (FaithfulSMul.algebraMap_injective _ _) hr

中文:
定理 isRoot_of_aeval_algebraMap_eq_zero
  结论: [代数 R S] [忠实标量乘法 R S] {p : R[X]} {r : R}
  证明: isRoot_of_eval₂_map_eq_zero (FaithfulSMul.algebraMap_injective _ _) hr

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] [FaithfulSMul R S] {p : R[X]} {r : R}
    (hr : p.aeval (algebraMap R S r) = 0) : p.IsRoot r :=
  isRoot_of_eval₂_map_eq_zero (FaithfulSMul.algebraMap_injective _ _) hr

end Semiring

section CommSemiring

section aevalTower

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

/--
Definition of `aevalTower` / `aevalTower` 的定义

English:
definition aevalTower
  signature: (f : R ->ₐ[S] A') (x : A')
  body: eval₂AlgHom f x fun _ => Commute.all _ _

中文:
定义 aevalTower
  签名: (f : R ->ₐ[S] A') (x : A')
  定义体: eval₂AlgHom f x fun _ => Commute.all _ _

Depends on / 依赖: Commute, Commute.all
-/
def aevalTower (f : R ->ₐ[S] A') (x : A') : R[X] ->ₐ[S] A' :=
  eval₂AlgHom f x fun _ => Commute.all _ _

variable (g : R ->ₐ[S] A') (y : A')

@[simp]
/--
theorem `aevalTower_X` / 定理 `aevalTower_X`

English:
theorem aevalTower_X
  statement: aevalTower g y X = y
  proof: eval₂_X _ _

@[simp]

中文:
定理 aevalTower_X
  结论: aevalTower g y X = y
  证明: eval₂_X _ _

@[simp]
-/
theorem aevalTower_X : aevalTower g y X = y :=
  eval₂_X _ _

@[simp]
/--
theorem `aevalTower_C` / 定理 `aevalTower_C`

English:
theorem aevalTower_C
  given: (x : R)
  statement: aevalTower g y (C x) = g x
  proof: eval₂_C _ _

@[simp]

中文:
定理 aevalTower_C
  条件: (x : R)
  结论: aevalTower g y (C x) = g x
  证明: eval₂_C _ _

@[simp]
-/
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _

@[simp]
/--
theorem `aevalTower_comp_C` / 定理 `aevalTower_comp_C`

English:
theorem aevalTower_comp_C
  statement: (aevalTower g y : R[X] ->+* A').comp C = g
  proof: RingHom.ext aevalTower_C _ _

中文:
定理 aevalTower_comp_C
  结论: (aevalTower g y : R[X] ->+* A').comp C = g
  证明: RingHom.ext aevalTower_C _ _

Depends on / 依赖: RingHom, RingHom.ext, aevalTower_C
-/
theorem aevalTower_comp_C : (aevalTower g y : R[X] ->+* A').comp C = g :=
RingHom.ext aevalTower_C _ _

/--
theorem `aevalTower_algebraMap` / 定理 `aevalTower_algebraMap`

English:
theorem aevalTower_algebraMap
  given: (x : R)
  statement: aevalTower g y (algebraMap R R[X] x) = g x
  proof: eval₂_C _ _

中文:
定理 aevalTower_algebraMap
  条件: (x : R)
  结论: aevalTower g y (algebraMap R R[X] x) = g x
  证明: eval₂_C _ _
-/
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _

/--
theorem `aevalTower_comp_algebraMap` / 定理 `aevalTower_comp_algebraMap`

English:
theorem aevalTower_comp_algebraMap
  statement: (aevalTower g y : R[X] ->+* A').comp (algebraMap R R[X]) = g
  proof: aevalTower_comp_C _ _

中文:
定理 aevalTower_comp_algebraMap
  结论: (aevalTower g y : R[X] ->+* A').comp (algebraMap R R[X]) = g
  证明: aevalTower_comp_C _ _

Depends on / 依赖: aevalTower_comp_C
-/
theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] ->+* A').comp (algebraMap R R[X]) = g :=
  aevalTower_comp_C _ _

/--
theorem `aevalTower_toAlgHom` / 定理 `aevalTower_toAlgHom`

English:
theorem aevalTower_toAlgHom
  given: (x : R)
  statement: aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x
  proof: aevalTower_algebraMap _ _ _

@[simp]

中文:
定理 aevalTower_toAlgHom
  条件: (x : R)
  结论: aevalTower g y (标量塔.toAlgHom S R R[X] x) = g x
  证明: aevalTower_algebraMap _ _ _

@[simp]

Depends on / 依赖: aevalTower_algebraMap
-/
theorem aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
/--
theorem `aevalTower_comp_toAlgHom` / 定理 `aevalTower_comp_toAlgHom`

English:
theorem aevalTower_comp_toAlgHom
  statement: (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g
  proof: AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]

中文:
定理 aevalTower_comp_toAlgHom
  结论: (aevalTower g y).comp (标量塔.toAlgHom S R R[X]) = g
  证明: AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, aevalTower_comp_algebraMap, coe_ringHom_injective
-/
theorem aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
AlgHom.coe_ringHom_injective aevalTower_comp_algebraMap _ _

@[simp]
/--
theorem `aevalTower_id` / 定理 `aevalTower_id`

English:
theorem aevalTower_id
  statement: aevalTower (AlgHom.id S S) = aeval
  proof: by
  ext s
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]

@[simp]

中文:
定理 aevalTower_id
  结论: aevalTower (代数态射.id S S) = aeval
  证明: by
  ext s
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]

@[simp]

Depends on / 依赖: aevalTower_X, coe_aeval_eq_eval, eval_X
-/
theorem aevalTower_id : aevalTower (AlgHom.id S S) = aeval := by
  ext s
  simp only [eval_X, aevalTower_X, coe_aeval_eq_eval]

@[simp]
/--
theorem `aevalTower_ofId` / 定理 `aevalTower_ofId`

English:
theorem aevalTower_ofId
  statement: aevalTower (Algebra.ofId S A') = aeval
  proof: by
  ext
  simp only [aeval_X, aevalTower_X]

中文:
定理 aevalTower_ofId
  结论: aevalTower (代数.ofId S A') = aeval
  证明: by
  ext
  simp only [aeval_X, aevalTower_X]

Depends on / 依赖: aevalTower_X, aeval_X
-/
theorem aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval := by
  ext
  simp only [aeval_X, aevalTower_X]

end aevalTower

open LinearMap TensorProduct in
/--
lemma `X_pow_smul_rTensor_monomial` / 引理 `X_pow_smul_rTensor_monomial`

English:
lemma X_pow_smul_rTensor_monomial
  statement: [CommSemiring S] [Algebra R S] {N : Type*}
  proof: by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s n =>
    simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
    rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_comm]; rw [C_mul_X_pow_eq_monomial]

中文:
引理 X_pow_smul_rTensor_monomial
  结论: [交换半环 S] [代数 R S] {N : 类型}
  证明: by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s n =>
    simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
    rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_comm]; rw [C_mul_X_pow_eq_monomial]

Depends on / 依赖: LinearMap, LinearMap.rTensor, monomial, rTensor, restrictScalars
-/
lemma X_pow_smul_rTensor_monomial [CommSemiring S] [Algebra R S] {N : Type*}
    [AddCommMonoid N] [Module R N] (k : Nat) (sn : S otimes[R] N) :
    X (R := S) ^ k • (LinearMap.rTensor N ((monomial 0).restrictScalars R)) sn =
      (LinearMap.rTensor N ((monomial k).restrictScalars R)) sn := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s n =>
    simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
    rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_comm]; rw [C_mul_X_pow_eq_monomial]


end CommSemiring

section CommRing

variable [CommRing S] {f : R ->+* S}

/--
theorem `dvd_term_of_dvd_eval_of_dvd_terms` / 定理 `dvd_term_of_dvd_eval_of_dvd_terms`

English:
theorem dvd_term_of_dvd_eval_of_dvd_terms
  statement: {z p : S} {f : S[X]} (i : Nat) (dvd_eval : p ∣ f.eval z)
  proof: by
  by_cases hi : i in f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi]; rw [Finset.sum_insert (Finset.notMem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert! dvd_zero p
    rw [notMem_support_iff] at hi
    simp [hi]

中文:
定理 dvd_term_of_dvd_eval_of_dvd_terms
  结论: {z p : S} {f : S[X]} (i : 自然数) (dvd_eval : p ∣ f.eval z)
  证明: by
  by_cases hi : i in f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi]; rw [Finset.sum_insert (Finset.notMem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert! dvd_zero p
    rw [notMem_support_iff] at hi
    simp [hi]

Depends on / 依赖: Finset, Finset.dvd_sum, Finset.insert_erase, Finset.ne_of_mem_erase, Finset.notMem_erase, Finset.sum_insert, convert, dvd_add_left, dvd_eval, dvd_sum, dvd_terms, dvd_zero, f.support, insert_erase, ne_of_mem_erase, notMem_erase, notMem_support_iff, sum_def, sum_insert, support
-/
theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : Nat) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : forall j != i, p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases hi : i in f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi]; rw [Finset.sum_insert (Finset.notMem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert! dvd_zero p
    rw [notMem_support_iff] at hi
    simp [hi]

/--
theorem `dvd_term_of_isRoot_of_dvd_terms` / 定理 `dvd_term_of_isRoot_of_dvd_terms`

English:
theorem dvd_term_of_isRoot_of_dvd_terms
  statement: {r p : S} {f : S[X]} (i : Nat) (hr : f.IsRoot r)
  proof: dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

中文:
定理 dvd_term_of_isRoot_of_dvd_terms
  结论: {r p : S} {f : S[X]} (i : 自然数) (hr : f.IsRoot r)
  证明: dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

Depends on / 依赖: Eq.symm, dvd_term_of_dvd_eval_of_dvd_terms, dvd_zero
-/
theorem dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : Nat) (hr : f.IsRoot r)
    (h : forall j != i, p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  dvd_term_of_dvd_eval_of_dvd_terms i (Eq.symm hr ▸ dvd_zero p) h

end CommRing

end aeval

section Ring

variable [Ring R]

/--
theorem `eval_mul_X_sub_C` / 定理 `eval_mul_X_sub_C`

English:
theorem eval_mul_X_sub_C
  given: {p : R[X]} (r : R)
  statement: (p * (X - C r)).eval r = 0
  proof: by
  rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [eval_mul_C_of_commute] <;> simp

中文:
定理 eval_mul_X_sub_C
  条件: {p : R[X]} (r : R)
  结论: (p * (X - C r)).eval r = 0
  证明: by
  rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [eval_mul_C_of_commute] <;> simp

Depends on / 依赖: eval_mul_C_of_commute, eval_mul_X, eval_sub, mul_sub
-/
theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - C r)).eval r = 0 := by
  rw [mul_sub]; rw [eval_sub]; rw [eval_mul_X]; rw [eval_mul_C_of_commute] <;> simp

/--
theorem `not_isUnit_X_sub_C` / 定理 `not_isUnit_X_sub_C`

English:
theorem not_isUnit_X_sub_C
  given: [Nontrivial R] (r : R)
  statement: ¬IsUnit (X - C r)
  proof: fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R by rw [← eval_mul_X_sub_C, hgf, eval_one]

中文:
定理 not_isUnit_X_sub_C
  条件: [非平凡 R] (r : R)
  结论: ¬是单位 (X - C r)
  证明: fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R by rw [← eval_mul_X_sub_C, hgf, eval_one]

Depends on / 依赖: _hfg, eval_mul_X_sub_C, eval_one, zero_ne_one
-/
theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r) :=
fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ => zero_ne_one' R by rw [← eval_mul_X_sub_C, hgf, eval_one]

end Ring

section CommRing
variable [CommRing R] {p : R[X]} {t : R}

@[simp]
/--
theorem `aeval_neg` / 定理 `aeval_neg`

English:
theorem aeval_neg
  given: {p : R[X]} [Ring A] [Algebra R A] (x : A)
  proof: map_neg ..

@[simp]

中文:
定理 aeval_neg
  条件: {p : R[X]} [环 A] [代数 R A] (x : A)
  证明: map_neg ..

@[simp]

Depends on / 依赖: map_neg
-/
theorem aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A) :
    aeval x (-p) = -aeval x p := map_neg ..

@[simp]
/--
theorem `aeval_sub` / 定理 `aeval_sub`

English:
theorem aeval_sub
  given: {p q : R[X]} [Ring A] [Algebra R A] (x : A)
  proof: map_sub ..

中文:
定理 aeval_sub
  条件: {p q : R[X]} [环 A] [代数 R A] (x : A)
  证明: map_sub ..

Depends on / 依赖: map_sub
-/
theorem aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x : A) :
    aeval x (p - q) = aeval x p - aeval x q := map_sub ..

/--
theorem `aeval_endomorphism` / 定理 `aeval_endomorphism`

English:
theorem aeval_endomorphism
  statement: {M : Type*} [AddCommGroup M] [Module R M] (f : M ->ₗ[R] M)
  proof: by
  rw [aeval_def]; rw [eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

中文:
定理 aeval_endomorphism
  结论: {M : 类型} [加法交换群 M] [模 R M] (f : M ->ₗ[R] M)
  证明: by
  rw [aeval_def]; rw [eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

Depends on / 依赖: LinearMap, LinearMap.apply, aeval_def, map_sum
-/
theorem aeval_endomorphism {M : Type*} [AddCommGroup M] [Module R M] (f : M ->ₗ[R] M)
    (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [aeval_def]; rw [eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

/--
lemma `X_sub_C_pow_dvd_iff` / 引理 `X_sub_C_pow_dvd_iff`

English:
lemma X_sub_C_pow_dvd_iff
  given: {n : Nat}
  statement: (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t)
  proof: by
  convert! (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

中文:
引理 X_sub_C_pow_dvd_iff
  条件: {n : 自然数}
  结论: (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t)
  证明: by
  convert! (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

Depends on / 依赖: C_eq_algebraMap, algEquivAevalXAddC, convert, map_dvd_iff
-/
lemma X_sub_C_pow_dvd_iff {n : Nat} : (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t) := by
  convert! (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

/--
lemma `comp_X_add_C_eq_zero_iff` / 引理 `comp_X_add_C_eq_zero_iff`

English:
lemma comp_X_add_C_eq_zero_iff
  statement: p.comp (X + C t) = 0 ↔ p = 0
  proof: EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXAddC t)

中文:
引理 comp_X_add_C_eq_zero_iff
  结论: p.comp (X + C t) = 0 ↔ p = 0
  证明: EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXAddC t)

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_eq_zero_iff, algEquivAevalXAddC, map_eq_zero_iff
-/
lemma comp_X_add_C_eq_zero_iff : p.comp (X + C t) = 0 ↔ p = 0 :=
  EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXAddC t)

/--
lemma `comp_X_add_C_ne_zero_iff` / 引理 `comp_X_add_C_ne_zero_iff`

English:
lemma comp_X_add_C_ne_zero_iff
  statement: p.comp (X + C t) != 0 ↔ p != 0
  proof: comp_X_add_C_eq_zero_iff.not

中文:
引理 comp_X_add_C_ne_zero_iff
  结论: p.comp (X + C t) != 0 ↔ p != 0
  证明: comp_X_add_C_eq_zero_iff.not

Depends on / 依赖: comp_X_add_C_eq_zero_iff, comp_X_add_C_eq_zero_iff.not
-/
lemma comp_X_add_C_ne_zero_iff : p.comp (X + C t) != 0 ↔ p != 0 := comp_X_add_C_eq_zero_iff.not

/--
lemma `dvd_comp_C_mul_X_add_C_iff` / 引理 `dvd_comp_C_mul_X_add_C_iff`

English:
lemma dvd_comp_C_mul_X_add_C_iff
  given: (p q : R[X]) (a b : R) [Invertible a]
  proof: by
convert! map_dvd_iff algEquivCMulXAddC a b using 2
  simp [← comp_eq_aeval, comp_assoc, ← mul_assoc, ← C_mul]

中文:
引理 dvd_comp_C_mul_X_add_C_iff
  条件: (p q : R[X]) (a b : R) [可逆 a]
  证明: by
convert! map_dvd_iff algEquivCMulXAddC a b using 2
  simp [← comp_eq_aeval, comp_assoc, ← mul_assoc, ← C_mul]

Depends on / 依赖: C_mul, algEquivCMulXAddC, comp_assoc, comp_eq_aeval, convert, map_dvd_iff, mul_assoc
-/
lemma dvd_comp_C_mul_X_add_C_iff (p q : R[X]) (a b : R) [Invertible a] :
    p ∣ q.comp (C a * X + C b) ↔ p.comp (C ⅟a * (X - C b)) ∣ q := by
convert! map_dvd_iff algEquivCMulXAddC a b using 2
  simp [← comp_eq_aeval, comp_assoc, ← mul_assoc, ← C_mul]

/--
lemma `dvd_comp_X_sub_C_iff` / 引理 `dvd_comp_X_sub_C_iff`

English:
lemma dvd_comp_X_sub_C_iff
  given: (p q : R[X]) (a : R)
  proof: by
  let _ := invertibleOne (α := R)
  simpa using! dvd_comp_C_mul_X_add_C_iff p q 1 (-a)

中文:
引理 dvd_comp_X_sub_C_iff
  条件: (p q : R[X]) (a : R)
  证明: by
  let _ := invertibleOne (α := R)
  simpa using! dvd_comp_C_mul_X_add_C_iff p q 1 (-a)

Depends on / 依赖: dvd_comp_C_mul_X_add_C_iff, invertibleOne
-/
lemma dvd_comp_X_sub_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X - C a) ↔ p.comp (X + C a) ∣ q := by
  let _ := invertibleOne (α := R)
  simpa using! dvd_comp_C_mul_X_add_C_iff p q 1 (-a)

/--
lemma `dvd_comp_X_add_C_iff` / 引理 `dvd_comp_X_add_C_iff`

English:
lemma dvd_comp_X_add_C_iff
  given: (p q : R[X]) (a : R)
  proof: by
  simpa using! dvd_comp_X_sub_C_iff p q (-a)

中文:
引理 dvd_comp_X_add_C_iff
  条件: (p q : R[X]) (a : R)
  证明: by
  simpa using! dvd_comp_X_sub_C_iff p q (-a)

Depends on / 依赖: dvd_comp_X_sub_C_iff
-/
lemma dvd_comp_X_add_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X + C a) ↔ p.comp (X - C a) ∣ q := by
  simpa using! dvd_comp_X_sub_C_iff p q (-a)

/--
lemma `dvd_comp_neg_X_iff` / 引理 `dvd_comp_neg_X_iff`

English:
lemma dvd_comp_neg_X_iff
  given: (p q : R[X])
  statement: p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q
  proof: by
  let _ := invertibleOne (α := R)
  let _ := invertibleNeg (R := R) 1
  simpa using dvd_comp_C_mul_X_add_C_iff p q (-1) 0

中文:
引理 dvd_comp_neg_X_iff
  条件: (p q : R[X])
  结论: p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q
  证明: by
  let _ := invertibleOne (α := R)
  let _ := invertibleNeg (R := R) 1
  simpa using dvd_comp_C_mul_X_add_C_iff p q (-1) 0

Depends on / 依赖: dvd_comp_C_mul_X_add_C_iff, invertibleNeg, invertibleOne
-/
lemma dvd_comp_neg_X_iff (p q : R[X]) : p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q := by
  let _ := invertibleOne (α := R)
  let _ := invertibleNeg (R := R) 1
  simpa using dvd_comp_C_mul_X_add_C_iff p q (-1) 0

variable [IsDomain R]

/--
lemma `units_coeff_zero_smul` / 引理 `units_coeff_zero_smul`

English:
lemma units_coeff_zero_smul
  given: (c : R[X]ˣ) (p : R[X])
  statement: (c : R[X]).coeff 0 • p = c * p
  proof: by
  rw [← Polynomial.C_mul']; rw [← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

中文:
引理 units_coeff_zero_smul
  条件: (c : R[X]ˣ) (p : R[X])
  结论: (c : R[X]).coeff 0 • p = c * p
  证明: by
  rw [← Polynomial.C_mul']; rw [← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

Depends on / 依赖: C_mul, Polynomial, Polynomial.C_mul, Polynomial.eq_C_of_degree_eq_zero, degree_coe_units, eq_C_of_degree_eq_zero
-/
lemma units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul']; rw [← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

end CommRing

section StableSubmodule

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

/--
lemma `aeval_apply_smul_mem_of_le_comap'` / 引理 `aeval_apply_smul_mem_of_le_comap'`

English:
lemma aeval_apply_smul_mem_of_le_comap'
  proof: by
  induction p using Polynomial.induction_on with
  | C a => simpa using SMulMemClass.smul_mem a hm
  | add f₁ f₂ h₁ h₂ =>
    simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  | monomial n t hmq =>
    rw [pow_succ']; rw [mul_left_comm]; rw [map_mul]; rw [aeval_X]; rw [mul_smul]
    solve_by_elim

中文:
引理 aeval_apply_smul_mem_of_le_comap'
  证明: by
  induction p using Polynomial.induction_on with
  | C a => simpa using SMulMemClass.smul_mem a hm
  | add f₁ f₂ h₁ h₂ =>
    simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  | monomial n t hmq =>
    rw [pow_succ']; rw [mul_left_comm]; rw [map_mul]; rw [aeval_X]; rw [mul_smul]
    solve_by_elim

Depends on / 依赖: Polynomial, Polynomial.induction_on, SMulMemClass, SMulMemClass.smul_mem, Submodule, Submodule.add_mem, add_mem, add_smul, aeval_X, induction_on, map_add, map_mul, monomial, mul_left_comm, mul_smul, pow_succ, simp_rw, smul_mem, solve_by_elim
-/
lemma aeval_apply_smul_mem_of_le_comap'
    [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m in q) (p : R[X]) (a : A)
    (hq : q <= q.comap (Algebra.lsmul R R M a)) :
    aeval a p • m in q := by
  induction p using Polynomial.induction_on with
  | C a => simpa using SMulMemClass.smul_mem a hm
  | add f₁ f₂ h₁ h₂ =>
    simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  | monomial n t hmq =>
    rw [pow_succ']; rw [mul_left_comm]; rw [map_mul]; rw [aeval_X]; rw [mul_smul]
    solve_by_elim

/--
lemma `aeval_apply_smul_mem_of_le_comap` / 引理 `aeval_apply_smul_mem_of_le_comap`

English:
lemma aeval_apply_smul_mem_of_le_comap
  proof: aeval_apply_smul_mem_of_le_comap' hm p f hq

中文:
引理 aeval_apply_smul_mem_of_le_comap
  证明: aeval_apply_smul_mem_of_le_comap' hm p f hq

Depends on / 依赖: aeval_apply_smul_mem_of_le_comap
-/
lemma aeval_apply_smul_mem_of_le_comap
    (hm : m in q) (p : R[X]) (f : Module.End R M) (hq : q <= q.comap f) :
    aeval f p m in q :=
  aeval_apply_smul_mem_of_le_comap' hm p f hq

end StableSubmodule

section CommSemiring

variable [CommSemiring R] {a p : R[X]}

/--
theorem `eq_zero_of_mul_eq_zero_of_smul` / 定理 `eq_zero_of_mul_eq_zero_of_smul`

English:
theorem eq_zero_of_mul_eq_zero_of_smul
  statement: (P : R[X]) (h : forall r : R, r • P = 0 -> r = 0) (Q : R[X])
  proof: by
  suffices forall i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i => congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi]; rw [zero_smul]
  intro l IH
  obtain _ | hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul]; rw [mul_left_comm]; rw [hQ]; rw [mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi | rfl | hi := lt_trichotomy i l
  · have hj : m < j := by lia
    rw [coeff_eq_zero_of_natDegree_lt hj]; rw [mul_zero]
  · lia
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

中文:
定理 eq_zero_of_mul_eq_zero_of_smul
  结论: (P : R[X]) (h : 对任意 r : R, r • P = 0 -> r = 0) (Q : R[X])
  证明: by
  suffices forall i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i => congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi]; rw [zero_smul]
  intro l IH
  obtain _ | hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul]; rw [mul_left_comm]; rw [hQ]; rw [mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi | rfl | hi := lt_trichotomy i l
  · have hj : m < j := by lia
    rw [coeff_eq_zero_of_natDegree_lt hj]; rw [mul_zero]
  · lia
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

Depends on / 依赖: Nat.strong_decreasing_induction, P.coeff, P.natDegree, Q.leadingCoeff, Q.natDegree, coeff_eq_zero_of_natDegree_lt, congr_arg, eq_zero_of_mul_eq_zero_of_smul, ext_iff, leadingCoeff, leadingCoeff_eq_zero, lt_or_eq, mul_comm, mul_left_comm, mul_zero, natDegree, natDegree_smul_le, smul_eq_C_mul, strong_decreasing_induction, zero_smul
-/
theorem eq_zero_of_mul_eq_zero_of_smul (P : R[X]) (h : forall r : R, r • P = 0 -> r = 0) (Q : R[X])
    (hQ : P * Q = 0) : Q = 0 := by
  suffices forall i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i => congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi]; rw [zero_smul]
  intro l IH
  obtain _ | hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul]; rw [mul_left_comm]; rw [hQ]; rw [mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi | rfl | hi := lt_trichotomy i l
  · have hj : m < j := by lia
    rw [coeff_eq_zero_of_natDegree_lt hj]; rw [mul_zero]
  · lia
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

open nonZeroDivisors

/--
theorem `notMem_nonZeroDivisors_iff` / 定理 `notMem_nonZeroDivisors_iff`

English:
theorem notMem_nonZeroDivisors_iff
  given: {P : R[X]}
  statement: P ∉ R[X]⁰ ↔ exists a : R, a != 0 ∧ a • P = 0
  proof: by
refine ⟨fun hP => ?_, fun ⟨a, ha, h⟩ h1 => ha C_eq_zero.1 (h1.2 _) smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := notMem_nonZeroDivisors_iff_right.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha => ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

中文:
定理 notMem_nonZeroDivisors_iff
  条件: {P : R[X]}
  结论: P ∉ R[X]⁰ ↔ 存在 a : R, a != 0 ∧ a • P = 0
  证明: by
refine ⟨fun hP => ?_, fun ⟨a, ha, h⟩ h1 => ha C_eq_zero.1 (h1.2 _) smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := notMem_nonZeroDivisors_iff_right.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha => ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

Depends on / 依赖: C_eq_zero, contrapose, eq_zero_of_mul_eq_zero_of_smul, mul_comm, notMem_nonZeroDivisors_iff_right, smul_eq_C_mul
-/
theorem notMem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ exists a : R, a != 0 ∧ a • P = 0 := by
refine ⟨fun hP => ?_, fun ⟨a, ha, h⟩ h1 => ha C_eq_zero.1 (h1.2 _) smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := notMem_nonZeroDivisors_iff_right.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha => ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

/--
lemma `mem_nonZeroDivisors_iff` / 引理 `mem_nonZeroDivisors_iff`

English:
lemma mem_nonZeroDivisors_iff
  given: {P : R[X]}
  statement: P in R[X]⁰ ↔ forall a : R, a • P = 0 -> a = 0
  proof: by
  simpa [not_imp_not] using (notMem_nonZeroDivisors_iff (P := P)).not

中文:
引理 mem_nonZeroDivisors_iff
  条件: {P : R[X]}
  结论: P in R[X]⁰ ↔ 对任意 a : R, a • P = 0 -> a = 0
  证明: by
  simpa [not_imp_not] using (notMem_nonZeroDivisors_iff (P := P)).not
-/
protected lemma mem_nonZeroDivisors_iff {P : R[X]} : P in R[X]⁰ ↔ forall a : R, a • P = 0 -> a = 0 := by
  simpa [not_imp_not] using (notMem_nonZeroDivisors_iff (P := P)).not

/--
lemma `mem_nonzeroDivisors_of_coeff_mem` / 引理 `mem_nonzeroDivisors_of_coeff_mem`

English:
lemma mem_nonzeroDivisors_of_coeff_mem
  given: {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰)
  proof: Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr => hp.2 _ (by simpa using congr(coeff $hr n))

中文:
引理 mem_nonzeroDivisors_of_coeff_mem
  条件: {p : R[X]} (n : 自然数) (hp : p.coeff n in R⁰)
  证明: Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr => hp.2 _ (by simpa using congr(coeff $hr n))

Depends on / 依赖: Polynomial, Polynomial.mem_nonZeroDivisors_iff.mpr, mem_nonZeroDivisors_iff
-/
lemma mem_nonzeroDivisors_of_coeff_mem {p : R[X]} (n : Nat) (hp : p.coeff n in R⁰) :
    p in R[X]⁰ :=
  Polynomial.mem_nonZeroDivisors_iff.mpr fun r hr => hp.2 _ (by simpa using congr(coeff $hr n))

/--
lemma `X_mem_nonzeroDivisors` / 引理 `X_mem_nonzeroDivisors`

English:
lemma X_mem_nonzeroDivisors
  statement: X in R[X]⁰
  proof: mem_nonzeroDivisors_of_coeff_mem 1 (by simp [one_mem])

中文:
引理 X_mem_nonzeroDivisors
  结论: X in R[X]⁰
  证明: mem_nonzeroDivisors_of_coeff_mem 1 (by simp [one_mem])

Depends on / 依赖: mem_nonzeroDivisors_of_coeff_mem, one_mem
-/
lemma X_mem_nonzeroDivisors : X in R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem 1 (by simp [one_mem])

end CommSemiring

end Polynomial
