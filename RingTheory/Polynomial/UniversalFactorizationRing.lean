/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal


/-!

# Universal factorization ring

Let `R` be a commutative ring and `p : R[X]` be monic of degree `n` and let `n = m + k`.
We construct the universal ring of the following functors on `R-Alg`:
- `S ↦ "monic polynomials over S of degree n"`:
  Represented by `R[X₁,...,Xₙ]`. See `MvPolynomial.mapEquivMonic`.
- `S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`:
  Represented by an `R`-algebra (`Polynomial.UniversalFactorizationRing`) that is finitely-presented
  as an `R`-module. See `Polynomial.UniversalFactorizationRing.homEquiv`.
- `S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`:
  Represented by an etale `R`-algebra (`Polynomial.UniversalCoprimeFactorizationRing`).
  See `Polynomial.UniversalCoprimeFactorizationRing.homEquiv`.

-/

@[expose] public section

open scoped Polynomial TensorProduct

open RingHomClass (toRingHom)

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : Nat) (hn : n = m + k)

noncomputable section

namespace Polynomial

/--
Definition of `freeMonic` / `freeMonic` 的定义

English:
definition freeMonic
  signature: : (MvPolynomial (Fin n) R)[X]
  body: .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : Nat)

中文:
定义 freeMonic
  签名: : (多元多项式 (有限集 n) R)[X]
  定义体: .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : Nat)
-/
def freeMonic : (MvPolynomial (Fin n) R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : Nat)

/--
lemma `coeff_freeMonic` / 引理 `coeff_freeMonic`

English:
lemma coeff_freeMonic
  proof: by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ => if_neg (by cases x; lia), add_zero, dif_neg h]

中文:
引理 coeff_freeMonic
  证明: by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ => if_neg (by cases x; lia), add_zero, dif_neg h]

Depends on / 依赖: Fin.ext_iff, Finset, Finset.sum_eq_single, Finset.sum_eq_zero, Polynomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_add, Polynomial.finsetSum_coeff, add_zero, coeff_C_mul, coeff_X_pow, coeff_add, contextual, dif_neg, eq_comm, ext_iff, finsetSum_coeff, freeMonic, h.ne
-/
lemma coeff_freeMonic :
    (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ => if_neg (by cases x; lia), add_zero, dif_neg h]

/--
lemma `degree_freeMonic` / 引理 `degree_freeMonic`

English:
lemma degree_freeMonic
  given: [Nontrivial R]
  statement: (freeMonic R n).degree = n
  proof: Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

中文:
引理 degree_freeMonic
  条件: [非平凡 R]
  结论: (freeMonic R n).degree = n
  证明: Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

Depends on / 依赖: LT.lt.ne, LT.lt.not_gt, Polynomial, Polynomial.degree_eq_of_le_of_coeff_ne_zero, Polynomial.degree_le_iff_coeff_zero, coeff_freeMonic, contextual, degree_eq_of_le_of_coeff_ne_zero, degree_le_iff_coeff_zero, not_gt
-/
lemma degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])

/--
lemma `natDegree_freeMonic` / 引理 `natDegree_freeMonic`

English:
lemma natDegree_freeMonic
  given: [Nontrivial R]
  statement: (freeMonic R n).natDegree = n
  proof: natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

中文:
引理 natDegree_freeMonic
  条件: [非平凡 R]
  结论: (freeMonic R n).natDegree = n
  证明: natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

Depends on / 依赖: degree_freeMonic, natDegree_eq_of_degree_eq_some
-/
lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R n)

/--
lemma `monic_freeMonic` / 引理 `monic_freeMonic`

English:
lemma monic_freeMonic
  statement: (freeMonic R n).Monic
  proof: by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in

中文:
引理 monic_freeMonic
  结论: (freeMonic R n).Monic
  证明: by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in

Depends on / 依赖: Polynomial, Polynomial.Monic, Polynomial.coeff_natDegree, coeff_freeMonic, coeff_natDegree, natDegree_freeMonic, nontriviality
-/
lemma monic_freeMonic : (freeMonic R n).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in
/--
lemma `map_map_freeMonic` / 引理 `map_map_freeMonic`

English:
lemma map_map_freeMonic
  given: (f : R ->+* S)
  proof: by
  simp [freeMonic, Polynomial.map_sum]

中文:
引理 map_map_freeMonic
  条件: (f : R ->+* S)
  证明: by
  simp [freeMonic, Polynomial.map_sum]

Depends on / 依赖: Polynomial, Polynomial.map_sum, freeMonic, map_sum
-/
lemma map_map_freeMonic (f : R ->+* S) :
    (freeMonic R n).map (MvPolynomial.map f) = freeMonic S n := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)

/-- The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X]`. -/
@[simps]
/--
Definition of `MonicDegreeEq.freeMonic` / `MonicDegreeEq.freeMonic` 的定义

English:
definition MonicDegreeEq.freeMonic
  signature: : MonicDegreeEq (MvPolynomial (Fin n) R) n
  body: ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

中文:
定义 MonicDegreeEq.freeMonic
  签名: : MonicDegreeEq (多元多项式 (有限集 n) R) n
  定义体: ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

Depends on / 依赖: LT.lt.ne, coeff_freeMonic, contextual, freeMonic, not_lt_of_gt
-/
def MonicDegreeEq.freeMonic : MonicDegreeEq (MvPolynomial (Fin n) R) n :=
  ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

end Polynomial

namespace MvPolynomial

open Polynomial

/--
Definition of `mapEquivMonic` / `mapEquivMonic` 的定义

English:
definition mapEquivMonic
  signature: : (MvPolynomial (Fin n) R ->ₐ[R] S) ≃ MonicDegreeEq S n where
  body: .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices forall i >= n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

中文:
定义 mapEquivMonic
  签名: : (多元多项式 (有限集 n) R ->ₐ[R] S) ≃ MonicDegreeEq S n where
  定义体: .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices forall i >= n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

Depends on / 依赖: f.toRingHom, freeMonic, toRingHom
-/
def mapEquivMonic : (MvPolynomial (Fin n) R ->ₐ[R] S) ≃ MonicDegreeEq S n where
  toFun f := .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices forall i >= n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

variable {R S T} in
/--
lemma `coe_mapEquivMonic_comp` / 引理 `coe_mapEquivMonic_comp`

English:
lemma coe_mapEquivMonic_comp
  given: (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T)
  proof: (Polynomial.map_map ..).symm

中文:
引理 coe_mapEquivMonic_comp
  条件: (f : 多元多项式 (有限集 n) R ->ₐ[R] S) (g : S ->ₐ[R] T)
  证明: (Polynomial.map_map ..).symm

Depends on / 依赖: Polynomial, Polynomial.map_map, map_map
-/
lemma coe_mapEquivMonic_comp (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T) :
    (mapEquivMonic R T n (g.comp f)).1 = (mapEquivMonic R S n f).1.map g :=
  (Polynomial.map_map ..).symm

variable {R S T} in
/--
lemma `coe_mapEquivMonic_comp'` / 引理 `coe_mapEquivMonic_comp'`

English:
lemma coe_mapEquivMonic_comp'
  given: (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T)
  proof: Subtype.ext (coe_mapEquivMonic_comp ..)

中文:
引理 coe_mapEquivMonic_comp'
  条件: (f : 多元多项式 (有限集 n) R ->ₐ[R] S) (g : S ->ₐ[R] T)
  证明: Subtype.ext (coe_mapEquivMonic_comp ..)

Depends on / 依赖: Subtype, Subtype.ext, coe_mapEquivMonic_comp
-/
lemma coe_mapEquivMonic_comp' (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T) :
    mapEquivMonic R T n (g.comp f) = (mapEquivMonic R S n f).map g :=
  Subtype.ext (coe_mapEquivMonic_comp ..)

variable {R S T} in
/--
lemma `mapEquivMonic_symm_map` / 引理 `mapEquivMonic_symm_map`

English:
lemma mapEquivMonic_symm_map
  given: (p : MonicDegreeEq S n) (g : S ->ₐ[R] T)
  proof: by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

中文:
引理 mapEquivMonic_symm_map
  条件: (p : MonicDegreeEq S n) (g : S ->ₐ[R] T)
  证明: by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

Depends on / 依赖: coe_mapEquivMonic_comp, mapEquivMonic, surjective, symm_apply_eq, symm_apply_eq.mpr
-/
lemma mapEquivMonic_symm_map (p : MonicDegreeEq S n) (g : S ->ₐ[R] T) :
    (mapEquivMonic R T n).symm (p.map g) = g.comp ((mapEquivMonic R S n).symm p) := by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

variable {R S T} in
/--
lemma `mapEquivMonic_symm_map_algebraMap` / 引理 `mapEquivMonic_symm_map_algebraMap`

English:
lemma mapEquivMonic_symm_map_algebraMap
  proof: by
  rw [← mapEquivMonic_symm_map]; rw [IsScalarTower.coe_toAlgHom]

中文:
引理 mapEquivMonic_symm_map_algebraMap
  证明: by
  rw [← mapEquivMonic_symm_map]; rw [IsScalarTower.coe_toAlgHom]

Depends on / 依赖: IsScalarTower, IsScalarTower.coe_toAlgHom, coe_toAlgHom, mapEquivMonic_symm_map
-/
lemma mapEquivMonic_symm_map_algebraMap
    (p : MonicDegreeEq S n) [Algebra S T] [IsScalarTower R S T] :
    (mapEquivMonic R T n).symm (p.map (algebraMap S T)) =
      (IsScalarTower.toAlgHom R S T).comp ((mapEquivMonic R S n).symm p) := by
  rw [← mapEquivMonic_symm_map]; rw [IsScalarTower.coe_toAlgHom]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `universalFactorizationMap` / `universalFactorizationMap` 的定义

English:
definition universalFactorizationMap
  signature: (hn : n = m + k)
  body: (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

中文:
定义 universalFactorizationMap
  签名: (hn : n = m + k)
  定义体: (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, MonicDegreeEq, MonicDegreeEq.mk, MvPolynomial, TensorProduct, includeLeft, includeRight, mapEquivMonic, monic_freeMonic, natDegre, natDegree_map, natDegree_mul, nontriviality, otimes, simp_rw
-/
def universalFactorizationMap (hn : n = m + k) :
    MvPolynomial (Fin n) R ->ₐ[R] MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R :=
  (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `universalFactorizationMap_freeMonic` / 引理 `universalFactorizationMap_freeMonic`

English:
lemma universalFactorizationMap_freeMonic
  proof: by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

中文:
引理 universalFactorizationMap_freeMonic
  证明: by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

Depends on / 依赖: mapEquivMonic, universalFactorizationMap
-/
lemma universalFactorizationMap_freeMonic :
    (freeMonic R n).map (toRingHom <| universalFactorizationMap R n m k hn) =
      (freeMonic R m).map (algebraMap _ _) *
        (freeMonic R k).map (toRingHom <| Algebra.TensorProduct.includeRight) := by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `universalFactorizationMap_comp_map` / 引理 `universalFactorizationMap_comp_map`

English:
lemma universalFactorizationMap_comp_map
  proof: by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr 2 <;> ext <;> simp

中文:
引理 universalFactorizationMap_comp_map
  证明: by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr 2 <;> ext <;> simp
-/
lemma universalFactorizationMap_comp_map :
    (universalFactorizationMap S n m k hn).toRingHom.comp (map (algebraMap R S)) =
    .comp (Algebra.TensorProduct.lift (S := R)
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId R S)))
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)))
      fun _ _ => .all _ _).toRingHom
      (universalFactorizationMap R n m k hn).toRingHom := by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr 2 <;> ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `universalFactorizationMapLiftEquiv` / `universalFactorizationMapLiftEquiv` 的定义

English:
definition universalFactorizationMapLiftEquiv
  signature: (p : MonicDegreeEq S n)
  body: ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ => .all _ _, by
refine (mapEquivMonic R S n).eq_symm_apply.mpr Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

中文:
定义 universalFactorizationMapLiftEquiv
  签名: (p : MonicDegreeEq S n)
  定义体: ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ => .all _ _, by
refine (mapEquivMonic R S n).eq_symm_apply.mpr Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeft, TensorProduct, includeLeft, mapEquivMonic
-/
def universalFactorizationMapLiftEquiv (p : MonicDegreeEq S n) :
    { f // AlgHom.comp f (universalFactorizationMap R n m k hn) =
        (mapEquivMonic _ _ n).symm p } ≃
    { q : MonicDegreeEq S m × MonicDegreeEq S k // q.1.1 * q.2.1 = p } where
  toFun f := ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ => .all _ _, by
refine (mapEquivMonic R S n).eq_symm_apply.mpr Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ker_eval₂Hom_universalFactorizationMap` / 引理 `ker_eval₂Hom_universalFactorizationMap`

English:
lemma ker_eval₂Hom_universalFactorizationMap
  proof: by
  set f := eval₂Hom (R := MvPolynomial (Fin n) R)
    (S₁ := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
    (universalFactorizationMap R n m k hn) (Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·))
  have H (i : _) : tensorEquivSum _ _ _ _ (f (.X i)) = .X i := by aesop
  apply le_antisymm
  · intro x hx
    convert_to x - (tensorEquivSum _ _ _ _ (f x)).map C in Ideal.span _ using 1
    · simp_all only [RingHom.mem_ker, map_zero, sub_zero]
    clear hx
    induction x using MvPolynomial.induction_on with
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i _ => simp only [map_mul, H, map_X, ← sub_mul]; exact Ideal.mul_mem_right _ _ ‹_›
    | C x =>
    induction x using MvPolynomial.induction_on with
    | C a => simp [f]
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i IH =>
      simp only [map_mul]
      exact Ideal.mul_sub_mul_mem _ IH (Ideal.subset_span ⟨i, by simp [f]⟩)
  · simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      eval₂Hom_C, RingHom.coe_coe, eval₂Hom_map_hom, coe_eval₂Hom, sub_eq_zero, f]
    simp only [← algebraMap_eq, AlgHom.comp_algebraMap_of_tower, ← aeval_def]
    intro i
    generalize universalFactorizationMap R n m k hn (X i) = p
    change AlgHom.id R _ p = ((aeval _).comp (tensorEquivSum R _ _ R).toAlgHom) p
    congr 1
    ext <;> simp

中文:
引理 ker_eval₂Hom_universalFactorizationMap
  证明: by
  set f := eval₂Hom (R := MvPolynomial (Fin n) R)
    (S₁ := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
    (universalFactorizationMap R n m k hn) (Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·))
  have H (i : _) : tensorEquivSum _ _ _ _ (f (.X i)) = .X i := by aesop
  apply le_antisymm
  · intro x hx
    convert_to x - (tensorEquivSum _ _ _ _ (f x)).map C in Ideal.span _ using 1
    · simp_all only [RingHom.mem_ker, map_zero, sub_zero]
    clear hx
    induction x using MvPolynomial.induction_on with
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i _ => simp only [map_mul, H, map_X, ← sub_mul]; exact Ideal.mul_mem_right _ _ ‹_›
    | C x =>
    induction x using MvPolynomial.induction_on with
    | C a => simp [f]
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i IH =>
      simp only [map_mul]
      exact Ideal.mul_sub_mul_mem _ IH (Ideal.subset_span ⟨i, by simp [f]⟩)
  · simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      eval₂Hom_C, RingHom.coe_coe, eval₂Hom_map_hom, coe_eval₂Hom, sub_eq_zero, f]
    simp only [← algebraMap_eq, AlgHom.comp_algebraMap_of_tower, ← aeval_def]
    intro i
    generalize universalFactorizationMap R n m k hn (X i) = p
    change AlgHom.id R _ p = ((aeval _).comp (tensorEquivSum R _ _ R).toAlgHom) p
    congr 1
    ext <;> simp

Depends on / 依赖: MvPolynomial, otimes
-/
lemma ker_eval₂Hom_universalFactorizationMap :
    RingHom.ker (eval₂Hom (S₁ := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
      (universalFactorizationMap R n m k hn) (Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·))) =
    Ideal.span (Set.range fun i => C (X i) - map C (tensorEquivSum _ _ _ _
      (universalFactorizationMap R n m k hn (X i)))) := by
  set f := eval₂Hom (R := MvPolynomial (Fin n) R)
    (S₁ := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
    (universalFactorizationMap R n m k hn) (Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·))
  have H (i : _) : tensorEquivSum _ _ _ _ (f (.X i)) = .X i := by aesop
  apply le_antisymm
  · intro x hx
    convert_to x - (tensorEquivSum _ _ _ _ (f x)).map C in Ideal.span _ using 1
    · simp_all only [RingHom.mem_ker, map_zero, sub_zero]
    clear hx
    induction x using MvPolynomial.induction_on with
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i _ => simp only [map_mul, H, map_X, ← sub_mul]; exact Ideal.mul_mem_right _ _ ‹_›
    | C x =>
    induction x using MvPolynomial.induction_on with
    | C a => simp [f]
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i IH =>
      simp only [map_mul]
      exact Ideal.mul_sub_mul_mem _ IH (Ideal.subset_span ⟨i, by simp [f]⟩)
  · simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      eval₂Hom_C, RingHom.coe_coe, eval₂Hom_map_hom, coe_eval₂Hom, sub_eq_zero, f]
    simp only [← algebraMap_eq, AlgHom.comp_algebraMap_of_tower, ← aeval_def]
    intro i
    generalize universalFactorizationMap R n m k hn (X i) = p
    change AlgHom.id R _ p = ((aeval _).comp (tensorEquivSum R _ _ R).toAlgHom) p
    congr 1
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `universalFactorizationMapPresentation` / `universalFactorizationMapPresentation` 的定义

English:
definition universalFactorizationMapPresentation
  signature: :
  body: (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (Fin m oplus Fin k) (Fin n) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  { val := Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·)
    σ' f := (tensorEquivSum _ _ _ _ f).map C
    aeval_val_σ' s := by
      change ((aeval _).restrictScalars R |>.comp (mapAlgHom (Algebra.ofId _ _)) |>.comp
          (tensorEquivSum R (Fin m) (Fin k) R).toAlgHom) s = AlgHom.id R _ s
      congr 1
      ext <;> simp
    algebra := (aeval _).toAlgebra
    algebraMap_eq := rfl
    relation i := .C (.X i) - (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (.X i))).map C
    span_range_relation_eq_ker := by
      exact (ker_eval₂Hom_universalFactorizationMap R n m k hn).symm,
    map := finSumFinEquiv.symm ∘ finCongr hn
    map_inj := finSumFinEquiv.symm.injective.comp (finCongr hn).injective }

中文:
定义 universalFactorizationMapPresentation
  签名: :
  定义体: (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (Fin m oplus Fin k) (Fin n) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  { val := Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·)
    σ' f := (tensorEquivSum _ _ _ _ f).map C
    aeval_val_σ' s := by
      change ((aeval _).restrictScalars R |>.comp (mapAlgHom (Algebra.ofId _ _)) |>.comp
          (tensorEquivSum R (Fin m) (Fin k) R).toAlgHom) s = AlgHom.id R _ s
      congr 1
      ext <;> simp
    algebra := (aeval _).toAlgebra
    algebraMap_eq := rfl
    relation i := .C (.X i) - (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (.X i))).map C
    span_range_relation_eq_ker := by
      exact (ker_eval₂Hom_universalFactorizationMap R n m k hn).symm,
    map := finSumFinEquiv.symm ∘ finCongr hn
    map_inj := finSumFinEquiv.symm.injective.comp (finCongr hn).injective }
-/
@[simps] def universalFactorizationMapPresentation :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (Fin m oplus Fin k) (Fin n) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  { val := Sum.elim (.X · otimesₜ 1) (1 otimesₜ .X ·)
    σ' f := (tensorEquivSum _ _ _ _ f).map C
    aeval_val_σ' s := by
      change ((aeval _).restrictScalars R |>.comp (mapAlgHom (Algebra.ofId _ _)) |>.comp
          (tensorEquivSum R (Fin m) (Fin k) R).toAlgHom) s = AlgHom.id R _ s
      congr 1
      ext <;> simp
    algebra := (aeval _).toAlgebra
    algebraMap_eq := rfl
    relation i := .C (.X i) - (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (.X i))).map C
    span_range_relation_eq_ker := by
      exact (ker_eval₂Hom_universalFactorizationMap R n m k hn).symm,
    map := finSumFinEquiv.symm ∘ finCongr hn
    map_inj := finSumFinEquiv.symm.injective.comp (finCongr hn).injective }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pderiv_inl_universalFactorizationMap_X` / 引理 `pderiv_inl_universalFactorizationMap_X`

English:
lemma pderiv_inl_universalFactorizationMap_X
  given: (i j)
  proof: by
  trans ∑ x in Finset.antidiagonal ↑j,
    if h : x.2 < k then if x.1 < m ∧ x.1 = ↑i then X (Sum.inr ⟨x.2, h⟩) else 0
    else if x.2 = k ∧ x.1 < m ∧ x.1 = ↑i then 1 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show a != i by lia]
    rw [Finset.sum_eq_single ⟨i.1]; rw [j.1 - i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
      intro a b e h
      simp [show a != i by lia]
    · simp [h]

中文:
引理 pderiv_inl_universalFactorizationMap_X
  条件: (i j)
  证明: by
  trans ∑ x in Finset.antidiagonal ↑j,
    if h : x.2 < k then if x.1 < m ∧ x.1 = ↑i then X (Sum.inr ⟨x.2, h⟩) else 0
    else if x.2 = k ∧ x.1 < m ∧ x.1 = ↑i then 1 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show a != i by lia]
    rw [Finset.sum_eq_single ⟨i.1]; rw [j.1 - i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
      intro a b e h
      simp [show a != i by lia]
    · simp [h]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, Fin.ext_iff, Finset, Finset.antidiagonal, Finset.mem_antidiagonal, Finset.sum_eq_zero, Pi.single_apply, Polynomial, Polynomial.coeff_mul, Prod.forall, Sum.inr, TensorProduct, antidiagonal, apply_dite, apply_ite, coeff_freeMonic, coeff_mul, ext_iff, if_pos
-/
lemma pderiv_inl_universalFactorizationMap_X (i j) :
    pderiv (Sum.inl i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : Nat) then 0 else if h : ↑j - ↑i < k then X (.inr ⟨↑j - ↑i, h⟩)
      else if ↑j - ↑i = k then 1 else 0 := by
  trans ∑ x in Finset.antidiagonal ↑j,
    if h : x.2 < k then if x.1 < m ∧ x.1 = ↑i then X (Sum.inr ⟨x.2, h⟩) else 0
    else if x.2 = k ∧ x.1 < m ∧ x.1 = ↑i then 1 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show a != i by lia]
    rw [Finset.sum_eq_single ⟨i.1]; rw [j.1 - i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
      intro a b e h
      simp [show a != i by lia]
    · simp [h]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `pderiv_inr_universalFactorizationMap_X` / 引理 `pderiv_inr_universalFactorizationMap_X`

English:
lemma pderiv_inr_universalFactorizationMap_X
  given: (i j)
  proof: by
  trans ∑ x in Finset.antidiagonal ↑j, if x.2 < k then if h : x.1 < m then if x.2 = ↑i then
    X (Sum.inl ⟨x.1, h⟩) else 0 else if x.1 = m ∧ x.2 = ↑i then 1 else 0 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal]
      lia
    rw [Finset.sum_eq_single ⟨j.1 - i.1]; rw [i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, ite_eq_right_iff, Prod.forall, Prod.mk.injEq]
      intro a b _ _ _
      simp [show b != i by lia]
    · simp [h]

中文:
引理 pderiv_inr_universalFactorizationMap_X
  条件: (i j)
  证明: by
  trans ∑ x in Finset.antidiagonal ↑j, if x.2 < k then if h : x.1 < m then if x.2 = ↑i then
    X (Sum.inl ⟨x.1, h⟩) else 0 else if x.1 = m ∧ x.2 = ↑i then 1 else 0 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal]
      lia
    rw [Finset.sum_eq_single ⟨j.1 - i.1]; rw [i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, ite_eq_right_iff, Prod.forall, Prod.mk.injEq]
      intro a b _ _ _
      simp [show b != i by lia]
    · simp [h]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, Fin.ext_iff, Finset, Finset.antidiagonal, Finset.mem_antidiagonal, Finset.sum_eq_single, Finset.sum_eq_zero, Pi.single_apply, Polynomial, Polynomial.coeff_mul, Sum.inl, TensorProduct, antidiagonal, apply_dite, apply_ite, coeff_freeMonic, coeff_mul, ext_iff, if_pos
-/
lemma pderiv_inr_universalFactorizationMap_X (i j) :
    pderiv (Sum.inr i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : Nat) then 0 else if h : ↑j - ↑i < m then
      X (.inl ⟨↑j - ↑i, h⟩) else if ↑j - ↑i = m then 1 else 0 := by
  trans ∑ x in Finset.antidiagonal ↑j, if x.2 < k then if h : x.1 < m then if x.2 = ↑i then
    X (Sum.inl ⟨x.1, h⟩) else 0 else if x.1 = m ∧ x.2 = ↑i then 1 else 0 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal]
      lia
    rw [Finset.sum_eq_single ⟨j.1 - i.1]; rw [i.1⟩]; rw [if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, ite_eq_right_iff, Prod.forall, Prod.mk.injEq]
      intro a b _ _ _
      simp [show b != i by lia]
    · simp [h]

/--
lemma `universalFactorizationMapPresentation_jacobiMatrix` / 引理 `universalFactorizationMapPresentation_jacobiMatrix`

English:
lemma universalFactorizationMapPresentation_jacobiMatrix
  proof: (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
    -((Polynomial.sylvester
      ((freeMonic R m).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inl)).toRingHom))
      ((freeMonic R k).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inr)).toRingHom))
      m k).reindex (finCongr (by lia)) (finCongr (by lia))).transpose := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  subst hn
  ext i j : 1
  dsimp [Polynomial.sylvester]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    induction j using Fin.addCases <;>
      simp [pderiv_map, coeff_freeMonic, apply_dite (DFunLike.coe _), apply_ite (DFunLike.coe _),
        pderiv_inl_universalFactorizationMap_X, pderiv_inr_universalFactorizationMap_X] <;> grind

中文:
引理 universalFactorizationMapPresentation_jacobiMatrix
  证明: (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
    -((Polynomial.sylvester
      ((freeMonic R m).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inl)).toRingHom))
      ((freeMonic R k).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inr)).toRingHom))
      m k).reindex (finCongr (by lia)) (finCongr (by lia))).transpose := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  subst hn
  ext i j : 1
  dsimp [Polynomial.sylvester]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    induction j using Fin.addCases <;>
      simp [pderiv_map, coeff_freeMonic, apply_dite (DFunLike.coe _), apply_ite (DFunLike.coe _),
        pderiv_inl_universalFactorizationMap_X, pderiv_inr_universalFactorizationMap_X] <;> grind

Depends on / 依赖: toAlgebra, universalFactorizationMap
-/
lemma universalFactorizationMapPresentation_jacobiMatrix :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
    -((Polynomial.sylvester
      ((freeMonic R m).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inl)).toRingHom))
      ((freeMonic R k).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inr)).toRingHom))
      m k).reindex (finCongr (by lia)) (finCongr (by lia))).transpose := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  subst hn
  ext i j : 1
  dsimp [Polynomial.sylvester]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    induction j using Fin.addCases <;>
      simp [pderiv_map, coeff_freeMonic, apply_dite (DFunLike.coe _), apply_ite (DFunLike.coe _),
        pderiv_inl_universalFactorizationMap_X, pderiv_inr_universalFactorizationMap_X] <;> grind

/--
lemma `universalFactorizationMapPresentation_jacobian` / 引理 `universalFactorizationMapPresentation_jacobian`

English:
lemma universalFactorizationMapPresentation_jacobian
  proof: (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobian =
    (-1) ^ n * (Polynomial.resultant
      ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom)
      ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]; rw [MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
  simp only [AlgHom.toRingHom_eq_coe, Matrix.det_neg, Matrix.det_transpose, Matrix.det_reindex_self,
    Algebra.Generators.algebraMap_apply, ← Polynomial.resultant.eq_def,
    Fintype.card_fin, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [← (aeval _).coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  congr 2
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]

中文:
引理 universalFactorizationMapPresentation_jacobian
  证明: (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobian =
    (-1) ^ n * (Polynomial.resultant
      ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom)
      ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]; rw [MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
  simp only [AlgHom.toRingHom_eq_coe, Matrix.det_neg, Matrix.det_transpose, Matrix.det_reindex_self,
    Algebra.Generators.algebraMap_apply, ← Polynomial.resultant.eq_def,
    Fintype.card_fin, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [← (aeval _).coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  congr 2
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]

Depends on / 依赖: toAlgebra, universalFactorizationMap
-/
lemma universalFactorizationMapPresentation_jacobian :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobian =
    (-1) ^ n * (Polynomial.resultant
      ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom)
      ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]; rw [MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
  simp only [AlgHom.toRingHom_eq_coe, Matrix.det_neg, Matrix.det_transpose, Matrix.det_reindex_self,
    Algebra.Generators.algebraMap_apply, ← Polynomial.resultant.eq_def,
    Fintype.card_fin, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [← (aeval _).coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]
  congr 2
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]

/--
lemma `finitePresentation_universalFactorizationMap` / 引理 `finitePresentation_universalFactorizationMap`

English:
lemma finitePresentation_universalFactorizationMap
  proof: letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).finitePresentation_of_isFinite

中文:
引理 finitePresentation_universalFactorizationMap
  证明: letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).finitePresentation_of_isFinite

Depends on / 依赖: finitePresentation_of_isFinite, toAlgebra, universalFactorizationMap, universalFactorizationMapPresentation
-/
lemma finitePresentation_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).FinitePresentation :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).finitePresentation_of_isFinite

set_option backward.isDefEq.respectTransparency false in
/--
lemma `finite_universalFactorizationMap` / 引理 `finite_universalFactorizationMap`

English:
lemma finite_universalFactorizationMap
  proof: by
  refine RingHom.IsIntegral.to_finite ?_
    (.of_finitePresentation (finitePresentation_universalFactorizationMap R n m k hn))
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : IsDomain (MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int) :=
    (MvPolynomial.tensorEquivSum Int (Fin m) (Fin k) Int).toRingEquiv.isDomain_iff.mpr inferInstance
  let := (universalFactorizationMap Int n m k hn).toAlgebra
  let F : MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int ->ₐ[Int]
      MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId Int R)))
      ((Algebra.TensorProduct.includeRight.restrictScalars Int).comp (mapAlgHom (Algebra.ofId Int R)))
      fun _ _ => .all _ _
  have H₁ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _) ⟨_, universalFactorizationMap_freeMonic Int n m k hn⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  have H₂ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _)
        ⟨_, (universalFactorizationMap_freeMonic Int n m k hn).trans (mul_comm _ _)⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | add x y _ _ => exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  | tmul x y =>
    suffices (universalFactorizationMap R n m k hn).IsIntegralElem (x otimesₜ 1 * 1 otimesₜ y) by simpa
    refine RingHom.IsIntegralElem.mul _ ?_ ?_
    · induction x using MvPolynomial.induction_on with
      | C a => simpa using! (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.add_tmul, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₁ i)
    · induction y using MvPolynomial.induction_on with
      | C a => simpa [← algebraMap_eq, ← algebraMap_apply, Algebra.algebraMap_eq_smul_one] using!
          (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.tmul_add, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₂ i)

中文:
引理 finite_universalFactorizationMap
  证明: by
  refine RingHom.IsIntegral.to_finite ?_
    (.of_finitePresentation (finitePresentation_universalFactorizationMap R n m k hn))
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : IsDomain (MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int) :=
    (MvPolynomial.tensorEquivSum Int (Fin m) (Fin k) Int).toRingEquiv.isDomain_iff.mpr inferInstance
  let := (universalFactorizationMap Int n m k hn).toAlgebra
  let F : MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int ->ₐ[Int]
      MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId Int R)))
      ((Algebra.TensorProduct.includeRight.restrictScalars Int).comp (mapAlgHom (Algebra.ofId Int R)))
      fun _ _ => .all _ _
  have H₁ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _) ⟨_, universalFactorizationMap_freeMonic Int n m k hn⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  have H₂ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _)
        ⟨_, (universalFactorizationMap_freeMonic Int n m k hn).trans (mul_comm _ _)⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | add x y _ _ => exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  | tmul x y =>
    suffices (universalFactorizationMap R n m k hn).IsIntegralElem (x otimesₜ 1 * 1 otimesₜ y) by simpa
    refine RingHom.IsIntegralElem.mul _ ?_ ?_
    · induction x using MvPolynomial.induction_on with
      | C a => simpa using! (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.add_tmul, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₁ i)
    · induction y using MvPolynomial.induction_on with
      | C a => simpa [← algebraMap_eq, ← algebraMap_apply, Algebra.algebraMap_eq_smul_one] using!
          (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.tmul_add, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₂ i)

Depends on / 依赖: IsDomain, IsIntegral, MvPolynomial, MvPolynomial.tensorEquivSum, RingHom, RingHom.IsIntegral.to_finite, finitePresentation_universalFactorizationMap, isDomain_iff, of_finitePresentation, otimes, tensorEquivSum, toAlgebra, toRingEquiv, toRingEquiv.isDomain_iff.mpr, to_finite, universalFactorizationMap
-/
lemma finite_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).Finite := by
  refine RingHom.IsIntegral.to_finite ?_
    (.of_finitePresentation (finitePresentation_universalFactorizationMap R n m k hn))
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : IsDomain (MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int) :=
    (MvPolynomial.tensorEquivSum Int (Fin m) (Fin k) Int).toRingEquiv.isDomain_iff.mpr inferInstance
  let := (universalFactorizationMap Int n m k hn).toAlgebra
  let F : MvPolynomial (Fin m) Int otimes[Int] MvPolynomial (Fin k) Int ->ₐ[Int]
      MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId Int R)))
      ((Algebra.TensorProduct.includeRight.restrictScalars Int).comp (mapAlgHom (Algebra.ofId Int R)))
      fun _ _ => .all _ _
  have H₁ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (.X i otimesₜ 1) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _) ⟨_, universalFactorizationMap_freeMonic Int n m k hn⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  have H₂ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap Int n m k hn).IsIntegralElem (1 otimesₜ .X i) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _)
        ⟨_, (universalFactorizationMap_freeMonic Int n m k hn).trans (mul_comm _ _)⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap Int R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂]; rw [← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | add x y _ _ => exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  | tmul x y =>
    suffices (universalFactorizationMap R n m k hn).IsIntegralElem (x otimesₜ 1 * 1 otimesₜ y) by simpa
    refine RingHom.IsIntegralElem.mul _ ?_ ?_
    · induction x using MvPolynomial.induction_on with
      | C a => simpa using! (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.add_tmul, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₁ i)
    · induction y using MvPolynomial.induction_on with
      | C a => simpa [← algebraMap_eq, ← algebraMap_apply, Algebra.algebraMap_eq_smul_one] using!
          (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.tmul_add, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₂ i)

end MvPolynomial

namespace Polynomial

open TensorProduct

variable {R n} (p : Polynomial.MonicDegreeEq R n)

attribute [-instance] leftModule in
/--
Definition of `UniversalFactorizationRing` / `UniversalFactorizationRing` 的定义

English:
definition UniversalFactorizationRing
  signature: : Type _
  body: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  R otimes[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
  deriving CommRing, Algebra R

local notation "𝓡" => UniversalFactorizationRing m k hn p

中文:
定义 UniversalFactorizationRing
  签名: : 类型 _
  定义体: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  R otimes[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
  deriving CommRing, Algebra R

local notation "𝓡" => UniversalFactorizationRing m k hn p

Depends on / 依赖: MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, mapEquivMonic, otimes, toAlgebra, universalFactorizationMap
-/
def UniversalFactorizationRing : Type _ :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  R otimes[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R)
  deriving CommRing, Algebra R

local notation "𝓡" => UniversalFactorizationRing m k hn p

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `UniversalFactorizationRing.fromTensor` / `UniversalFactorizationRing.fromTensor` 的定义

English:
definition UniversalFactorizationRing.fromTensor
  signature: :
  body: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  Algebra.TensorProduct.includeRight.restrictScalars _

中文:
定义 UniversalFactorizationRing.fromTensor
  签名: :
  定义体: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  Algebra.TensorProduct.includeRight.restrictScalars _

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.restrictScalars, MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, TensorProduct, includeRight, mapEquivMonic, restrictScalars, toAlgebra, universalFactorizationMap
-/
def UniversalFactorizationRing.fromTensor :
    (MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) ->ₐ[R] 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  Algebra.TensorProduct.includeRight.restrictScalars _

/--
Definition of `UniversalFactorizationRing.monicDegreeEq` / `UniversalFactorizationRing.monicDegreeEq` 的定义

English:
definition UniversalFactorizationRing.monicDegreeEq
  signature: :
  body: ⟨p.1.map (algebraMap _ _), by simp +contextual only [Polynomial.coeff_map, p.2,
    map_one, map_zero, gt_iff_lt, implies_true, and_self]⟩

中文:
定义 UniversalFactorizationRing.monicDegreeEq
  签名: :
  定义体: ⟨p.1.map (algebraMap _ _), by simp +contextual only [Polynomial.coeff_map, p.2,
    map_one, map_zero, gt_iff_lt, implies_true, and_self]⟩
-/
@[simps] def UniversalFactorizationRing.monicDegreeEq :
    MonicDegreeEq 𝓡 n :=
  ⟨p.1.map (algebraMap _ _), by simp +contextual only [Polynomial.coeff_map, p.2,
    map_one, map_zero, gt_iff_lt, implies_true, and_self]⟩

/--
lemma `UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap` / 引理 `UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap`

English:
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap
  proof: by
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  exact AlgHom.ext fun x => (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm

中文:
引理 UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap
  证明: by
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  exact AlgHom.ext fun x => (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm

Depends on / 依赖: AlgHom, AlgHom.ext, Algebra, Algebra.TensorProduct.tmul_one_eq_one_tmul, MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, TensorProduct, mapEquivMonic, tmul_one_eq_one_tmul, toAlgebra, universalFactorizationMap
-/
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    (Algebra.ofId R _).comp ((MvPolynomial.mapEquivMonic R _ n).symm p) := by
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  exact AlgHom.ext fun x => (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm

/--
lemma `UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap'` / 引理 `UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap'`

English:
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap'
  proof: by
  rw [UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap]; rw [Equiv.eq_symm_apply]
  ext1
  simp [MvPolynomial.coe_mapEquivMonic_comp, monicDegreeEq]

中文:
引理 UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap'
  证明: by
  rw [UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap]; rw [Equiv.eq_symm_apply]
  ext1
  simp [MvPolynomial.coe_mapEquivMonic_comp, monicDegreeEq]

Depends on / 依赖: Equiv.eq_symm_apply, MvPolynomial, MvPolynomial.coe_mapEquivMonic_comp, UniversalFactorizationRing, UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap, coe_mapEquivMonic_comp, eq_symm_apply, fromTensor_comp_universalFactorizationMap, monicDegreeEq
-/
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap' :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    ((MvPolynomial.mapEquivMonic _ _ n).symm (monicDegreeEq m k hn p)) := by
  rw [UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap]; rw [Equiv.eq_symm_apply]
  ext1
  simp [MvPolynomial.coe_mapEquivMonic_comp, monicDegreeEq]

/--
Definition of `UniversalFactorizationRing.factor₁` / `UniversalFactorizationRing.factor₁` 的定义

English:
definition UniversalFactorizationRing.factor₁
  signature: : MonicDegreeEq 𝓡 m
  body: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.1

中文:
定义 UniversalFactorizationRing.factor₁
  签名: : MonicDegreeEq 𝓡 m
  定义体: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.1

Depends on / 依赖: MvPolynomial, MvPolynomial.universalFactorizationMapLiftEquiv, fromTensor, fromTensor_comp_universalFactorizationMap, universalFactorizationMapLiftEquiv
-/
def UniversalFactorizationRing.factor₁ : MonicDegreeEq 𝓡 m :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.1

/--
Definition of `UniversalFactorizationRing.factor₂` / `UniversalFactorizationRing.factor₂` 的定义

English:
definition UniversalFactorizationRing.factor₂
  signature: : MonicDegreeEq 𝓡 k
  body: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.2

中文:
定义 UniversalFactorizationRing.factor₂
  签名: : MonicDegreeEq 𝓡 k
  定义体: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.2

Depends on / 依赖: MvPolynomial, MvPolynomial.universalFactorizationMapLiftEquiv, fromTensor, fromTensor_comp_universalFactorizationMap, universalFactorizationMapLiftEquiv
-/
def UniversalFactorizationRing.factor₂ : MonicDegreeEq 𝓡 k :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.2

/--
lemma `UniversalFactorizationRing.factor₁_mul_factor₂` / 引理 `UniversalFactorizationRing.factor₁_mul_factor₂`

English:
lemma UniversalFactorizationRing.factor₁_mul_factor₂
  proof: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).2

中文:
引理 UniversalFactorizationRing.factor₁_mul_factor₂
  证明: (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).2

Depends on / 依赖: MvPolynomial, MvPolynomial.universalFactorizationMapLiftEquiv, fromTensor, fromTensor_comp_universalFactorizationMap, universalFactorizationMapLiftEquiv
-/
lemma UniversalFactorizationRing.factor₁_mul_factor₂ :
    (factor₁ m k hn p).1 * (factor₂ m k hn p).1 = (monicDegreeEq m k hn p).1 :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).2

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] leftModule in
/--
Definition of `UniversalFactorizationRing.homEquiv` / `UniversalFactorizationRing.homEquiv` 的定义

English:
definition UniversalFactorizationRing.homEquiv
  signature: :
  body: ⟨((factor₁ m k hn p).map f, (factor₂ m k hn p).map f), by
    simp [← Polynomial.map_mul, factor₁_mul_factor₂ m k hn p, Polynomial.map_map]⟩
  invFun q :=
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    letI f := ((MvPolynomial.universalFactorizationMapLiftEquiv R _ n m k hn
          (p.map (algebraMap R S))).symm q)
    Algebra.TensorProduct.lift (R := MvPolynomial (Fin n) R) (S := R) (A := R)
      (B := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (C := S) (Algebra.ofId R S)
      { toRingHom := f.1.toRingHom
        commutes' r := congr($(f.2) r).trans
          (by simp [MvPolynomial.mapEquivMonic_symm_map_algebraMap]; rfl) } fun _ _ => .all _ _
  left_inv f := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    let := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    have : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r => by
      simp [Algebra.compHom_algebraMap_apply]
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R (Algebra.TensorProduct.ext ?_ ?_)
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₁, coeff_freeMonic]; rfl
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₂, coeff_freeMonic]; rfl
  right_inv q := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    simp only [UniversalFactorizationRing, MvPolynomial.mapEquivMonic, AlgHom.toRingHom_eq_coe,
      Equiv.coe_fn_symm_mk, MvPolynomial.coe_aeval_eq_eval, factor₁,
      MvPolynomial.universalFactorizationMapLiftEquiv, Equiv.coe_fn_mk, fromTensor, factor₂]
    ext <;> simp +contextual [coeff_freeMonic, apply_dite, MonicDegreeEq.coeff_of_ge]

中文:
定义 UniversalFactorizationRing.homEquiv
  签名: :
  定义体: ⟨((factor₁ m k hn p).map f, (factor₂ m k hn p).map f), by
    simp [← Polynomial.map_mul, factor₁_mul_factor₂ m k hn p, Polynomial.map_map]⟩
  invFun q :=
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    letI f := ((MvPolynomial.universalFactorizationMapLiftEquiv R _ n m k hn
          (p.map (algebraMap R S))).symm q)
    Algebra.TensorProduct.lift (R := MvPolynomial (Fin n) R) (S := R) (A := R)
      (B := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (C := S) (Algebra.ofId R S)
      { toRingHom := f.1.toRingHom
        commutes' r := congr($(f.2) r).trans
          (by simp [MvPolynomial.mapEquivMonic_symm_map_algebraMap]; rfl) } fun _ _ => .all _ _
  left_inv f := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    let := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    have : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r => by
      simp [Algebra.compHom_algebraMap_apply]
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R (Algebra.TensorProduct.ext ?_ ?_)
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₁, coeff_freeMonic]; rfl
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₂, coeff_freeMonic]; rfl
  right_inv q := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    simp only [UniversalFactorizationRing, MvPolynomial.mapEquivMonic, AlgHom.toRingHom_eq_coe,
      Equiv.coe_fn_symm_mk, MvPolynomial.coe_aeval_eq_eval, factor₁,
      MvPolynomial.universalFactorizationMapLiftEquiv, Equiv.coe_fn_mk, fromTensor, factor₂]
    ext <;> simp +contextual [coeff_freeMonic, apply_dite, MonicDegreeEq.coeff_of_ge]

Depends on / 依赖: Algebra, Algebra.compHom, IsScalarTower, IsTopologicalRing, MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, MvPolynomial.universalFactorizationMapLiftEquiv, Polynomial, Polynomial.map_map, Polynomial.map_mul, compHom, invFun, mapEquivMonic, map_map, map_mul, of_algebraMap_eq, toAlgebra, toRingHom, universalFactorizationMap
-/
def UniversalFactorizationRing.homEquiv :
    (𝓡 ->ₐ[R] S) ≃ { q : MonicDegreeEq S m × MonicDegreeEq S k //
      q.1.1 * q.2.1 = p.1.map (algebraMap R S) } where
  toFun f := ⟨((factor₁ m k hn p).map f, (factor₂ m k hn p).map f), by
    simp [← Polynomial.map_mul, factor₁_mul_factor₂ m k hn p, Polynomial.map_map]⟩
  invFun q :=
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    letI f := ((MvPolynomial.universalFactorizationMapLiftEquiv R _ n m k hn
          (p.map (algebraMap R S))).symm q)
    Algebra.TensorProduct.lift (R := MvPolynomial (Fin n) R) (S := R) (A := R)
      (B := MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R) (C := S) (Algebra.ofId R S)
      { toRingHom := f.1.toRingHom
        commutes' r := congr($(f.2) r).trans
          (by simp [MvPolynomial.mapEquivMonic_symm_map_algebraMap]; rfl) } fun _ _ => .all _ _
  left_inv f := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    let := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    have : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r => by
      simp [Algebra.compHom_algebraMap_apply]
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R (Algebra.TensorProduct.ext ?_ ?_)
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₁, coeff_freeMonic]; rfl
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₂, coeff_freeMonic]; rfl
  right_inv q := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    simp only [UniversalFactorizationRing, MvPolynomial.mapEquivMonic, AlgHom.toRingHom_eq_coe,
      Equiv.coe_fn_symm_mk, MvPolynomial.coe_aeval_eq_eval, factor₁,
      MvPolynomial.universalFactorizationMapLiftEquiv, Equiv.coe_fn_mk, fromTensor, factor₂]
    ext <;> simp +contextual [coeff_freeMonic, apply_dite, MonicDegreeEq.coeff_of_ge]

attribute [-instance] leftModule in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R 𝓡
  body: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Module.Finite _ _ := MvPolynomial.finite_universalFactorizationMap R n m k hn
  inferInstanceAs (Module.Finite R (R otimes[_] _))

中文:
实例 :
  签名: 模.有限 R 𝓡
  定义体: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Module.Finite _ _ := MvPolynomial.finite_universalFactorizationMap R n m k hn
  inferInstanceAs (Module.Finite R (R otimes[_] _))

Depends on / 依赖: Finite, Module, Module.Finite, MvPolynomial, MvPolynomial.finite_universalFactorizationMap, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, finite_universalFactorizationMap, mapEquivMonic, otimes, toAlgebra, universalFactorizationMap
-/
instance : Module.Finite R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Module.Finite _ _ := MvPolynomial.finite_universalFactorizationMap R n m k hn
  inferInstanceAs (Module.Finite R (R otimes[_] _))

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] leftModule in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.FinitePresentation R 𝓡
  body: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Algebra.FinitePresentation _ _ :=
    MvPolynomial.finitePresentation_universalFactorizationMap R n m k hn
  inferInstanceAs (Algebra.FinitePresentation R (R otimes[_] _))

中文:
实例 :
  签名: 代数.有限呈现 R 𝓡
  定义体: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Algebra.FinitePresentation _ _ :=
    MvPolynomial.finitePresentation_universalFactorizationMap R n m k hn
  inferInstanceAs (Algebra.FinitePresentation R (R otimes[_] _))

Depends on / 依赖: Algebra, Algebra.FinitePresentation, FinitePresentation, MvPolynomial, MvPolynomial.finitePresentation_universalFactorizationMap, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, finitePresentation_universalFactorizationMap, mapEquivMonic, otimes, toAlgebra, universalFactorizationMap
-/
instance : Algebra.FinitePresentation R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Algebra.FinitePresentation _ _ :=
    MvPolynomial.finitePresentation_universalFactorizationMap R n m k hn
  inferInstanceAs (Algebra.FinitePresentation R (R otimes[_] _))

/--
Definition of `UniversalFactorizationRing.presentation` / `UniversalFactorizationRing.presentation` 的定义

English:
definition UniversalFactorizationRing.presentation
  signature: :
  body: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  (MvPolynomial.universalFactorizationMapPresentation R n m k hn).baseChange _

中文:
定义 UniversalFactorizationRing.presentation
  签名: :
  定义体: letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  (MvPolynomial.universalFactorizationMapPresentation R n m k hn).baseChange _

Depends on / 依赖: MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, MvPolynomial.universalFactorizationMapPresentation, baseChange, mapEquivMonic, toAlgebra, universalFactorizationMap, universalFactorizationMapPresentation
-/
def UniversalFactorizationRing.presentation :
    Algebra.PreSubmersivePresentation R 𝓡 (Fin m oplus Fin k) (Fin n) :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  (MvPolynomial.universalFactorizationMapPresentation R n m k hn).baseChange _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `UniversalFactorizationRing.jacobian_resentation` / 引理 `UniversalFactorizationRing.jacobian_resentation`

English:
lemma UniversalFactorizationRing.jacobian_resentation
  proof: by
  cases subsingleton_or_nontrivial 𝓡
  · exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial ((MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R))
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial R
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  refine (Algebra.PreSubmersivePresentation.baseChange_jacobian _ _).trans ?_
  change fromTensor _ _ _ _ _ = _
  rw [MvPolynomial.universalFactorizationMapPresentation_jacobian]
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [← AlgHom.coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [(monic_freeMonic R k).natDegree_map]; rw [(monic_freeMonic R m).natDegree_map]; rw [MonicDegreeEq.natDegree]; rw [MonicDegreeEq.natDegree]; rw [natDegree_freeMonic]; rw [natDegree_freeMonic]
  rfl

中文:
引理 UniversalFactorizationRing.jacobian_resentation
  证明: by
  cases subsingleton_or_nontrivial 𝓡
  · exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial ((MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R))
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial R
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  refine (Algebra.PreSubmersivePresentation.baseChange_jacobian _ _).trans ?_
  change fromTensor _ _ _ _ _ = _
  rw [MvPolynomial.universalFactorizationMapPresentation_jacobian]
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [← AlgHom.coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [(monic_freeMonic R k).natDegree_map]; rw [(monic_freeMonic R m).natDegree_map]; rw [MonicDegreeEq.natDegree]; rw [MonicDegreeEq.natDegree]; rw [natDegree_freeMonic]; rw [natDegree_freeMonic]
  rfl

Depends on / 依赖: Algebra, Algebra.PreSubmersivePresentation, MvPolynomial, MvPolynomial.mapEquivMonic, MvPolynomial.universalFactorizationMap, PreSubmersivePresentation, Subsingleton, Subsingleton.elim, UniversalFactorizationRing, mapEquivMonic, otimes, subsingleton_or_nontrivial, toAlgebra, universalFactorizationMap
-/
lemma UniversalFactorizationRing.jacobian_resentation :
    (presentation m k hn p).jacobian =
      (-1) ^ n * (factor₁ m k hn p).1.resultant (factor₂ m k hn p).1 := by
  cases subsingleton_or_nontrivial 𝓡
  · exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial ((MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R))
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial R
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  refine (Algebra.PreSubmersivePresentation.baseChange_jacobian _ _).trans ?_
  change fromTensor _ _ _ _ _ = _
  rw [MvPolynomial.universalFactorizationMapPresentation_jacobian]
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [← AlgHom.coe_toRingHom]; rw [← Polynomial.resultant_map_map]; rw [Polynomial.map_map]; rw [Polynomial.map_map]; rw [(monic_freeMonic R k).natDegree_map]; rw [(monic_freeMonic R m).natDegree_map]; rw [MonicDegreeEq.natDegree]; rw [MonicDegreeEq.natDegree]; rw [natDegree_freeMonic]; rw [natDegree_freeMonic]
  rfl

open UniversalFactorizationRing in
/--
Definition of `UniversalCoprimeFactorizationRing` / `UniversalCoprimeFactorizationRing` 的定义

English:
abbreviation UniversalCoprimeFactorizationRing
  signature: : Type _
  body: Localization.Away (M := 𝓡) (presentation m k hn p).jacobian

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

中文:
缩写 UniversalCoprimeFactorizationRing
  签名: : 类型 _
  定义体: Localization.Away (M := 𝓡) (presentation m k hn p).jacobian

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

Depends on / 依赖: Localization, Localization.Away, jacobian, presentation
-/
abbrev UniversalCoprimeFactorizationRing : Type _ :=
  Localization.Away (M := 𝓡) (presentation m k hn p).jacobian

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

/--
Definition of `UniversalCoprimeFactorizationRing.factor₁` / `UniversalCoprimeFactorizationRing.factor₁` 的定义

English:
definition UniversalCoprimeFactorizationRing.factor₁
  signature: : MonicDegreeEq 𝓡' m
  body: (UniversalFactorizationRing.factor₁ m k hn p).map (algebraMap _ _)

中文:
定义 UniversalCoprimeFactorizationRing.factor₁
  签名: : MonicDegreeEq 𝓡' m
  定义体: (UniversalFactorizationRing.factor₁ m k hn p).map (algebraMap _ _)

Depends on / 依赖: UniversalFactorizationRing, UniversalFactorizationRing.factor, algebraMap
-/
def UniversalCoprimeFactorizationRing.factor₁ : MonicDegreeEq 𝓡' m :=
  (UniversalFactorizationRing.factor₁ m k hn p).map (algebraMap _ _)

/--
Definition of `UniversalCoprimeFactorizationRing.factor₂` / `UniversalCoprimeFactorizationRing.factor₂` 的定义

English:
definition UniversalCoprimeFactorizationRing.factor₂
  signature: : MonicDegreeEq 𝓡' k
  body: (UniversalFactorizationRing.factor₂ m k hn p).map (algebraMap _ _)

中文:
定义 UniversalCoprimeFactorizationRing.factor₂
  签名: : MonicDegreeEq 𝓡' k
  定义体: (UniversalFactorizationRing.factor₂ m k hn p).map (algebraMap _ _)

Depends on / 依赖: UniversalFactorizationRing, UniversalFactorizationRing.factor, algebraMap
-/
def UniversalCoprimeFactorizationRing.factor₂ : MonicDegreeEq 𝓡' k :=
  (UniversalFactorizationRing.factor₂ m k hn p).map (algebraMap _ _)

/--
lemma `UniversalCoprimeFactorizationRing.factor₁_mul_factor₂` / 引理 `UniversalCoprimeFactorizationRing.factor₁_mul_factor₂`

English:
lemma UniversalCoprimeFactorizationRing.factor₁_mul_factor₂
  proof: by
  simp [factor₁, factor₂, ← Polynomial.map_mul, UniversalFactorizationRing.factor₁_mul_factor₂,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

中文:
引理 UniversalCoprimeFactorizationRing.factor₁_mul_factor₂
  证明: by
  simp [factor₁, factor₂, ← Polynomial.map_mul, UniversalFactorizationRing.factor₁_mul_factor₂,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, Polynomial, Polynomial.map_map, Polynomial.map_mul, UniversalFactorizationRing, UniversalFactorizationRing.factor, algebraMap_eq, map_map, map_mul
-/
lemma UniversalCoprimeFactorizationRing.factor₁_mul_factor₂ :
    (factor₁ m k hn p).1 * (factor₂ m k hn p).1 = p.map (algebraMap R 𝓡') := by
  simp [factor₁, factor₂, ← Polynomial.map_mul, UniversalFactorizationRing.factor₁_mul_factor₂,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

/--
lemma `UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂` / 引理 `UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂`

English:
lemma UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂
  proof: by
  cases subsingleton_or_nontrivial 𝓡'
  · rw [Subsingleton.elim (Subtype.val _) 1]; exact isCoprime_one_left
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (factor₁ m k hn p).monic]; rw [factor₁]; rw [factor₂]; rw [MonicDegreeEq.map_coe]; rw [MonicDegreeEq.map_coe]; rw [Polynomial.resultant_map_map]; rw [(UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map]; rw [(UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map]
  refine ((IsUnit.mul_iff (x := algebraMap 𝓡 𝓡' ((-1) ^ n))).mp ?_).2
  rw [← map_mul]; rw [← UniversalFactorizationRing.jacobian_resentation m k hn p]
  exact IsLocalization.Away.algebraMap_isUnit _

中文:
引理 UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂
  证明: by
  cases subsingleton_or_nontrivial 𝓡'
  · rw [Subsingleton.elim (Subtype.val _) 1]; exact isCoprime_one_left
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (factor₁ m k hn p).monic]; rw [factor₁]; rw [factor₂]; rw [MonicDegreeEq.map_coe]; rw [MonicDegreeEq.map_coe]; rw [Polynomial.resultant_map_map]; rw [(UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map]; rw [(UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map]
  refine ((IsUnit.mul_iff (x := algebraMap 𝓡 𝓡' ((-1) ^ n))).mp ?_).2
  rw [← map_mul]; rw [← UniversalFactorizationRing.jacobian_resentation m k hn p]
  exact IsLocalization.Away.algebraMap_isUnit _

Depends on / 依赖: IsUnit, IsUnit.mul_iff, MonicDegreeEq, MonicDegreeEq.map_coe, Polynomial, Polynomial.isUnit_resultant_iff_isCoprime, Polynomial.resultant_map_map, Subsingleton, Subsingleton.elim, Subtype, Subtype.val, UniversalFactorizationRing, UniversalFactorizationRing.factor, algebraMap, isCoprime_one_left, isUnit_resultant_iff_isCoprime, map_coe, monic.natDegree_map, mul_iff, natDegree_map
-/
lemma UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂ :
    IsCoprime (factor₁ m k hn p).1 (factor₂ m k hn p).1 := by
  cases subsingleton_or_nontrivial 𝓡'
  · rw [Subsingleton.elim (Subtype.val _) 1]; exact isCoprime_one_left
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (factor₁ m k hn p).monic]; rw [factor₁]; rw [factor₂]; rw [MonicDegreeEq.map_coe]; rw [MonicDegreeEq.map_coe]; rw [Polynomial.resultant_map_map]; rw [(UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map]; rw [(UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map]
  refine ((IsUnit.mul_iff (x := algebraMap 𝓡 𝓡' ((-1) ^ n))).mp ?_).2
  rw [← map_mul]; rw [← UniversalFactorizationRing.jacobian_resentation m k hn p]
  exact IsLocalization.Away.algebraMap_isUnit _

open UniversalFactorizationRing in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.Etale R 𝓡'
  body: by
  let Δ : 𝓡 := (presentation m k hn p).jacobian
  have hΔ : IsUnit (algebraMap 𝓡 (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let P : Algebra.SubmersivePresentation R (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ) (presentation m k hn p),
      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away Δ) :=
    ⟨_, _, _, inferInstance, P, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, P]
      simp [Algebra.Presentation.dimension, hn]⟩
  infer_instance

中文:
实例 :
  签名: 代数.平展 R 𝓡'
  定义体: by
  let Δ : 𝓡 := (presentation m k hn p).jacobian
  have hΔ : IsUnit (algebraMap 𝓡 (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let P : Algebra.SubmersivePresentation R (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ) (presentation m k hn p),
      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away Δ) :=
    ⟨_, _, _, inferInstance, P, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, P]
      simp [Algebra.Presentation.dimension, hn]⟩
  infer_instance

Depends on / 依赖: Algebra, Algebra.IsStandardSmoothOfRelativeDimension, Algebra.SubmersivePresentation, Algebra.smul_def, IsLocalization, IsLocalization.Away.algebraMap_isUnit, IsStandardSmoothOfRelativeDimension, IsUnit, Localization, Localization.Away, SubmersivePresentation, algebraMap, algebraMap_isUnit, isUnit_map_iff, jacobian, jacobian_isUnit, localizationAway, presentation, smul_def, toPreSubmersivePresentation
-/
instance : Algebra.Etale R 𝓡' := by
  let Δ : 𝓡 := (presentation m k hn p).jacobian
  have hΔ : IsUnit (algebraMap 𝓡 (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let P : Algebra.SubmersivePresentation R (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ) (presentation m k hn p),
      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away Δ) :=
    ⟨_, _, _, inferInstance, P, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, P]
      simp [Algebra.Presentation.dimension, hn]⟩
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `UniversalCoprimeFactorizationRing.homEquiv` / `UniversalCoprimeFactorizationRing.homEquiv` 的定义

English:
definition UniversalCoprimeFactorizationRing.homEquiv
  signature: :
  body: letI q := UniversalFactorizationRing.homEquiv S m k hn p (f.comp (IsScalarTower.toAlgHom _ _ _))
    ⟨q.1, q.2, by
      convert! (isCoprime_factor₁_factor₂ m k hn p).map (Polynomial.mapRingHom f.toRingHom) <;>
        simp [q, UniversalFactorizationRing.homEquiv,
          AlgHom.comp_toRingHom, ← Polynomial.map_map] <;> rfl⟩
  invFun q := by
    letI f := (UniversalFactorizationRing.homEquiv S m k hn p).symm ⟨q.1, q.2.1⟩
    apply IsLocalization.Away.liftAlgHom (f := f)
      (UniversalFactorizationRing.presentation m k hn p).jacobian
    nontriviality S
    rw [← AlgHom.coe_toRingHom]; rw [UniversalFactorizationRing.jacobian_resentation]; rw [map_mul]; rw [← Polynomial.resultant_map_map]; rw [IsUnit.mul_iff]
    refine ⟨by cases n <;> simp, ?_⟩
    rw [← (UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map f.toRingHom]; rw [← (UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map f.toRingHom]; rw [AlgHom.toRingHom_eq_coe]; rw [Polynomial.isUnit_resultant_iff_isCoprime
        ((UniversalFactorizationRing.factor₁ m k hn p).monic.map _)]
    change IsCoprime (UniversalFactorizationRing.homEquiv S m k hn p f).1.1.1
      (UniversalFactorizationRing.homEquiv S m k hn p f).1.2.1
    simpa [f] using q.2.2
  left_inv f := by
    apply IsLocalization.algHom_ext
      (.powers (UniversalFactorizationRing.presentation m k hn p).jacobian)
    ext; simp [Algebra.algHom]
  right_inv q := by
    apply Subtype.ext
    convert! congr($((UniversalFactorizationRing.homEquiv S m k hn p).apply_symm_apply
      ⟨_, q.2.1⟩).1) using 1
    dsimp
    congr 2
    ext
    simp

中文:
定义 UniversalCoprimeFactorizationRing.homEquiv
  签名: :
  定义体: letI q := UniversalFactorizationRing.homEquiv S m k hn p (f.comp (IsScalarTower.toAlgHom _ _ _))
    ⟨q.1, q.2, by
      convert! (isCoprime_factor₁_factor₂ m k hn p).map (Polynomial.mapRingHom f.toRingHom) <;>
        simp [q, UniversalFactorizationRing.homEquiv,
          AlgHom.comp_toRingHom, ← Polynomial.map_map] <;> rfl⟩
  invFun q := by
    letI f := (UniversalFactorizationRing.homEquiv S m k hn p).symm ⟨q.1, q.2.1⟩
    apply IsLocalization.Away.liftAlgHom (f := f)
      (UniversalFactorizationRing.presentation m k hn p).jacobian
    nontriviality S
    rw [← AlgHom.coe_toRingHom]; rw [UniversalFactorizationRing.jacobian_resentation]; rw [map_mul]; rw [← Polynomial.resultant_map_map]; rw [IsUnit.mul_iff]
    refine ⟨by cases n <;> simp, ?_⟩
    rw [← (UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map f.toRingHom]; rw [← (UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map f.toRingHom]; rw [AlgHom.toRingHom_eq_coe]; rw [Polynomial.isUnit_resultant_iff_isCoprime
        ((UniversalFactorizationRing.factor₁ m k hn p).monic.map _)]
    change IsCoprime (UniversalFactorizationRing.homEquiv S m k hn p f).1.1.1
      (UniversalFactorizationRing.homEquiv S m k hn p f).1.2.1
    simpa [f] using q.2.2
  left_inv f := by
    apply IsLocalization.algHom_ext
      (.powers (UniversalFactorizationRing.presentation m k hn p).jacobian)
    ext; simp [Algebra.algHom]
  right_inv q := by
    apply Subtype.ext
    convert! congr($((UniversalFactorizationRing.homEquiv S m k hn p).apply_symm_apply
      ⟨_, q.2.1⟩).1) using 1
    dsimp
    congr 2
    ext
    simp

Depends on / 依赖: AlgHom, AlgHom.comp_toRingHom, IsLocalization, IsLocalization.Away.liftAlgHom, IsScalarTower, IsScalarTower.toAlgHom, Polynomial, Polynomial.mapRingHom, Polynomial.map_map, UniversalFactorizationRing, UniversalFactorizationRing.homEquiv, UniversalFactorizationRing.presentation, comp_toRingHom, convert, f.comp, f.toRingHom, homEquiv, invFun, jacobian, liftAlgHom
-/
def UniversalCoprimeFactorizationRing.homEquiv :
    (𝓡' ->ₐ[R] S) ≃ { q : MonicDegreeEq S m × MonicDegreeEq S k //
      q.1.1 * q.2.1 = p.1.map (algebraMap R S) ∧ IsCoprime q.1.1 q.2.1 } where
  toFun f :=
    letI q := UniversalFactorizationRing.homEquiv S m k hn p (f.comp (IsScalarTower.toAlgHom _ _ _))
    ⟨q.1, q.2, by
      convert! (isCoprime_factor₁_factor₂ m k hn p).map (Polynomial.mapRingHom f.toRingHom) <;>
        simp [q, UniversalFactorizationRing.homEquiv,
          AlgHom.comp_toRingHom, ← Polynomial.map_map] <;> rfl⟩
  invFun q := by
    letI f := (UniversalFactorizationRing.homEquiv S m k hn p).symm ⟨q.1, q.2.1⟩
    apply IsLocalization.Away.liftAlgHom (f := f)
      (UniversalFactorizationRing.presentation m k hn p).jacobian
    nontriviality S
    rw [← AlgHom.coe_toRingHom]; rw [UniversalFactorizationRing.jacobian_resentation]; rw [map_mul]; rw [← Polynomial.resultant_map_map]; rw [IsUnit.mul_iff]
    refine ⟨by cases n <;> simp, ?_⟩
    rw [← (UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map f.toRingHom]; rw [← (UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map f.toRingHom]; rw [AlgHom.toRingHom_eq_coe]; rw [Polynomial.isUnit_resultant_iff_isCoprime
        ((UniversalFactorizationRing.factor₁ m k hn p).monic.map _)]
    change IsCoprime (UniversalFactorizationRing.homEquiv S m k hn p f).1.1.1
      (UniversalFactorizationRing.homEquiv S m k hn p f).1.2.1
    simpa [f] using q.2.2
  left_inv f := by
    apply IsLocalization.algHom_ext
      (.powers (UniversalFactorizationRing.presentation m k hn p).jacobian)
    ext; simp [Algebra.algHom]
  right_inv q := by
    apply Subtype.ext
    convert! congr($((UniversalFactorizationRing.homEquiv S m k hn p).apply_symm_apply
      ⟨_, q.2.1⟩).1) using 1
    dsimp
    congr 2
    ext
    simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `UniversalCoprimeFactorizationRing.homEquiv_comp_fst` / 引理 `UniversalCoprimeFactorizationRing.homEquiv_comp_fst`

English:
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_fst
  statement: {T : Type*} [CommRing T] [Algebra R T]
  proof: by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

中文:
引理 UniversalCoprimeFactorizationRing.homEquiv_comp_fst
  结论: {T : 类型} [交换环 T] [代数 R T]
  证明: by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

Depends on / 依赖: Polynomial, Polynomial.map_map, UniversalFactorizationRing, UniversalFactorizationRing.homEquiv, homEquiv, map_map
-/
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_fst {T : Type*} [CommRing T] [Algebra R T]
    (f : 𝓡' ->ₐ[R] S) (g : S ->ₐ[R] T) :
    (homEquiv T m k hn p (g.comp f)).1.1 = (homEquiv S m k hn p f).1.1.map g := by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `UniversalCoprimeFactorizationRing.homEquiv_comp_snd` / 引理 `UniversalCoprimeFactorizationRing.homEquiv_comp_snd`

English:
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_snd
  statement: {T : Type*} [CommRing T] [Algebra R T]
  proof: by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

中文:
引理 UniversalCoprimeFactorizationRing.homEquiv_comp_snd
  结论: {T : 类型} [交换环 T] [代数 R T]
  证明: by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

Depends on / 依赖: Polynomial, Polynomial.map_map, UniversalFactorizationRing, UniversalFactorizationRing.homEquiv, homEquiv, map_map
-/
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_snd {T : Type*} [CommRing T] [Algebra R T]
    (f : 𝓡' ->ₐ[R] S) (g : S ->ₐ[R] T) :
    (homEquiv T m k hn p (g.comp f)).1.2 = (homEquiv S m k hn p f).1.2.map g := by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective` / 引理 `UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective`

English:
lemma UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective
  proof: by
  let φ : 𝓡' ->ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField ->ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField ->ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x => φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x => e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

中文:
引理 UniversalCoprimeFactorizationRing.存在_liesOver_residueFieldMap_bijective
  证明: by
  let φ : 𝓡' ->ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField ->ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField ->ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x => φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x => e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, H.symm, Ideal.ResidueField.lift, Ideal.ker_algebraMap_residueField, Ideal.under, IsPrime, IsUnit, IsUnit.mem_submonoid_iff, LiesOver, P.ResidueF, P.ResidueField, Q.IsPrime, Q.LiesOver, Q.ResidueField, ResidueF, ResidueField, RingHom, RingHom.comap_ker, RingHom.ker
-/
lemma UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective
    (P : Ideal R) [P.IsPrime]
    (f : MonicDegreeEq P.ResidueField m) (g : MonicDegreeEq P.ResidueField k)
    (H : p.1.map (algebraMap R _) = f.1 * g.1) (Hpq : IsCoprime f.1 g.1) :
    exists (Q : Ideal 𝓡') (_ : Q.IsPrime) (_ : Q.LiesOver P),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₁ m k hn p).map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₂ m k hn p).map (algebraMap _ _) := by
  let φ : 𝓡' ->ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField ->ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField ->ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x => φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x => e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

open UniversalCoprimeFactorizationRing in
/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists an etale algebra `R'` of `R` and a prime `Q` of `R'` lying over `P`,
such that `κ(P) = κ(Q)` and that the factorization lifts to `R'`. -/
@[stacks 00UH]
/--
lemma `_root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.` / 引理 `_root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.`

English:
lemma _root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
  proof: by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

中文:
引理 _root_.代数.存在_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
  证明: by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

Depends on / 依赖: exists_liesOver_residueFieldMap_bijective, f.natDegree, g.natDegree, hf.natDegree_mul, hp.natDegree_map, natDegree, natDegree_map, natDegree_mul
-/
lemma _root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
    {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (p : R[X])
    (f g : P.ResidueField[X]) (hp : p.Monic) (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R _) = f * g) (Hpq : IsCoprime f g) :
    exists (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (Q : Ideal R') (_ : Q.IsPrime) (_ : Q.LiesOver P) (f' g' : R'[X]),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f'.Monic ∧ g'.Monic ∧ p.map (algebraMap R R') = f' * g' ∧ IsCoprime f' g' ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      f'.map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      g'.map (algebraMap _ _) := by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

end Polynomial
