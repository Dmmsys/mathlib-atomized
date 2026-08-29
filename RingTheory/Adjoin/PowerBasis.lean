/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Power basis for `R[x]`

This file defines the canonical power basis on `R[x]`,
where `x` is an integral element over `R`.
-/

@[expose] public section

open Module Polynomial PowerBasis

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

namespace Algebra

/--
Definition of `adjoin.powerBasisAux` / `adjoin.powerBasisAux` 的定义

English:
definition adjoin.powerBasisAux
  signature: {x : S} (hx : IsIntegral K x)
  body: by
  have hST : Function.Injective (algebraMap (K[(x : S)]) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : K[(x : S)]) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert! hx
  apply Basis.mk (v := fun i : Fin _ => ⟨x, subset_adjoin (

中文:
定义 adjoin.powerBasisAux
  签名: {x : S} (hx : 是整 K x)
  定义体: by
  have hST : Function.Injective (algebraMap (K[(x : S)]) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : K[(x : S)]) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert! hx
  apply Basis.mk (v := fun i : Fin _ => ⟨x, subset_adjoin (

Depends on / 依赖: Basis.mk, Function, Function.Injective, Injective, IsIntegral, LinearIndependent, Set.mem_singleton, Subtype, Subtype.coe_injective, algebraMap, algebraMap_eq, coe_injective, convert, isIntegral_algebraMap_iff, linearIndependent_pow, mem_singleton, mem_span_p, minpoly, minpoly.algebraMap_eq, self_mem_adjoin_singleton
-/
noncomputable def adjoin.powerBasisAux {x : S} (hx : IsIntegral K x) :
    Basis (Fin (minpoly K x).natDegree) K (K[(x : S)]) := by
  have hST : Function.Injective (algebraMap (K[(x : S)]) S) := Subtype.coe_injective
  have hx' :
    IsIntegral K (⟨x, subset_adjoin (Set.mem_singleton x)⟩ : K[(x : S)]) := by
    apply (isIntegral_algebraMap_iff hST).mp
    convert! hx
  apply Basis.mk (v := fun i : Fin _ => ⟨x, subset_adjoin (Set.mem_singleton x)⟩ ^ (i : Nat))
  · have : LinearIndependent K _ := linearIndependent_pow
      (⟨x, self_mem_adjoin_singleton _ _⟩ : K[x])
    rwa [← minpoly.algebraMap_eq hST] at this
  · rintro ⟨y, hy⟩ _
    have := hx'.mem_span_pow (y := ⟨y, hy⟩)
    rw [← minpoly.algebraMap_eq hST] at this
    apply this
    rw [adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := (aeval x).mem_range.mp hy
    use f
    ext
    exact aeval_algebraMap_apply S (⟨x, _⟩ : K[x]) _

set_option backward.isDefEq.respectTransparency.types false in
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. See `Algebra.adjoin.powerBasis'` for
a version over a more general base ring. -/
@[simps gen dim]
/--
Definition of `adjoin.powerBasis` / `adjoin.powerBasis` 的定义

English:
definition adjoin.powerBasis
  signature: {x : S} (hx : IsIntegral K x)
  body: ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  basis := adjoin.powerBasisAux hx
  basis_eq_pow i := by rw [adjoin.powerBasisAux, Basis.mk_apply]

中文:
定义 adjoin.powerBasis
  签名: {x : S} (hx : 是整 K x)
  定义体: ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  basis := adjoin.powerBasisAux hx
  basis_eq_pow i := by rw [adjoin.powerBasisAux, Basis.mk_apply]
-/
noncomputable def adjoin.powerBasis {x : S} (hx : IsIntegral K x) :
    PowerBasis K K[(x : S)] where
  gen := ⟨x, subset_adjoin (Set.mem_singleton x)⟩
  dim := (minpoly K x).natDegree
  basis := adjoin.powerBasisAux hx
  basis_eq_pow i := by rw [adjoin.powerBasisAux, Basis.mk_apply]

/--
Definition of `_root_.PowerBasis.ofAdjoinEqTop` / `_root_.PowerBasis.ofAdjoinEqTop` 的定义

English:
definition _root_.PowerBasis.ofAdjoinEqTop
  signature: {x : S} (hx : IsIntegral K x)
  body: (adjoin.powerBasis hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

中文:
定义 _root_.PowerBasis.ofAdjoinEqTop
  签名: {x : S} (hx : 是整 K x)
  定义体: (adjoin.powerBasis hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

Depends on / 依赖: Subalgebra, Subalgebra.equivOfEq, Subalgebra.topEquiv, adjoin, adjoin.powerBasis, equivOfEq, powerBasis, topEquiv
-/
noncomputable def _root_.PowerBasis.ofAdjoinEqTop {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) : PowerBasis K S :=
  (adjoin.powerBasis hx).map ((Subalgebra.equivOfEq _ _ hx').trans Subalgebra.topEquiv)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `_root_.PowerBasis.ofAdjoinEqTop_gen` / 定理 `_root_.PowerBasis.ofAdjoinEqTop_gen`

English:
theorem _root_.PowerBasis.ofAdjoinEqTop_gen
  statement: {x : S} (hx : IsIntegral K x)
  proof: rfl

中文:
定理 _root_.PowerBasis.ofAdjoinEqTop_gen
  结论: {x : S} (hx : 是整 K x)
  证明: rfl
-/
theorem _root_.PowerBasis.ofAdjoinEqTop_gen {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) : (PowerBasis.ofAdjoinEqTop hx hx').gen = x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `_root_.PowerBasis.ofAdjoinEqTop_dim` / 定理 `_root_.PowerBasis.ofAdjoinEqTop_dim`

English:
theorem _root_.PowerBasis.ofAdjoinEqTop_dim
  statement: {x : S} (hx : IsIntegral K x)
  proof: rfl

中文:
定理 _root_.PowerBasis.ofAdjoinEqTop_dim
  结论: {x : S} (hx : 是整 K x)
  证明: rfl
-/
theorem _root_.PowerBasis.ofAdjoinEqTop_dim {x : S} (hx : IsIntegral K x)
    (hx' : K[x] = ⊤) :
    (PowerBasis.ofAdjoinEqTop hx hx').dim = (minpoly K x).natDegree := rfl

end Algebra

open Algebra

section IsIntegral

namespace PowerBasis

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R S] [Algebra R K] [IsScalarTower R K S]
variable {A : Type*} [CommRing A] [Algebra R A] [Algebra S A]
variable [IsScalarTower R S A] {B : PowerBasis S A}

/--
theorem `repr_gen_pow_isIntegral` / 定理 `repr_gen_pow_isIntegral`

English:
theorem repr_gen_pow_isIntegral
  statement: (hB : IsIntegral R B.gen)
  proof: by
  intro i
  nontriviality S
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen]; rw [← modByMonic_add_div (X ^ n) (minpoly R B.gen)]
    simp [Q]
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.natDegree < 

中文:
定理 repr_gen_pow_is整数egral
  结论: (hB : 是整 R B.gen)
  证明: by
  intro i
  nontriviality S
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen]; rw [← modByMonic_add_div (X ^ n) (minpoly R B.gen)]
    simp [Q]
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.natDegree < 

Depends on / 依赖: B.dim, B.gen, B.natDegree_minpoly, Nontrivial, Nontrivial.of_polynomial_ne, Q.natDegree, aeval_X_pow, degree_modByMonic_lt, isIntegral_zero, minpoly, minpoly.monic, modByMonic_add_div, natDegree, natDegree_lt_natDegree_iff, natDegree_map, natDegree_minpoly, nontriviality, of_polynomial_ne
-/
theorem repr_gen_pow_isIntegral (hB : IsIntegral R B.gen)
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : Nat) :
    forall i, IsIntegral R (B.basis.repr (B.gen ^ n) i) := by
  intro i
  nontriviality S
  let Q := X ^ n %ₘ minpoly R B.gen
  have : B.gen ^ n = aeval B.gen Q := by
    rw [← @aeval_X_pow R _ _ _ _ B.gen]; rw [← modByMonic_add_div (X ^ n) (minpoly R B.gen)]
    simp [Q]
  by_cases hQ : Q = 0
  · simp [this, hQ, isIntegral_zero]
  have hlt : Q.natDegree < B.dim := by
    rw [← B.natDegree_minpoly]; rw [hmin]; rw [(minpoly.monic hB).natDegree_map]; rw [natDegree_lt_natDegree_iff hQ]
    let : Nontrivial R := Nontrivial.of_polynomial_ne hQ
    exact degree_modByMonic_lt _ (minpoly.monic hB)
  rw [this]; rw [aeval_eq_sum_range' hlt]
  simp only [map_sum, Finset.sum_apply']
  refine IsIntegral.sum _ fun j hj => ?_
  replace hj := Finset.mem_range.1 hj
  rw [← Fin.val_mk hj]; rw [← B.basis_eq_pow]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S A]; rw [←
    Algebra.smul_def]; rw [map_smul]
  simp only [algebraMap_smul, Finsupp.coe_smul, Pi.smul_apply, B.basis.repr_self_apply]
  by_cases hij : (⟨j, hj⟩ : Fin _) = i
  · simp only [hij, if_true]
    rw [Algebra.smul_def]; rw [mul_one]
    exact isIntegral_algebraMap
  · simp [hij, isIntegral_zero]

/--
theorem `repr_mul_isIntegral` / 定理 `repr_mul_isIntegral`

English:
theorem repr_mul_isIntegral
  statement: (hB : IsIntegral R B.gen) {x y : A}
  proof: by
  intro i
  rw [← B.basis.sum_repr x]; rw [← B.basis.sum_repr y]; rw [Finset.sum_mul_sum]; rw [← Finset.sum_product']; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun I _ => ?_
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smulₛₗ, RingHom.id_apply,
    Finsupp

中文:
定理 repr_mul_is整数egral
  结论: (hB : 是整 R B.gen) {x y : A}
  证明: by
  intro i
  rw [← B.basis.sum_repr x]; rw [← B.basis.sum_repr y]; rw [Finset.sum_mul_sum]; rw [← Finset.sum_product']; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun I _ => ?_
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smulₛₗ, RingHom.id_apply,
    Finsupp

Depends on / 依赖: Algebra, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, B.basis.sum_repr, Finset, Finset.sum_apply, Finset.sum_mul_sum, Finset.sum_product, Finsupp, Finsupp.coe_smul, IsIntegral, IsIntegral.sum, Pi.smul_apply, RingHom, RingHom.id_apply, coe_basis, coe_smul, id_apply, map_sum, mul_smul_comm
-/
theorem repr_mul_isIntegral (hB : IsIntegral R B.gen) {x y : A}
    (hx : forall i, IsIntegral R (B.basis.repr x i)) (hy : forall i, IsIntegral R (B.basis.repr y i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) :
    forall i, IsIntegral R (B.basis.repr (x * y) i) := by
  intro i
  rw [← B.basis.sum_repr x]; rw [← B.basis.sum_repr y]; rw [Finset.sum_mul_sum]; rw [← Finset.sum_product']; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun I _ => ?_
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smulₛₗ, RingHom.id_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  refine (hy _).mul ((hx _).mul ?_)
  simp only [coe_basis, ← pow_add]
  exact repr_gen_pow_isIntegral hB hmin _ _

/--
theorem `repr_pow_isIntegral` / 定理 `repr_pow_isIntegral`

English:
theorem repr_pow_isIntegral
  statement: (hB : IsIntegral R B.gen) {x : A}
  proof: by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n => _ -> forall (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n ?_ fun n hn => ?_
  · intro _ i
  

中文:
定理 repr_pow_is整数egral
  结论: (hB : 是整 R B.gen) {x : A}
  证明: by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n => _ -> forall (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n ?_ fun n hn => ?_
  · intro _ i
  

Depends on / 依赖: Nat.case_strong_induction_on, Subsingleton, Subsingleton.elim, case_strong_induction_on, isIntegral_zero, nontriviality, revert
-/
theorem repr_pow_isIntegral (hB : IsIntegral R B.gen) {x : A}
    (hx : forall i, IsIntegral R (B.basis.repr x i))
    (hmin : minpoly S B.gen = (minpoly R B.gen).map (algebraMap R S)) (n : Nat) :
    forall i, IsIntegral R (B.basis.repr (x ^ n) i) := by
  nontriviality A using Subsingleton.elim (x ^ n) 0, isIntegral_zero
  revert hx
  refine Nat.case_strong_induction_on
    -- Porting note: had to hint what to induct on
    (p := fun n => _ -> forall (i : Fin B.dim), IsIntegral R (B.basis.repr (x ^ n) i))
    n ?_ fun n hn => ?_
  · intro _ i
    rw [pow_zero]; rw [← pow_zero B.gen]; rw [← Fin.val_mk B.dim_pos]; rw [← B.basis_eq_pow]; rw [B.basis.repr_self_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · intro hx
    rw [pow_succ]
    exact repr_mul_isIntegral hB (fun _ => hn _ le_rfl (fun _ => hx _) _) hx hmin

/--
theorem `toMatrix_isIntegral` / 定理 `toMatrix_isIntegral`

English:
theorem toMatrix_isIntegral
  statement: {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
  proof: by
  intro i j
  rw [B.basis.toMatrix_apply]; rw [B'.coe_basis]
  refine repr_pow_isIntegral hB (fun i => ?_) hmin _ _
  rw [← h]; rw [aeval_eq_sum_range]; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun n _ => ?_
  rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R K S];

中文:
定理 toMatrix_is整数egral
  结论: {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
  证明: by
  intro i j
  rw [B.basis.toMatrix_apply]; rw [B'.coe_basis]
  refine repr_pow_isIntegral hB (fun i => ?_) hmin _ _
  rw [← h]; rw [aeval_eq_sum_range]; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun n _ => ?_
  rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R K S];

Depends on / 依赖: Algebra, Algebra.smul_def, B.basis.toMatrix_apply, Finset, Finset.sum_apply, IsIntegral, IsIntegral.sum, IsScalarTower, IsScalarTower.algebraMap_apply, aeval_eq_sum_range, algebraMap_apply, algebraMap_smul, coe_basis, map_smul, map_sum, repr_gen_pow_isIntegral, repr_pow_isIntegral, smul_def, sum_apply, toMatrix_apply
-/
theorem toMatrix_isIntegral {B B' : PowerBasis K S} {P : R[X]} (h : aeval B.gen P = B'.gen)
    (hB : IsIntegral R B.gen) (hmin : minpoly K B.gen = (minpoly R B.gen).map (algebraMap R K)) :
    forall i j, IsIntegral R (B.basis.toMatrix B'.basis i j) := by
  intro i j
  rw [B.basis.toMatrix_apply]; rw [B'.coe_basis]
  refine repr_pow_isIntegral hB (fun i => ?_) hmin _ _
  rw [← h]; rw [aeval_eq_sum_range]; rw [map_sum]; rw [Finset.sum_apply']
  refine IsIntegral.sum _ fun n _ => ?_
  rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R K S]; rw [← Algebra.smul_def]; rw [map_smul]; rw [algebraMap_smul]
  exact (repr_gen_pow_isIntegral hB hmin _ _).smul _

end PowerBasis

end IsIntegral
