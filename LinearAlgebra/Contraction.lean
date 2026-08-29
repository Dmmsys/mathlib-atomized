/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

@[expose] public section

variable {ι : Type*} (R M N P Q : Type*)

-- Enable extensionality of maps out of the tensor product.
-- High priority so it takes precedence over `LinearMap.ext`.
attribute [local ext high] TensorProduct.ext

section Contraction

open TensorProduct LinearMap Matrix Module

open TensorProduct

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable (b : Basis ι R M)

/--
Definition of `contractLeft` / `contractLeft` 的定义

English:
definition contractLeft
  signature: : Module.Dual R M otimes[R] M ->ₗ[R] R
  body: (uncurry _ _ _ _).toFun LinearMap.id

中文:
定义 contractLeft
  签名: : 模.对偶 R M otimes[R] M ->ₗ[R] R
  定义体: (uncurry _ _ _ _).toFun LinearMap.id

Depends on / 依赖: LinearMap, LinearMap.id, uncurry
-/
def contractLeft : Module.Dual R M otimes[R] M ->ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/--
Definition of `contractRight` / `contractRight` 的定义

English:
definition contractRight
  signature: : M otimes[R] Module.Dual R M ->ₗ[R] R
  body: (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

中文:
定义 contractRight
  签名: : M otimes[R] 模.对偶 R M ->ₗ[R] R
  定义体: (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

Depends on / 依赖: LinearMap, LinearMap.flip, LinearMap.id, uncurry
-/
def contractRight : M otimes[R] Module.Dual R M ->ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/--
Definition of `dualTensorHom` / `dualTensorHom` 的定义

English:
definition dualTensorHom
  signature: : Module.Dual R M otimes[R] N ->ₗ[R] M ->ₗ[R] N
  body: let M' := Module.Dual R M
  (uncurry (.id R) M' N (M ->ₗ[R] N) : _ -> M' otimes N ->ₗ[R] M ->ₗ[R] N) LinearMap.smulRightₗ

中文:
定义 dualTensorHom
  签名: : 模.对偶 R M otimes[R] N ->ₗ[R] M ->ₗ[R] N
  定义体: let M' := Module.Dual R M
  (uncurry (.id R) M' N (M ->ₗ[R] N) : _ -> M' otimes N ->ₗ[R] M ->ₗ[R] N) LinearMap.smulRightₗ

Depends on / 依赖: LinearMap, LinearMap.smulRight, Module, Module.Dual, otimes, uncurry
-/
def dualTensorHom : Module.Dual R M otimes[R] N ->ₗ[R] M ->ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry (.id R) M' N (M ->ₗ[R] N) : _ -> M' otimes N ->ₗ[R] M ->ₗ[R] N) LinearMap.smulRightₗ

variable {R M N P Q}

@[simp]
/--
theorem `contractLeft_apply` / 定理 `contractLeft_apply`

English:
theorem contractLeft_apply
  given: (f : Module.Dual R M) (m : M)
  statement: contractLeft R M (f otimesₜ m) = f m
  proof: rfl

@[simp]

中文:
定理 contractLeft_apply
  条件: (f : 模.对偶 R M) (m : M)
  结论: contractLeft R M (f otimesₜ m) = f m
  证明: rfl

@[simp]
-/
theorem contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f otimesₜ m) = f m :=
  rfl

@[simp]
/--
theorem `contractRight_apply` / 定理 `contractRight_apply`

English:
theorem contractRight_apply
  given: (f : Module.Dual R M) (m : M)
  statement: contractRight R M (m otimesₜ f) = f m
  proof: rfl

@[simp]

中文:
定理 contractRight_apply
  条件: (f : 模.对偶 R M) (m : M)
  结论: contractRight R M (m otimesₜ f) = f m
  证明: rfl

@[simp]
-/
theorem contractRight_apply (f : Module.Dual R M) (m : M) : contractRight R M (m otimesₜ f) = f m :=
  rfl

@[simp]
/--
theorem `dualTensorHom_apply` / 定理 `dualTensorHom_apply`

English:
theorem dualTensorHom_apply
  given: (f : Module.Dual R M) (m : M) (n : N)
  proof: rfl

中文:
定理 dualTensorHom_apply
  条件: (f : 模.对偶 R M) (m : M) (n : N)
  证明: rfl
-/
theorem dualTensorHom_apply (f : Module.Dual R M) (m : M) (n : N) :
    dualTensorHom R M N (f otimesₜ n) m = f m • n :=
  rfl

/--
theorem `dualTensorHom_comp_lTensor` / 定理 `dualTensorHom_comp_lTensor`

English:
theorem dualTensorHom_comp_lTensor
  given: (f : N ->ₗ[R] P)
  proof: by
  ext; simp

中文:
定理 dualTensorHom_comp_lTensor
  条件: (f : N ->ₗ[R] P)
  证明: by
  ext; simp
-/
theorem dualTensorHom_comp_lTensor (f : N ->ₗ[R] P) :
    dualTensorHom R M P ∘ₗ f.lTensor _ = f.compRight R ∘ₗ dualTensorHom R M N := by
  ext; simp

/--
theorem `dualTensorHom_comp_rTensor_dualMap` / 定理 `dualTensorHom_comp_rTensor_dualMap`

English:
theorem dualTensorHom_comp_rTensor_dualMap
  given: (f : M ->ₗ[R] N)
  proof: by
  ext; simp

@[simp]

中文:
定理 dualTensorHom_comp_rTensor_dualMap
  条件: (f : M ->ₗ[R] N)
  证明: by
  ext; simp

@[simp]
-/
theorem dualTensorHom_comp_rTensor_dualMap (f : M ->ₗ[R] N) :
    dualTensorHom R M P ∘ₗ f.dualMap.rTensor _ = f.lcomp R P ∘ₗ dualTensorHom R N P := by
  ext; simp

@[simp]
/--
theorem `transpose_dualTensorHom` / 定理 `transpose_dualTensorHom`

English:
theorem transpose_dualTensorHom
  given: (f : Module.Dual R M) (m : M)
  proof: by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    map_smulₛₗ, RingHom.id_apply, smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _

@[simp]

中文:
定理 transpose_dualTensorHom
  条件: (f : 模.对偶 R M) (m : M)
  证明: by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    map_smulₛₗ, RingHom.id_apply, smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _

@[simp]

Depends on / 依赖: dualTensorHom
-/
theorem transpose_dualTensorHom (f : Module.Dual R M) (m : M) :
    Dual.transpose (R := R) (dualTensorHom R M M (f otimesₜ m)) =
    dualTensorHom R _ _ (Dual.eval R M m otimesₜ f) := by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    map_smulₛₗ, RingHom.id_apply, smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _

@[simp]
/--
theorem `dualTensorHom_prodMap_zero` / 定理 `dualTensorHom_prodMap_zero`

English:
theorem dualTensorHom_prodMap_zero
  given: (f : Module.Dual R M) (p : P)
  proof: by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

@[simp]

中文:
定理 dualTensorHom_prodMap_zero
  条件: (f : 模.对偶 R M) (p : P)
  证明: by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.zero_apply, Prod.smul_mk, coe_comp, coe_inl, comp_apply, dualTensorHom_apply, fst_apply, prodMap_apply, smul_mk, smul_zero, zero_apply
-/
theorem dualTensorHom_prodMap_zero (f : Module.Dual R M) (p : P) :
    ((dualTensorHom R M P) (f otimesₜ[R] p)).prodMap (0 : N ->ₗ[R] Q) =
      dualTensorHom R (M × N) (P × Q) ((f ∘ₗ fst R M N) otimesₜ inl R P Q p) := by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

@[simp]
/--
theorem `zero_prodMap_dualTensorHom` / 定理 `zero_prodMap_dualTensorHom`

English:
theorem zero_prodMap_dualTensorHom
  given: (g : Module.Dual R N) (q : Q)
  proof: by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

中文:
定理 zero_prodMap_dualTensorHom
  条件: (g : 模.对偶 R N) (q : Q)
  证明: by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.zero_apply, Prod.smul_mk, coe_comp, coe_inr, comp_apply, dualTensorHom_apply, prodMap_apply, smul_mk, smul_zero, snd_apply, zero_apply
-/
theorem zero_prodMap_dualTensorHom (g : Module.Dual R N) (q : Q) :
    (0 : M ->ₗ[R] P).prodMap ((dualTensorHom R N Q) (g otimesₜ[R] q)) =
      dualTensorHom R (M × N) (P × Q) ((g ∘ₗ snd R M N) otimesₜ inr R P Q q) := by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

attribute [-ext] AlgebraTensorModule.curry_injective in
/--
theorem `map_dualTensorHom` / 定理 `map_dualTensorHom`

English:
theorem map_dualTensorHom
  given: (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q)
  proof: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply,
    ← smul_tmul_smul]

中文:
定理 map_dualTensorHom
  条件: (f : 模.对偶 R M) (p : P) (g : 模.对偶 R N) (q : Q)
  证明: by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply,
    ← smul_tmul_smul]

Depends on / 依赖: dualDistrib_apply, dualTensorHom_apply, map_tmul, mk_apply, smul_tmul_smul
-/
theorem map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q) :
    TensorProduct.map (dualTensorHom R M P (f otimesₜ[R] p)) (dualTensorHom R N Q (g otimesₜ[R] q)) =
      dualTensorHom R (M otimes[R] N) (P otimes[R] Q) (dualDistrib R M N (f otimesₜ g) otimesₜ[R] (p otimesₜ[R] q)) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply,
    ← smul_tmul_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `comp_dualTensorHom` / 定理 `comp_dualTensorHom`

English:
theorem comp_dualTensorHom
  given: (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P)
  proof: by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

中文:
定理 comp_dualTensorHom
  条件: (f : 模.对偶 R M) (n : N) (g : 模.对偶 R N) (p : P)
  证明: by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.smul_apply, coe_comp, comp_apply, dualTensorHom_apply, map_smul, smul_apply, smul_comm
-/
theorem comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P) :
    dualTensorHom R N P (g otimesₜ[R] p) ∘ₗ dualTensorHom R M N (f otimesₜ[R] n) =
      g n • dualTensorHom R M P (f otimesₜ p) := by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toMatrix_dualTensorHom` / 定理 `toMatrix_dualTensorHom`

English:
theorem toMatrix_dualTensorHom
  statement: {m : Type*} {n : Type*} [Fintype m] [Finite n] [DecidableEq m]
  proof: by
  ext i' j'
  by_cases hij : i = i' ∧ j = j'
  · simp [LinearMap.toMatrix_apply, hij]
  · rw [and_iff_not_or_not, Classical.not_not] at hij
    rcases hij with hij | hij <;> simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]

中文:
定理 toMatrix_dualTensorHom
  结论: {m : 类型} {n : 类型} [有限类型 m] [有限 n] [DecidableEq m]
  证明: by
  ext i' j'
  by_cases hij : i = i' ∧ j = j'
  · simp [LinearMap.toMatrix_apply, hij]
  · rw [and_iff_not_or_not, Classical.not_not] at hij
    rcases hij with hij | hij <;> simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]

Depends on / 依赖: Classical, Classical.not_not, Finsupp, Finsupp.single_eq_pi_single, LinearMap, LinearMap.toMatrix_apply, and_iff_not_or_not, not_not, single_eq_pi_single, toMatrix_apply
-/
theorem toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Finite n] [DecidableEq m]
    [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.coord j otimesₜ bN i)) = single i j 1 := by
  ext i' j'
  by_cases hij : i = i' ∧ j = j'
  · simp [LinearMap.toMatrix_apply, hij]
  · rw [and_iff_not_or_not, Classical.not_not] at hij
    rcases hij with hij | hij <;> simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]

section

variable (h : 1 in (dualTensorHom R M M).range)
include h

/--
theorem `finite_projective_of_one_mem_range_dualTensorHom` / 定理 `finite_projective_of_one_mem_range_dualTensorHom`

English:
theorem finite_projective_of_one_mem_range_dualTensorHom
  proof: by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s -> R) ->ₗ[R] M := Fintype.linearCombination R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = 1 := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩

中文:
定理 finite_projective_of_one_mem_range_dualTensorHom
  证明: by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s -> R) ->ₗ[R] M := Fintype.linearCombination R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = 1 := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩
-/
private theorem finite_projective_of_one_mem_range_dualTensorHom :
    Module.Finite R M ∧ Projective R M := by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s -> R) ->ₗ[R] M := Fintype.linearCombination R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = 1 := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩

/--
theorem `Module.Finite.of_one_mem_range_dualTensorHom` / 定理 `Module.Finite.of_one_mem_range_dualTensorHom`

English:
theorem Module.Finite.of_one_mem_range_dualTensorHom
  statement: Module.Finite R M
  proof: (finite_projective_of_one_mem_range_dualTensorHom h).1

中文:
定理 模.有限.of_one_mem_range_dualTensorHom
  结论: 模.有限 R M
  证明: (finite_projective_of_one_mem_range_dualTensorHom h).1

Depends on / 依赖: finite_projective_of_one_mem_range_dualTensorHom
-/
theorem Module.Finite.of_one_mem_range_dualTensorHom : Module.Finite R M :=
  (finite_projective_of_one_mem_range_dualTensorHom h).1

/--
theorem `Module.Projective.of_one_mem_range_dualTensorHom` / 定理 `Module.Projective.of_one_mem_range_dualTensorHom`

English:
theorem Module.Projective.of_one_mem_range_dualTensorHom
  statement: Module.Projective R M
  proof: (finite_projective_of_one_mem_range_dualTensorHom h).2

中文:
定理 模.投射.of_one_mem_range_dualTensorHom
  结论: 模.投射 R M
  证明: (finite_projective_of_one_mem_range_dualTensorHom h).2

Depends on / 依赖: finite_projective_of_one_mem_range_dualTensorHom
-/
theorem Module.Projective.of_one_mem_range_dualTensorHom : Module.Projective R M :=
  (finite_projective_of_one_mem_range_dualTensorHom h).2

end

section Fintype

variable [DecidableEq ι] [Fintype ι]

attribute [-ext] AlgebraTensorModule.curry_injective in
-- We manually create simp-lemmas because `@[simps]` generates a malformed lemma
/--
Definition of `dualTensorHomEquivOfBasis` / `dualTensorHomEquivOfBasis` 的定义

English:
definition dualTensorHomEquivOfBasis
  signature: : Module.Dual R M otimes[R] N ≃ₗ[R] M ->ₗ[R] N
  body: LinearEquiv.ofLinearMap (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

中文:
定义 dualTensorHomEquivOfBasis
  签名: : 模.对偶 R M otimes[R] N ≃ₗ[R] M ->ₗ[R] N
  定义体: LinearEquiv.ofLinearMap (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

Depends on / 依赖: Basis.coe_dualBasis, Basis.coord_apply, Fintype, Fintype.sum_apply, Function, Function.comp_apply, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.apply, TensorProduct, TensorProduct.mk, _root_, _root_.id, _root_.map_sum, b.dualBasis, b.sum_repr, coe_comp, coe_dualBasis, coe_sum
-/
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M otimes[R] N ≃ₗ[R] M ->ₗ[R] N :=
  LinearEquiv.ofLinearMap (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])

/--
theorem `coe_dualTensorHomEquivOfBasis` / 定理 `coe_dualTensorHomEquivOfBasis`

English:
theorem coe_dualTensorHomEquivOfBasis
  proof: rfl

@[simp]

中文:
定理 coe_dualTensorHomEquivOfBasis
  证明: rfl

@[simp]

Depends on / 依赖: dualTensorHom
-/
theorem coe_dualTensorHomEquivOfBasis :
    ⇑(dualTensorHomEquivOfBasis (N := N) b) = dualTensorHom R M N := rfl

@[simp]
/--
theorem `dualTensorHomEquivOfBasis_apply` / 定理 `dualTensorHomEquivOfBasis_apply`

English:
theorem dualTensorHomEquivOfBasis_apply
  given: (x : Module.Dual R M otimes[R] N)
  proof: rfl

@[simp]

中文:
定理 dualTensorHomEquivOfBasis_apply
  条件: (x : 模.对偶 R M otimes[R] N)
  证明: rfl

@[simp]
-/
theorem dualTensorHomEquivOfBasis_apply (x : Module.Dual R M otimes[R] N) :
    dualTensorHomEquivOfBasis b x = dualTensorHom R M N x :=
  rfl

@[simp]
/--
theorem `dualTensorHomEquivOfBasis_toLinearMap` / 定理 `dualTensorHomEquivOfBasis_toLinearMap`

English:
theorem dualTensorHomEquivOfBasis_toLinearMap
  proof: rfl

@[simp]

中文:
定理 dualTensorHomEquivOfBasis_toLinearMap
  证明: rfl

@[simp]
-/
theorem dualTensorHomEquivOfBasis_toLinearMap :
    (dualTensorHomEquivOfBasis b).toLinearMap = dualTensorHom R M N :=
  rfl

@[simp]
/--
theorem `dualTensorHomEquivOfBasis_symm_cancel_left` / 定理 `dualTensorHomEquivOfBasis_symm_cancel_left`

English:
theorem dualTensorHomEquivOfBasis_symm_cancel_left
  given: (x : Module.Dual R M otimes[R] N)
  proof: by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.symm_apply_apply dualTensorHomEquivOfBasis (N := N) b]

@[simp]

中文:
定理 dualTensorHomEquivOfBasis_symm_cancel_left
  条件: (x : 模.对偶 R M otimes[R] N)
  证明: by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.symm_apply_apply dualTensorHomEquivOfBasis (N := N) b]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, dualTensorHomEquivOfBasis, dualTensorHomEquivOfBasis_apply, symm_apply_apply
-/
theorem dualTensorHomEquivOfBasis_symm_cancel_left (x : Module.Dual R M otimes[R] N) :
    (dualTensorHomEquivOfBasis b).symm (dualTensorHom R M N x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.symm_apply_apply dualTensorHomEquivOfBasis (N := N) b]

@[simp]
/--
theorem `dualTensorHomEquivOfBasis_symm_cancel_right` / 定理 `dualTensorHomEquivOfBasis_symm_cancel_right`

English:
theorem dualTensorHomEquivOfBasis_symm_cancel_right
  given: (x : M ->ₗ[R] N)
  proof: by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.apply_symm_apply]

中文:
定理 dualTensorHomEquivOfBasis_symm_cancel_right
  条件: (x : M ->ₗ[R] N)
  证明: by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.apply_symm_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, dualTensorHomEquivOfBasis_apply
-/
theorem dualTensorHomEquivOfBasis_symm_cancel_right (x : M ->ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquivOfBasis b).symm x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b]; rw [LinearEquiv.apply_symm_apply]

end Fintype

/--
theorem `dualTensorHom_bijective` / 定理 `dualTensorHom_bijective`

English:
theorem dualTensorHom_bijective
  given: [Module.Finite R M] [Projective R M]
  proof: by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp]; rw [← dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp (injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_)
    simp [← rTensor_comp, dualMap_comp_dualMap g f, eq]
  · refine .of_comp (g := g.dualMap.rTensor N) ?_
    rw [← coe_comp]; rw [dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (surjective_of_comp_eq_id (f.lcomp R N) _ ?_).comp (EquivLike.surjective _)
    ext φ; exact congr(φ ($eq _))

中文:
定理 dualTensorHom_bijective
  条件: [模.有限 R M] [投射 R M]
  证明: by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp]; rw [← dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp (injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_)
    simp [← rTensor_comp, dualMap_comp_dualMap g f, eq]
  · refine .of_comp (g := g.dualMap.rTensor N) ?_
    rw [← coe_comp]; rw [dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (surjective_of_comp_eq_id (f.lcomp R N) _ ?_).comp (EquivLike.surjective _)
    ext φ; exact congr(φ ($eq _))

Depends on / 依赖: EquivLike, EquivLike.injective, Finite, Finite.exists_comp_eq_id_of_projective, Pi.basisFun, basisFun, coe_comp, coe_dualTensorHomEquivOfBasis, dualMap, dualMap_comp_dualMap, dualTensorHom_comp_rTensor_dualMa, dualTensorHom_comp_rTensor_dualMap, exists_comp_eq_id_of_projective, f.lcomp, g.dualMap, g.dualMap.rTensor, injective, injective_of_comp_eq_id, of_comp, rTensor
-/
theorem dualTensorHom_bijective [Module.Finite R M] [Projective R M] :
    Function.Bijective (dualTensorHom R M N) := by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp]; rw [← dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp (injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_)
    simp [← rTensor_comp, dualMap_comp_dualMap g f, eq]
  · refine .of_comp (g := g.dualMap.rTensor N) ?_
    rw [← coe_comp]; rw [dualTensorHom_comp_rTensor_dualMap]; rw [coe_comp]; rw [← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (surjective_of_comp_eq_id (f.lcomp R N) _ ?_).comp (EquivLike.surjective _)
    ext φ; exact congr(φ ($eq _))

/--
theorem `dualTensorHom_self_right` / 定理 `dualTensorHom_self_right`

English:
theorem dualTensorHom_self_right
  statement: dualTensorHom R M R = TensorProduct.rid R (Dual R M)
  proof: by
  ext; simp

中文:
定理 dualTensorHom_self_right
  结论: dualTensorHom R M R = 张量积.rid R (对偶 R M)
  证明: by
  ext; simp
-/
theorem dualTensorHom_self_right : dualTensorHom R M R = TensorProduct.rid R (Dual R M) := by
  ext; simp

/--
theorem `dualTensorHom_self_right_bijective` / 定理 `dualTensorHom_self_right_bijective`

English:
theorem dualTensorHom_self_right_bijective
  statement: Function.Bijective (dualTensorHom R M R)
  proof: by
  simpa only [dualTensorHom_self_right] using! LinearEquiv.bijective _

中文:
定理 dualTensorHom_self_right_bijective
  结论: 函数.双射 (dualTensorHom R M R)
  证明: by
  simpa only [dualTensorHom_self_right] using! LinearEquiv.bijective _
-/
private theorem dualTensorHom_self_right_bijective : Function.Bijective (dualTensorHom R M R) := by
  simpa only [dualTensorHom_self_right] using! LinearEquiv.bijective _

/--
theorem `dualTensorHom_finsupp` / 定理 `dualTensorHom_finsupp`

English:
theorem dualTensorHom_finsupp
  given: [DecidableEq ι]
  proof: by
  ext; simp [Finsupp.single_apply]; aesop

中文:
定理 dualTensorHom_finsupp
  条件: [DecidableEq ι]
  证明: by
  ext; simp [Finsupp.single_apply]; aesop

Depends on / 依赖: Finsupp, Finsupp.single_apply, single_apply
-/
theorem dualTensorHom_finsupp [DecidableEq ι] :
    dualTensorHom R M (ι ->₀ N) = .finsuppLinearMap R ∘ₗ
      Finsupp.mapRange.linearMap (dualTensorHom R M N) ∘ₗ (finsuppRight R R _ N ι).toLinearMap := by
  ext; simp [Finsupp.single_apply]; aesop

/--
theorem `dualTensorHom_finsupp_bijective` / 定理 `dualTensorHom_finsupp_bijective`

English:
theorem dualTensorHom_finsupp_bijective
  statement: (fin : Finite ι ∨ Module.Finite R M)
  proof: by
  classical rw [dualTensorHom_finsupp, coe_comp]
  refine .comp ?_ ((Finsupp.mapRange_bijective _ (map_zero _) h).comp (LinearEquiv.bijective _))
  cases fin
  · apply finsuppLinearMap_bijective_of_finite
  · apply finsuppLinearMap_bijective_of_moduleFinite

中文:
定理 dualTensorHom_finsupp_bijective
  结论: (fin : 有限 ι ∨ 模.有限 R M)
  证明: by
  classical rw [dualTensorHom_finsupp, coe_comp]
  refine .comp ?_ ((Finsupp.mapRange_bijective _ (map_zero _) h).comp (LinearEquiv.bijective _))
  cases fin
  · apply finsuppLinearMap_bijective_of_finite
  · apply finsuppLinearMap_bijective_of_moduleFinite

Depends on / 依赖: Finsupp, Finsupp.mapRange_bijective, LinearEquiv, LinearEquiv.bijective, bijective, classical, coe_comp, dualTensorHom_finsupp, finsuppLinearMap_bijective_of_finite, finsuppLinearMap_bijective_of_moduleFinite, mapRange_bijective, map_zero
-/
theorem dualTensorHom_finsupp_bijective (fin : Finite ι ∨ Module.Finite R M)
    (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι ->₀ N)) := by
  classical rw [dualTensorHom_finsupp, coe_comp]
  refine .comp ?_ ((Finsupp.mapRange_bijective _ (map_zero _) h).comp (LinearEquiv.bijective _))
  cases fin
  · apply finsuppLinearMap_bijective_of_finite
  · apply finsuppLinearMap_bijective_of_moduleFinite

/--
theorem `dualTensorHom_bijective_of_comp_eq_id_right` / 定理 `dualTensorHom_bijective_of_comp_eq_id_right`

English:
theorem dualTensorHom_bijective_of_comp_eq_id_right
  statement: (f : N ->ₗ[R] P) (g : P ->ₗ[R] N)
  proof: .of_comp (f := f.compRight R) by
    rw [← coe_comp]; rw [← dualTensorHom_comp_lTensor]
    refine h.1.comp (injective_of_comp_eq_id _ (g.lTensor _) ?_)
    rw [← lTensor_comp]; rw [comp_eq_id]; rw [lTensor_id]
right := .of_comp (g := g.lTensor _) by
    rw [← coe_comp]; rw [dualTensorHom_comp_lTensor]; rw [coe_comp]
    refine (surjective_of_comp_eq_id (f.compRight R) _ ?_).comp h.2
    ext; exact congr($comp_eq_id _)

中文:
定理 dualTensorHom_bijective_of_comp_eq_id_right
  结论: (f : N ->ₗ[R] P) (g : P ->ₗ[R] N)
  证明: .of_comp (f := f.compRight R) by
    rw [← coe_comp]; rw [← dualTensorHom_comp_lTensor]
    refine h.1.comp (injective_of_comp_eq_id _ (g.lTensor _) ?_)
    rw [← lTensor_comp]; rw [comp_eq_id]; rw [lTensor_id]
right := .of_comp (g := g.lTensor _) by
    rw [← coe_comp]; rw [dualTensorHom_comp_lTensor]; rw [coe_comp]
    refine (surjective_of_comp_eq_id (f.compRight R) _ ?_).comp h.2
    ext; exact congr($comp_eq_id _)

Depends on / 依赖: coe_comp, compRight, comp_eq_id, dualTensorHom_comp_lTensor, f.compRight, g.lTensor, injective_of_comp_eq_id, lTensor, lTensor_comp, lTensor_id, of_comp, surjective_of_comp_eq_id
-/
theorem dualTensorHom_bijective_of_comp_eq_id_right (f : N ->ₗ[R] P) (g : P ->ₗ[R] N)
    (comp_eq_id : g ∘ₗ f = .id) (h : Function.Bijective (dualTensorHom R M P)) :
    Function.Bijective (dualTensorHom R M N) where
left := .of_comp (f := f.compRight R) by
    rw [← coe_comp]; rw [← dualTensorHom_comp_lTensor]
    refine h.1.comp (injective_of_comp_eq_id _ (g.lTensor _) ?_)
    rw [← lTensor_comp]; rw [comp_eq_id]; rw [lTensor_id]
right := .of_comp (g := g.lTensor _) by
    rw [← coe_comp]; rw [dualTensorHom_comp_lTensor]; rw [coe_comp]
    refine (surjective_of_comp_eq_id (f.compRight R) _ ?_).comp h.2
    ext; exact congr($comp_eq_id _)

/--
theorem `dualTensorHom_fun_bijective` / 定理 `dualTensorHom_fun_bijective`

English:
theorem dualTensorHom_fun_bijective
  given: [Finite ι] (h : Function.Bijective (dualTensorHom R M N))
  proof: dualTensorHom_bijective_of_comp_eq_id_right
    (Finsupp.linearEquivFunOnFinite R N ι).symm
    (Finsupp.linearEquivFunOnFinite ..).toLinearMap (by ext; simp)
    (dualTensorHom_finsupp_bijective (.inl ‹_›) h)

中文:
定理 dualTensorHom_fun_bijective
  条件: [有限 ι] (h : 函数.双射 (dualTensorHom R M N))
  证明: dualTensorHom_bijective_of_comp_eq_id_right
    (Finsupp.linearEquivFunOnFinite R N ι).symm
    (Finsupp.linearEquivFunOnFinite ..).toLinearMap (by ext; simp)
    (dualTensorHom_finsupp_bijective (.inl ‹_›) h)

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, dualTensorHom_bijective_of_comp_eq_id_right, dualTensorHom_finsupp_bijective, linearEquivFunOnFinite, toLinearMap
-/
theorem dualTensorHom_fun_bijective [Finite ι] (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι -> N)) :=
  dualTensorHom_bijective_of_comp_eq_id_right
    (Finsupp.linearEquivFunOnFinite R N ι).symm
    (Finsupp.linearEquivFunOnFinite ..).toLinearMap (by ext; simp)
    (dualTensorHom_finsupp_bijective (.inl ‹_›) h)

/--
theorem `dualTensorHom_bijective_of_finite_projective_right` / 定理 `dualTensorHom_bijective_of_finite_projective_right`

English:
theorem dualTensorHom_bijective_of_finite_projective_right
  given: [Module.Finite R N] [Projective R N]
  proof: have ⟨_n, f, g, _, _, eq⟩ := Finite.exists_comp_eq_id_of_projective R N
dualTensorHom_bijective_of_comp_eq_id_right g f eq
    dualTensorHom_fun_bijective dualTensorHom_self_right_bijective

中文:
定理 dualTensorHom_bijective_of_finite_projective_right
  条件: [模.有限 R N] [投射 R N]
  证明: have ⟨_n, f, g, _, _, eq⟩ := Finite.exists_comp_eq_id_of_projective R N
dualTensorHom_bijective_of_comp_eq_id_right g f eq
    dualTensorHom_fun_bijective dualTensorHom_self_right_bijective

Depends on / 依赖: Finite, Finite.exists_comp_eq_id_of_projective, dualTensorHom_bijective_of_comp_eq_id_right, dualTensorHom_fun_bijective, dualTensorHom_self_right_bijective, exists_comp_eq_id_of_projective
-/
theorem dualTensorHom_bijective_of_finite_projective_right [Module.Finite R N] [Projective R N] :
    Function.Bijective (dualTensorHom R M N) :=
  have ⟨_n, f, g, _, _, eq⟩ := Finite.exists_comp_eq_id_of_projective R N
dualTensorHom_bijective_of_comp_eq_id_right g f eq
    dualTensorHom_fun_bijective dualTensorHom_self_right_bijective

/--
theorem `dualTensorHom_bijective_of_finite_left_projective_right` / 定理 `dualTensorHom_bijective_of_finite_left_projective_right`

English:
theorem dualTensorHom_bijective_of_finite_left_projective_right
  statement: [Module.Finite R M]
  proof: have ⟨f, eq⟩ := projective_def'.mp ‹Projective R N›
dualTensorHom_bijective_of_comp_eq_id_right _ _ eq
    dualTensorHom_finsupp_bijective (.inr ‹_›) dualTensorHom_self_right_bijective

中文:
定理 dualTensorHom_bijective_of_finite_left_projective_right
  结论: [模.有限 R M]
  证明: have ⟨f, eq⟩ := projective_def'.mp ‹Projective R N›
dualTensorHom_bijective_of_comp_eq_id_right _ _ eq
    dualTensorHom_finsupp_bijective (.inr ‹_›) dualTensorHom_self_right_bijective

Depends on / 依赖: Projective, dualTensorHom_bijective_of_comp_eq_id_right, dualTensorHom_finsupp_bijective, dualTensorHom_self_right_bijective, projective_def
-/
theorem dualTensorHom_bijective_of_finite_left_projective_right [Module.Finite R M]
    [Projective R N] : Function.Bijective (dualTensorHom R M N) :=
  have ⟨f, eq⟩ := projective_def'.mp ‹Projective R N›
dualTensorHom_bijective_of_comp_eq_id_right _ _ eq
    dualTensorHom_finsupp_bijective (.inr ‹_›) dualTensorHom_self_right_bijective

variable (R M N) in
/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
/--
Definition of `dualTensorHomEquiv` / `dualTensorHomEquiv` 的定义

English:
definition dualTensorHomEquiv
  signature: [Module.Finite R M] [Projective R M]
  body: .ofBijective _ (dualTensorHom_bijective ..)

中文:
定义 dualTensorHomEquiv
  签名: [模.有限 R M] [投射 R M]
  定义体: .ofBijective _ (dualTensorHom_bijective ..)

Depends on / 依赖: dualTensorHom_bijective, ofBijective
-/
noncomputable def dualTensorHomEquiv [Module.Finite R M] [Projective R M] :
    Module.Dual R M otimes[R] N ≃ₗ[R] M ->ₗ[R] N :=
  .ofBijective _ (dualTensorHom_bijective ..)

/--
theorem `dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis` / 定理 `dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis`

English:
theorem dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis
  proof: Module.Finite.of_basis b; have := Module.Free.of_basis b
    dualTensorHomEquiv R M N = dualTensorHomEquivOfBasis b := by
  ext; rfl

中文:
定理 dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis
  证明: Module.Finite.of_basis b; have := Module.Free.of_basis b
    dualTensorHomEquiv R M N = dualTensorHomEquivOfBasis b := by
  ext; rfl

Depends on / 依赖: Finite, Module, Module.Finite.of_basis, Module.Free.of_basis, of_basis
-/
theorem dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis
    (b : Basis ι R M) [DecidableEq ι] [Fintype ι] :
    have := Module.Finite.of_basis b; have := Module.Free.of_basis b
    dualTensorHomEquiv R M N = dualTensorHomEquivOfBasis b := by
  ext; rfl

end CommSemiring

end Contraction

section HomTensorHom

open TensorProduct

open Module TensorProduct LinearMap

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Projective R M] [Module.Finite R M]

/--
Definition of `lTensorHomEquivHomLTensor` / `lTensorHomEquivHomLTensor` 的定义

English:
definition lTensorHomEquivHomLTensor
  signature: : P otimes[R] (M ->ₗ[R] Q) ≃ₗ[R] M ->ₗ[R] P otimes[R] Q
  body: congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

中文:
定义 lTensorHomEquivHomLTensor
  签名: : P otimes[R] (M ->ₗ[R] Q) ≃ₗ[R] M ->ₗ[R] P otimes[R] Q
  定义体: congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, TensorProduct, TensorProduct.leftComm, dualTensorHomEquiv, leftComm
-/
noncomputable def lTensorHomEquivHomLTensor : P otimes[R] (M ->ₗ[R] Q) ≃ₗ[R] M ->ₗ[R] P otimes[R] Q :=
  congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

/--
Definition of `rTensorHomEquivHomRTensor` / `rTensorHomEquivHomRTensor` 的定义

English:
definition rTensorHomEquivHomRTensor
  signature: : (M ->ₗ[R] P) otimes[R] Q ≃ₗ[R] M ->ₗ[R] P otimes[R] Q
  body: congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

中文:
定义 rTensorHomEquivHomRTensor
  签名: : (M ->ₗ[R] P) otimes[R] Q ≃ₗ[R] M ->ₗ[R] P otimes[R] Q
  定义体: congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, TensorProduct, TensorProduct.assoc, dualTensorHomEquiv
-/
noncomputable def rTensorHomEquivHomRTensor : (M ->ₗ[R] P) otimes[R] Q ≃ₗ[R] M ->ₗ[R] P otimes[R] Q :=
  congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/--
theorem `lTensorHomEquivHomLTensor_toLinearMap` / 定理 `lTensorHomEquivHomLTensor_toLinearMap`

English:
theorem lTensorHomEquivHomLTensor_toLinearMap
  proof: by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp [e, lTensorHomEquivHomLTensor]

中文:
定理 lTensorHomEquivHomLTensor_toLinearMap
  证明: by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp [e, lTensorHomEquivHomLTensor]

Depends on / 依赖: Function, Function.Surjective, LinearEquiv, LinearEquiv.refl, Surjective, cancel_right, dualTensorHomEquiv, e.surjective, e.toLinearMap, lTensorHomEquivHomLTensor, surjective, toLinearMap
-/
theorem lTensorHomEquivHomLTensor_toLinearMap :
    (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor (.id R) M P Q := by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp [e, lTensorHomEquivHomLTensor]

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/--
theorem `rTensorHomEquivHomRTensor_toLinearMap` / 定理 `rTensorHomEquivHomRTensor_toLinearMap`

English:
theorem rTensorHomEquivHomRTensor_toLinearMap
  proof: by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

中文:
定理 rTensorHomEquivHomRTensor_toLinearMap
  证明: by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

Depends on / 依赖: Function, Function.Surjective, LinearEquiv, LinearEquiv.refl, Surjective, cancel_right, dualTensorHomEquiv, e.surjective, e.toLinearMap, rTensorHomEquivHomRTensor, smul_tmul, surjective, toLinearMap
-/
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor (.id R) M P Q := by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

variable {R M N P Q}

@[simp]
/--
theorem `lTensorHomEquivHomLTensor_apply` / 定理 `lTensorHomEquivHomLTensor_apply`

English:
theorem lTensorHomEquivHomLTensor_apply
  given: (x : P otimes[R] (M ->ₗ[R] Q))
  proof: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [lTensorHomEquivHomLTensor_toLinearMap]

@[simp]

中文:
定理 lTensorHomEquivHomLTensor_apply
  条件: (x : P otimes[R] (M ->ₗ[R] Q))
  证明: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [lTensorHomEquivHomLTensor_toLinearMap]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap
-/
theorem lTensorHomEquivHomLTensor_apply (x : P otimes[R] (M ->ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap]; rw [lTensorHomEquivHomLTensor_toLinearMap]

@[simp]
/--
theorem `rTensorHomEquivHomRTensor_apply` / 定理 `rTensorHomEquivHomRTensor_apply`

English:
theorem rTensorHomEquivHomRTensor_apply
  given: (x : (M ->ₗ[R] P) otimes[R] Q)
  proof: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [rTensorHomEquivHomRTensor_toLinearMap]

中文:
定理 rTensorHomEquivHomRTensor_apply
  条件: (x : (M ->ₗ[R] P) otimes[R] Q)
  证明: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [rTensorHomEquivHomRTensor_toLinearMap]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap
-/
theorem rTensorHomEquivHomRTensor_apply (x : (M ->ₗ[R] P) otimes[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap]; rw [rTensorHomEquivHomRTensor_toLinearMap]

variable (R M N P Q) [Projective R N] [Module.Finite R N]

/--
Definition of `homTensorHomEquiv` / `homTensorHomEquiv` 的定义

English:
definition homTensorHomEquiv
  signature: : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q) ≃ₗ[R] M otimes[R] N ->ₗ[R] P otimes[R] Q
  body: rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv _ M N _

中文:
定义 homTensorHomEquiv
  签名: : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q) ≃ₗ[R] M otimes[R] N ->ₗ[R] P otimes[R] Q
  定义体: rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv _ M N _

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, arrowCongr, lTensorHomEquivHomLTensor, lift.equiv, rTensorHomEquivHomRTensor
-/
noncomputable def homTensorHomEquiv : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q) ≃ₗ[R] M otimes[R] N ->ₗ[R] P otimes[R] Q :=
  rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv _ M N _

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/--
theorem `homTensorHomEquiv_toLinearMap` / 定理 `homTensorHomEquiv_toLinearMap`

English:
theorem homTensorHomEquiv_toLinearMap
  proof: by
  ext m n
  simp only [homTensorHomEquiv, compr₂ₛₗ_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]

中文:
定理 homTensorHomEquiv_toLinearMap
  证明: by
  ext m n
  simp only [homTensorHomEquiv, compr₂ₛₗ_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]

Depends on / 依赖: LinearEquiv, LinearEquiv.arrowCongr_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.refl_apply, LinearEquiv.refl_symm, LinearEquiv.trans_apply, arrowCongr_apply, coe_toLinearMap, equiv_apply, homTensorHomEquiv, homTensorHomMap_apply, lTensorHomEquivHomLTensor_apply, lTensorHomToHomLTensor_apply, lift.equiv_apply, map_tmul, mk_apply, rTensorHomEquivHomRTensor_apply, rTensorHomToHomRTensor_apply, refl_apply, refl_symm
-/
theorem homTensorHomEquiv_toLinearMap :
    (homTensorHomEquiv R M N P Q).toLinearMap = homTensorHomMap (.id R) M N P Q := by
  ext m n
  simp only [homTensorHomEquiv, compr₂ₛₗ_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]

variable {R M N P Q}

@[simp]
/--
theorem `homTensorHomEquiv_apply` / 定理 `homTensorHomEquiv_apply`

English:
theorem homTensorHomEquiv_apply
  given: (x : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q))
  proof: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [homTensorHomEquiv_toLinearMap]

中文:
定理 homTensorHomEquiv_apply
  条件: (x : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q))
  证明: by
  rw [← LinearEquiv.coe_toLinearMap]; rw [homTensorHomEquiv_toLinearMap]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, coe_toLinearMap, homTensorHomEquiv_toLinearMap
-/
theorem homTensorHomEquiv_apply (x : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q)) :
    homTensorHomEquiv R M N P Q x = homTensorHomMap (.id R) M N P Q x := by
  rw [← LinearEquiv.coe_toLinearMap]; rw [homTensorHomEquiv_toLinearMap]

end CommSemiring

end HomTensorHom

namespace TensorProduct

open LinearMap Module

variable {R M N : Type*} {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

attribute [local ext] TensorProduct.ext

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/--
Definition of `dualDistribInvOfBasis` / `dualDistribInvOfBasis` 的定义

English:
definition dualDistribInvOfBasis
  signature: (b : Basis ι R M) (c : Basis κ R N)
  body: ∑ i, ∑ j,
    (ringLmapEquivSelf R Nat _).symm (b.dualBasis i otimesₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[simp]

中文:
定义 dualDistribInvOfBasis
  签名: (b : 基 ι R M) (c : 基 κ R N)
  定义体: ∑ i, ∑ j,
    (ringLmapEquivSelf R Nat _).symm (b.dualBasis i otimesₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[simp]

Depends on / 依赖: b.dualBasis, c.dualBasis, dualBasis, lcurry, ringLmapEquivSelf
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M otimes[R] N) ->ₗ[R] Dual R M otimes[R] Dual R N :=
  ∑ i, ∑ j,
    (ringLmapEquivSelf R Nat _).symm (b.dualBasis i otimesₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[simp]
/--
theorem `dualDistribInvOfBasis_apply` / 定理 `dualDistribInvOfBasis_apply`

English:
theorem dualDistribInvOfBasis_apply
  given: (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M otimes[R] N))
  proof: by
  simp [dualDistribInvOfBasis]

中文:
定理 dualDistribInvOfBasis_apply
  条件: (b : 基 ι R M) (c : 基 κ R N) (f : 对偶 R (M otimes[R] N))
  证明: by
  simp [dualDistribInvOfBasis]

Depends on / 依赖: dualDistribInvOfBasis
-/
theorem dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M otimes[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i otimesₜ c j) • b.dualBasis i otimesₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]

/--
theorem `dualDistrib_dualDistribInvOfBasis_left_inverse` / 定理 `dualDistrib_dualDistribInvOfBasis_left_inverse`

English:
theorem dualDistrib_dualDistribInvOfBasis_left_inverse
  given: (b : Basis ι R M) (c : Basis κ R N)
  proof: by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

中文:
定理 dualDistrib_dualDistribInvOfBasis_left_inverse
  条件: (b : 基 ι R M) (c : 基 κ R N)
  证明: by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

Depends on / 依赖: Basis.coe_dualBasis, Basis.coord_apply, Basis.repr_self, Basis.tensorProduct_apply, Basis.tensorProduct_repr_tmul_apply, Finset, Finset.sum_apply, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_sum, _root_, _root_.map_sum, b.tensorProduct, coe_coe, coe_comp, coe_dualBasis, coe_sum
-/
theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

/--
theorem `dualDistrib_dualDistribInvOfBasis_right_inverse` / 定理 `dualDistrib_dualDistribInvOfBasis_right_inverse`

English:
theorem dualDistrib_dualDistribInvOfBasis_right_inverse
  given: (b : Basis ι R M) (c : Basis κ R N)
  proof: by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

中文:
定理 dualDistrib_dualDistribInvOfBasis_right_inverse
  条件: (b : 基 ι R M) (c : 基 κ R N)
  证明: by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

Depends on / 依赖: Basis.coe_dualBasis, Basis.coord_apply, Basis.repr_self, Basis.tensorProduct_apply, Finset, Finset.sum_eq_single, Function, Function.comp_apply, all_goals, b.dualBasis.tensorProduct, c.dualBasis, coe_comp, coe_dualBasis, comp_apply, coord_apply, dualBasis, dualDistribInvOfBasis_apply, dualDistrib_apply, id_coe, id_eq
-/
theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i]; rw [Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps!]
/--
Definition of `dualDistribEquivOfBasis` / `dualDistribEquivOfBasis` 的定义

English:
definition dualDistribEquivOfBasis
  signature: (b : Basis ι R M) (c : Basis κ R N)
  body: by
  refine LinearEquiv.ofLinearMap (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

中文:
定义 dualDistribEquivOfBasis
  签名: (b : 基 ι R M) (c : 基 κ R N)
  定义体: by
  refine LinearEquiv.ofLinearMap (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, dualDistrib, dualDistribInvOfBasis, dualDistrib_dualDistribInvOfBasis_left_inverse, dualDistrib_dualDistribInvOfBasis_right_inverse, ofLinearMap
-/
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M otimes[R] Dual R N ≃ₗ[R] Dual R (M otimes[R] N) := by
  refine LinearEquiv.ofLinearMap (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

variable (R M N)
variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
/--
Definition of `dualDistribEquiv` / `dualDistribEquiv` 的定义

English:
definition dualDistribEquiv
  signature: : Dual R M otimes[R] Dual R N ≃ₗ[R] Dual R (M otimes[R] N)
  body: dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

中文:
定义 dualDistribEquiv
  签名: : 对偶 R M otimes[R] 对偶 R N ≃ₗ[R] 对偶 R (M otimes[R] N)
  定义体: dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, dualDistribEquivOfBasis
-/
noncomputable def dualDistribEquiv : Dual R M otimes[R] Dual R N ≃ₗ[R] Dual R (M otimes[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

end TensorProduct
