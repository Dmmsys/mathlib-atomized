/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and the bases of elementary, complete homogeneous,
power sum, and monomial symmetric `MvPolynomial`s. We also prove some basic facts about them.

## Main declarations

* `MvPolynomial.IsSymmetric`

* `MvPolynomial.symmetricSubalgebra`

* `MvPolynomial.esymm`

* `MvPolynomial.hsymm`

* `MvPolynomial.psum`

* `MvPolynomial.msymm`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `hsymm σ R n` is the `n`th complete homogeneous symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

+ `msymm σ R μ` is the monomial symmetric polynomial whose exponents set are the parts
  of `μ ⊢ n` in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/

@[expose] public section


open Equiv (Perm)

noncomputable section

namespace Multiset

variable {R : Type*} [CommSemiring R]

/--
Definition of `esymm` / `esymm` 的定义

English:
definition esymm
  signature: (s : Multiset R) (n : Nat)
  body: ((s.powersetCard n).map Multiset.prod).sum

中文:
定义 esymm
  签名: (s : Multiset R) (n : 自然数)
  定义体: ((s.powersetCard n).map Multiset.prod).sum

Depends on / 依赖: Multiset, Multiset.prod, powersetCard, s.powersetCard
-/
def esymm (s : Multiset R) (n : Nat) : R :=
  ((s.powersetCard n).map Multiset.prod).sum

/--
theorem `_root_.Finset.esymm_map_val` / 定理 `_root_.Finset.esymm_map_val`

English:
theorem _root_.Finset.esymm_map_val
  given: {σ} (f : σ -> R) (s : Finset σ) (n : Nat)
  proof: by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  simp only [Function.comp_apply, Finset.prod_map_val, Finset.sum_map_val]

中文:
定理 _root_.有限集.esymm_map_val
  条件: {σ} (f : σ -> R) (s : 有限集 σ) (n : 自然数)
  证明: by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  simp only [Function.comp_apply, Finset.prod_map_val, Finset.sum_map_val]

Depends on / 依赖: Finset, Finset.map_val_val_powersetCard, Finset.prod_map_val, Finset.sum_map_val, Function, Function.comp_apply, comp_apply, map_map, map_val_val_powersetCard, powersetCard_map, prod_map_val, sum_map_val
-/
theorem _root_.Finset.esymm_map_val {σ} (f : σ -> R) (s : Finset σ) (n : Nat) :
    (s.val.map f).esymm n = (s.powersetCard n).sum fun t => t.prod f := by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  simp only [Function.comp_apply, Finset.prod_map_val, Finset.sum_map_val]

/--
lemma `pow_smul_esymm` / 引理 `pow_smul_esymm`

English:
lemma pow_smul_esymm
  statement: {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
  proof: by
  rw [esymm]; rw [smul_sum]; rw [map_map]
  trans ((powersetCard n m).map (fun x : Multiset R => s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx => ?_))
    rw [Function.comp_apply]; rw [(mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]

中文:
引理 pow_smul_esymm
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S R] [标量塔 S R R]
  证明: by
  rw [esymm]; rw [smul_sum]; rw [map_map]
  trans ((powersetCard n m).map (fun x : Multiset R => s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx => ?_))
    rw [Function.comp_apply]; rw [(mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_apply, Function.comp_def, Multiset, comp_apply, comp_def, congr_arg, map_congr, map_map, mem_powersetCard, powersetCard, powersetCard_map, simp_rw, smul_prod, smul_sum, x.prod
-/
lemma pow_smul_esymm {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    [SMulCommClass S R R] (s : S) (n : Nat) (m : Multiset R) :
    s ^ n • m.esymm n = (m.map (s • ·)).esymm n := by
  rw [esymm]; rw [smul_sum]; rw [map_map]
  trans ((powersetCard n m).map (fun x : Multiset R => s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx => ?_))
    rw [Function.comp_apply]; rw [(mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]

-- TODO: `Multiset.insert_eq_cons` being simp means that `esymm {x, y}` is not simp normal form
/--
lemma `esymm_pair_one` / 引理 `esymm_pair_one`

English:
lemma esymm_pair_one
  given: (x y : R)
  proof: by
  simp [esymm, powersetCard_one, add_comm]

中文:
引理 esymm_pair_one
  条件: (x y : R)
  证明: by
  simp [esymm, powersetCard_one, add_comm]
-/
@[simp] lemma esymm_pair_one (x y : R) :
    esymm (x ::ₘ {y}) 1 = x + y := by
  simp [esymm, powersetCard_one, add_comm]

/--
lemma `esymm_pair_two` / 引理 `esymm_pair_two`

English:
lemma esymm_pair_two
  given: (x y : R)
  proof: by
  simp [esymm, powersetCard_one]

中文:
引理 esymm_pair_two
  条件: (x y : R)
  证明: by
  simp [esymm, powersetCard_one]
-/
@[simp] lemma esymm_pair_two (x y : R) :
    esymm (x ::ₘ {y}) 2 = x * y := by
  simp [esymm, powersetCard_one]

end Multiset

namespace MvPolynomial

variable {σ τ : Type*} {R S : Type*}

/--
Definition of `IsSymmetric` / `IsSymmetric` 的定义

English:
definition IsSymmetric
  signature: [CommSemiring R] (φ : MvPolynomial σ R)
  body: forall e : Perm σ, rename e φ = φ

中文:
定义 IsSymmetric
  签名: [交换半环 R] (φ : 多元多项式 σ R)
  定义体: forall e : Perm σ, rename e φ = φ
-/
def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  forall e : Perm σ, rename e φ = φ

/--
Definition of `symmetricSubalgebra` / `symmetricSubalgebra` 的定义

English:
definition symmetricSubalgebra
  signature: (σ R : Type*) [CommSemiring R]
  body: Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]

@[simp]

中文:
定义 symmetricSubalgebra
  签名: (σ R : 类型) [交换半环 R]
  定义体: Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]

@[simp]

Depends on / 依赖: IsSymmetric, Set.ofPred, ofPred
-/
def symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPolynomial σ R) where
  carrier := Set.ofPred IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]

@[simp]
/--
theorem `mem_symmetricSubalgebra` / 定理 `mem_symmetricSubalgebra`

English:
theorem mem_symmetricSubalgebra
  given: [CommSemiring R] (p : MvPolynomial σ R)
  proof: Iff.rfl

中文:
定理 mem_symmetricSubalgebra
  条件: [交换半环 R] (p : 多元多项式 σ R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_symmetricSubalgebra [CommSemiring R] (p : MvPolynomial σ R) :
    p in symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ ψ : MvPolynomial σ R}

@[simp]
/--
theorem `C` / 定理 `C`

English:
theorem C
  given: (r : R)
  statement: IsSymmetric (C r : MvPolynomial σ R)
  proof: (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]

中文:
定理 C
  条件: (r : R)
  结论: IsSymmetric (C r : 多元多项式 σ R)
  证明: (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]

Depends on / 依赖: algebraMap_mem, symmetricSubalgebra
-/
theorem C (r : R) : IsSymmetric (C r : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: IsSymmetric (0 : MvPolynomial σ R)
  proof: (symmetricSubalgebra σ R).zero_mem

@[simp]

中文:
定理 zero
  结论: IsSymmetric (0 : 多元多项式 σ R)
  证明: (symmetricSubalgebra σ R).zero_mem

@[simp]

Depends on / 依赖: symmetricSubalgebra, zero_mem
-/
theorem zero : IsSymmetric (0 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).zero_mem

@[simp]
/--
theorem `one` / 定理 `one`

English:
theorem one
  statement: IsSymmetric (1 : MvPolynomial σ R)
  proof: (symmetricSubalgebra σ R).one_mem

中文:
定理 one
  结论: IsSymmetric (1 : 多元多项式 σ R)
  证明: (symmetricSubalgebra σ R).one_mem

Depends on / 依赖: one_mem, symmetricSubalgebra
-/
theorem one : IsSymmetric (1 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).one_mem

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  statement: IsSymmetric (φ + ψ)
  proof: (symmetricSubalgebra σ R).add_mem hφ hψ

中文:
定理 add
  条件: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  结论: IsSymmetric (φ + ψ)
  证明: (symmetricSubalgebra σ R).add_mem hφ hψ

Depends on / 依赖: add_mem, symmetricSubalgebra
-/
theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
  (symmetricSubalgebra σ R).add_mem hφ hψ

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  statement: IsSymmetric (φ * ψ)
  proof: (symmetricSubalgebra σ R).mul_mem hφ hψ

中文:
定理 mul
  条件: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  结论: IsSymmetric (φ * ψ)
  证明: (symmetricSubalgebra σ R).mul_mem hφ hψ

Depends on / 依赖: mul_mem, symmetricSubalgebra
-/
theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
  (symmetricSubalgebra σ R).mul_mem hφ hψ

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (r : R) (hφ : IsSymmetric φ)
  statement: IsSymmetric (r • φ)
  proof: (symmetricSubalgebra σ R).smul_mem hφ r

@[simp]

中文:
定理 smul
  条件: (r : R) (hφ : IsSymmetric φ)
  结论: IsSymmetric (r • φ)
  证明: (symmetricSubalgebra σ R).smul_mem hφ r

@[simp]

Depends on / 依赖: smul_mem, symmetricSubalgebra
-/
theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
  (symmetricSubalgebra σ R).smul_mem hφ r

@[simp]
/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (hφ : IsSymmetric φ) (f : R ->+* S)
  statement: IsSymmetric (map f φ)
  proof: fun e => by
  rw [← map_rename]; rw [hφ]

中文:
定理 map
  条件: (hφ : IsSymmetric φ) (f : R ->+* S)
  结论: IsSymmetric (map f φ)
  证明: fun e => by
  rw [← map_rename]; rw [hφ]

Depends on / 依赖: map_rename
-/
theorem map (hφ : IsSymmetric φ) (f : R ->+* S) : IsSymmetric (map f φ) := fun e => by
  rw [← map_rename]; rw [hφ]

/--
theorem `rename` / 定理 `rename`

English:
theorem rename
  given: (hφ : φ.IsSymmetric) (e : σ ≃ τ)
  statement: (rename e φ).IsSymmetric
  proof: fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id_apply]
  rw [hφ]

@[simp]

中文:
定理 rename
  条件: (hφ : φ.IsSymmetric) (e : σ ≃ τ)
  结论: (rename e φ).IsSymmetric
  证明: fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id_apply]
  rw [hφ]

@[simp]
-/
protected theorem rename (hφ : φ.IsSymmetric) (e : σ ≃ τ) : (rename e φ).IsSymmetric := fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id_apply]
  rw [hφ]

@[simp]
/--
theorem `_root_.MvPolynomial.isSymmetric_rename` / 定理 `_root_.MvPolynomial.isSymmetric_rename`

English:
theorem _root_.MvPolynomial.isSymmetric_rename
  given: {e : σ ≃ τ}
  proof: ⟨fun h => by simpa using (IsSymmetric.rename (R := R) h e.symm), (IsSymmetric.rename · e)⟩

中文:
定理 _root_.多元多项式.isSymmetric_rename
  条件: {e : σ ≃ τ}
  证明: ⟨fun h => by simpa using (IsSymmetric.rename (R := R) h e.symm), (IsSymmetric.rename · e)⟩

Depends on / 依赖: IsSymmetric, IsSymmetric.rename, e.symm
-/
theorem _root_.MvPolynomial.isSymmetric_rename {e : σ ≃ τ} :
    (MvPolynomial.rename e φ).IsSymmetric ↔ φ.IsSymmetric :=
  ⟨fun h => by simpa using (IsSymmetric.rename (R := R) h e.symm), (IsSymmetric.rename · e)⟩

end CommSemiring

section CommRing

variable [CommRing R] {φ ψ : MvPolynomial σ R}

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hφ : IsSymmetric φ)
  statement: IsSymmetric (-φ)
  proof: (symmetricSubalgebra σ R).neg_mem hφ

中文:
定理 neg
  条件: (hφ : IsSymmetric φ)
  结论: IsSymmetric (-φ)
  证明: (symmetricSubalgebra σ R).neg_mem hφ

Depends on / 依赖: neg_mem, symmetricSubalgebra
-/
theorem neg (hφ : IsSymmetric φ) : IsSymmetric (-φ) :=
  (symmetricSubalgebra σ R).neg_mem hφ

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  statement: IsSymmetric (φ - ψ)
  proof: (symmetricSubalgebra σ R).sub_mem hφ hψ

中文:
定理 sub
  条件: (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ)
  结论: IsSymmetric (φ - ψ)
  证明: (symmetricSubalgebra σ R).sub_mem hφ hψ

Depends on / 依赖: sub_mem, symmetricSubalgebra
-/
theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
  (symmetricSubalgebra σ R).sub_mem hφ hψ

end CommRing

end IsSymmetric

set_option backward.isDefEq.respectTransparency false in
/-- `MvPolynomial.rename` induces an isomorphism between the symmetric subalgebras. -/
@[simps! apply_coe symm_apply_coe]
/--
Definition of `renameSymmetricSubalgebra` / `renameSymmetricSubalgebra` 的定义

English:
definition renameSymmetricSubalgebra
  signature: [CommSemiring R] (e : σ ≃ τ)
  body: AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

中文:
定义 renameSymmetricSubalgebra
  签名: [交换半环 R] (e : σ ≃ τ)
  定义体: AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.ext, Subalgebra, Subalgebra.val, Subtype, Subtype.ext, codRestrict, e.symm, ofAlgHom, symmetricSubalgebra
-/
def renameSymmetricSubalgebra [CommSemiring R] (e : σ ≃ τ) :
    symmetricSubalgebra σ R ≃ₐ[R] symmetricSubalgebra τ R :=
  AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

variable (σ R : Type*) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

section ElementarySymmetric

open Finset

/--
Definition of `esymm` / `esymm` 的定义

English:
definition esymm
  signature: (n : Nat)
  body: ∑ t in powersetCard n univ, ∏ i in t, X i

中文:
定义 esymm
  签名: (n : 自然数)
  定义体: ∑ t in powersetCard n univ, ∏ i in t, X i

Depends on / 依赖: powersetCard
-/
def esymm (n : Nat) : MvPolynomial σ R :=
  ∑ t in powersetCard n univ, ∏ i in t, X i

/--
Definition of `esymmPart` / `esymmPart` 的定义

English:
definition esymmPart
  signature: {n : Nat} (μ : n.Partition)
  body: (μ.parts.map (esymm σ R)).prod

中文:
定义 esymmPart
  签名: {n : 自然数} (μ : n.分拆)
  定义体: (μ.parts.map (esymm σ R)).prod

Depends on / 依赖: parts.map
-/
def esymmPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (esymm σ R)).prod

/--
theorem `esymm_eq_multiset_esymm` / 定理 `esymm_eq_multiset_esymm`

English:
theorem esymm_eq_multiset_esymm
  statement: esymm σ R = (univ.val.map X).esymm
  proof: by
  exact funext fun n => (esymm_map_val X _ n).symm

中文:
定理 esymm_eq_multiset_esymm
  结论: esymm σ R = (univ.val.map X).esymm
  证明: by
  exact funext fun n => (esymm_map_val X _ n).symm

Depends on / 依赖: esymm_map_val
-/
theorem esymm_eq_multiset_esymm : esymm σ R = (univ.val.map X).esymm := by
  exact funext fun n => (esymm_map_val X _ n).symm

/--
theorem `aeval_esymm_eq_multiset_esymm` / 定理 `aeval_esymm_eq_multiset_esymm`

English:
theorem aeval_esymm_eq_multiset_esymm
  given: [Algebra R S] (n : Nat) (f : σ -> S)
  proof: by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

中文:
定理 aeval_esymm_eq_multiset_esymm
  条件: [代数 R S] (n : 自然数) (f : σ -> S)
  证明: by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

Depends on / 依赖: aeval_X, aeval_prod, aeval_sum, esymm_map_val, simp_rw
-/
theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (n : Nat) (f : σ -> S) :
    aeval f (esymm σ R n) = (univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

/--
theorem `esymm_eq_sum_subtype` / 定理 `esymm_eq_sum_subtype`

English:
theorem esymm_eq_sum_subtype
  given: (n : Nat)
  proof: sum_subtype _ (fun _ => mem_powersetCard_univ) _

中文:
定理 esymm_eq_sum_subtype
  条件: (n : 自然数)
  证明: sum_subtype _ (fun _ => mem_powersetCard_univ) _

Depends on / 依赖: mem_powersetCard_univ, sum_subtype
-/
theorem esymm_eq_sum_subtype (n : Nat) :
    esymm σ R n = ∑ t : {s : Finset σ // #s = n}, ∏ i in (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powersetCard_univ) _

/--
theorem `esymm_eq_sum_monomial` / 定理 `esymm_eq_sum_monomial`

English:
theorem esymm_eq_sum_monomial
  given: (n : Nat)
  proof: by
  simp_rw [monomial_sum_one, esymm, ← X_pow_eq_monomial, pow_one]

@[simp]

中文:
定理 esymm_eq_sum_monomial
  条件: (n : 自然数)
  证明: by
  simp_rw [monomial_sum_one, esymm, ← X_pow_eq_monomial, pow_one]

@[simp]

Depends on / 依赖: X_pow_eq_monomial, monomial_sum_one, pow_one, simp_rw
-/
theorem esymm_eq_sum_monomial (n : Nat) :
    esymm σ R n = ∑ t in powersetCard n univ, monomial (∑ i in t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one, esymm, ← X_pow_eq_monomial, pow_one]

@[simp]
/--
theorem `esymm_zero` / 定理 `esymm_zero`

English:
theorem esymm_zero
  statement: esymm σ R 0 = 1
  proof: by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]

@[simp]

中文:
定理 esymm_zero
  结论: esymm σ R 0 = 1
  证明: by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]

@[simp]

Depends on / 依赖: powersetCard_zero, prod_empty, sum_singleton
-/
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]

@[simp]
/--
theorem `esymm_one` / 定理 `esymm_one`

English:
theorem esymm_one
  statement: esymm σ R 1 = ∑ i, X i
  proof: by simp [esymm, powersetCard_one]

中文:
定理 esymm_one
  结论: esymm σ R 1 = ∑ i, X i
  证明: by simp [esymm, powersetCard_one]

Depends on / 依赖: powersetCard_one
-/
theorem esymm_one : esymm σ R 1 = ∑ i, X i := by simp [esymm, powersetCard_one]

/--
theorem `esymmPart_zero` / 定理 `esymmPart_zero`

English:
theorem esymmPart_zero
  statement: esymmPart σ R (.indiscrete 0) = 1
  proof: by simp [esymmPart]

@[simp]

中文:
定理 esymmPart_zero
  结论: esymmPart σ R (.indiscrete 0) = 1
  证明: by simp [esymmPart]

@[simp]

Depends on / 依赖: esymmPart
-/
theorem esymmPart_zero : esymmPart σ R (.indiscrete 0) = 1 := by simp [esymmPart]

@[simp]
/--
theorem `esymmPart_indiscrete` / 定理 `esymmPart_indiscrete`

English:
theorem esymmPart_indiscrete
  given: (n : Nat)
  statement: esymmPart σ R (.indiscrete n) = esymm σ R n
  proof: by
  cases n <;> simp [esymmPart]

中文:
定理 esymmPart_indiscrete
  条件: (n : 自然数)
  结论: esymmPart σ R (.indiscrete n) = esymm σ R n
  证明: by
  cases n <;> simp [esymmPart]

Depends on / 依赖: esymmPart
-/
theorem esymmPart_indiscrete (n : Nat) : esymmPart σ R (.indiscrete n) = esymm σ R n := by
  cases n <;> simp [esymmPart]

/--
theorem `map_esymm` / 定理 `map_esymm`

English:
theorem map_esymm
  given: (n : Nat) (f : R ->+* S)
  statement: map f (esymm σ R n) = esymm σ S n
  proof: by
  simp_rw [esymm, map_sum, map_prod, map_X]

中文:
定理 map_esymm
  条件: (n : 自然数) (f : R ->+* S)
  结论: map f (esymm σ R n) = esymm σ S n
  证明: by
  simp_rw [esymm, map_sum, map_prod, map_X]

Depends on / 依赖: map_X, map_prod, map_sum, simp_rw
-/
theorem map_esymm (n : Nat) (f : R ->+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]

/--
theorem `rename_esymm` / 定理 `rename_esymm`

English:
theorem rename_esymm
  given: (n : Nat) (e : σ ≃ τ)
  statement: rename e (esymm σ R n) = esymm τ R n
  proof: calc
    rename e (esymm σ R n) = ∑ x in powersetCard n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetCard n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [powersetCard_map, -map_univ_equiv, (mapEmbedding_apply)]
    _ = ∑ t in powersetCard n univ, ∏ i in t, X i := by rw [map_univ_equiv]

中文:
定理 rename_esymm
  条件: (n : 自然数) (e : σ ≃ τ)
  结论: rename e (esymm σ R n) = esymm τ R n
  证明: calc
    rename e (esymm σ R n) = ∑ x in powersetCard n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetCard n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [powersetCard_map, -map_univ_equiv, (mapEmbedding_apply)]
    _ = ∑ t in powersetCard n univ, ∏ i in t, X i := by rw [map_univ_equiv]

Depends on / 依赖: e.toEmbedding, mapEmbedding_apply, map_prod, map_sum, map_univ_equiv, powersetCard, powersetCard_map, rename_X, simp_rw, toEmbedding, univ.map
-/
theorem rename_esymm (n : Nat) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x in powersetCard n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetCard n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [powersetCard_map, -map_univ_equiv, (mapEmbedding_apply)]
    _ = ∑ t in powersetCard n univ, ∏ i in t, X i := by rw [map_univ_equiv]

/--
theorem `esymm_isSymmetric` / 定理 `esymm_isSymmetric`

English:
theorem esymm_isSymmetric
  given: (n : Nat)
  statement: IsSymmetric (esymm σ R n)
  proof: by
  intro
  rw [rename_esymm]

中文:
定理 esymm_isSymmetric
  条件: (n : 自然数)
  结论: IsSymmetric (esymm σ R n)
  证明: by
  intro
  rw [rename_esymm]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.to_continuousDiv, rename_esymm, to_continuousDiv
-/
theorem esymm_isSymmetric (n : Nat) : IsSymmetric (esymm σ R n) := by
  intro
  rw [rename_esymm]

/--
theorem `support_esymm''` / 定理 `support_esymm''`

English:
theorem support_esymm''
  given: [DecidableEq σ] [Nontrivial R] (n : Nat)
  proof: by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  simp only [support, MvPolynomial, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  refine Finsupp.support_sum_eq_biUnion _ fun s t hst => ?_
  rw [disjoint_left]; rw [Finsupp.support_single _ one_ne_zero]
  rw [Finsupp.support_single _ one_ne_zero]
  simp only [mem_singleton]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion _ (by simp)]; rw [Finsupp.support_sum_eq_biUnion _ (by simp)]
    at this
  simp_all

中文:
定理 support_esymm''
  条件: [DecidableEq σ] [非平凡 R] (n : 自然数)
  证明: by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  simp only [support, MvPolynomial, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  refine Finsupp.support_sum_eq_biUnion _ fun s t hst => ?_
  rw [disjoint_left]; rw [Finsupp.support_single _ one_ne_zero]
  rw [Finsupp.support_single _ one_ne_zero]
  simp only [mem_singleton]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion _ (by simp)]; rw [Finsupp.support_sum_eq_biUnion _ (by simp)]
    at this
  simp_all

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_sum, Finsupp, Finsupp.support, Finsupp.support_single, Finsupp.support_sum_eq_biUnion, MvPolynomial, coeff_single, coeff_sum, congr_arg, disjoint_left, esymm_eq_sum_monomial, mem_singleton, one_ne_zero, single_eq_monomial, support, support_single, support_sum_eq_biUnion
-/
theorem support_esymm'' [DecidableEq σ] [Nontrivial R] (n : Nat) :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t =>
        (Finsupp.single (∑ i in t, Finsupp.single i 1) (1 : R)).support := by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  simp only [support, MvPolynomial, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
  refine Finsupp.support_sum_eq_biUnion _ fun s t hst => ?_
  rw [disjoint_left]; rw [Finsupp.support_single _ one_ne_zero]
  rw [Finsupp.support_single _ one_ne_zero]
  simp only [mem_singleton]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion _ (by simp)]; rw [Finsupp.support_sum_eq_biUnion _ (by simp)]
    at this
  simp_all

/--
theorem `support_esymm'` / 定理 `support_esymm'`

English:
theorem support_esymm'
  given: [DecidableEq σ] [Nontrivial R] (n : Nat)
  statement: (esymm σ R n).support =
  proof: by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single _ one_ne_zero

中文:
定理 support_esymm'
  条件: [DecidableEq σ] [非平凡 R] (n : 自然数)
  结论: (esymm σ R n).support =
  证明: by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single _ one_ne_zero

Depends on / 依赖: Finsupp, Finsupp.support_single, one_ne_zero, support_esymm, support_single
-/
theorem support_esymm' [DecidableEq σ] [Nontrivial R] (n : Nat) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i in t, Finsupp.single i 1} := by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single _ one_ne_zero

/--
theorem `support_esymm` / 定理 `support_esymm`

English:
theorem support_esymm
  given: [DecidableEq σ] [Nontrivial R] (n : Nat)
  statement: (esymm σ R n).support =
  proof: by
  rw [support_esymm']
  exact biUnion_singleton

中文:
定理 support_esymm
  条件: [DecidableEq σ] [非平凡 R] (n : 自然数)
  结论: (esymm σ R n).support =
  证明: by
  rw [support_esymm']
  exact biUnion_singleton

Depends on / 依赖: biUnion_singleton, support_esymm
-/
theorem support_esymm [DecidableEq σ] [Nontrivial R] (n : Nat) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).image fun t => ∑ i in t, Finsupp.single i 1 := by
  rw [support_esymm']
  exact biUnion_singleton

/--
theorem `degrees_esymm` / 定理 `degrees_esymm`

English:
theorem degrees_esymm
  given: [Nontrivial R] {n : Nat} (hpos : 0 < n) (hn : n <= Fintype.card σ)
  proof: by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i in t, Finsupp.single i 1) = val := by
      funext
      simp
    rw [degrees_def]; rw [support_esymm]; rw [sup_image]; rw [this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine apply_sup_eq_sup_comp _ ?_ ?_ <;> simp
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using! powersetCard_sup _ _ (Nat.lt_of_succ_le hn)

中文:
定理 degrees_esymm
  条件: [非平凡 R] {n : 自然数} (hpos : 0 < n) (hn : n <= 有限类型.card σ)
  证明: by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i in t, Finsupp.single i 1) = val := by
      funext
      simp
    rw [degrees_def]; rw [support_esymm]; rw [sup_image]; rw [this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine apply_sup_eq_sup_comp _ ?_ ?_ <;> simp
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using! powersetCard_sup _ _ (Nat.lt_of_succ_le hn)

Depends on / 依赖: Finset, Finsupp, Finsupp.single, Finsupp.toMultiset, Nat.exists_eq_succ_of_ne_zero, Nat.lt_of_succ_le, apply_sup_eq_sup_comp, classical, degrees_def, exists_eq_succ_of_ne_zero, hpos.ne, lt_of_succ_le, powersetCard, powersetCard_sup, single, sup_image, support_esymm, toMultiset
-/
theorem degrees_esymm [Nontrivial R] {n : Nat} (hpos : 0 < n) (hn : n <= Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i in t, Finsupp.single i 1) = val := by
      funext
      simp
    rw [degrees_def]; rw [support_esymm]; rw [sup_image]; rw [this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine apply_sup_eq_sup_comp _ ?_ ?_ <;> simp
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using! powersetCard_sup _ _ (Nat.lt_of_succ_le hn)

end ElementarySymmetric

section CompleteHomogeneousSymmetric

open Finset Multiset Sym

variable [DecidableEq σ] [DecidableEq τ]

/--
Definition of `hsymm` / `hsymm` 的定义

English:
definition hsymm
  signature: (n : Nat)
  body: ∑ s : Sym σ n, (s.1.map X).prod

中文:
定义 hsymm
  签名: (n : 自然数)
  定义体: ∑ s : Sym σ n, (s.1.map X).prod
-/
def hsymm (n : Nat) : MvPolynomial σ R := ∑ s : Sym σ n, (s.1.map X).prod

/--
Definition of `hsymmPart` / `hsymmPart` 的定义

English:
definition hsymmPart
  signature: {n : Nat} (μ : n.Partition)
  body: (μ.parts.map (hsymm σ R)).prod

@[simp]

中文:
定义 hsymmPart
  签名: {n : 自然数} (μ : n.分拆)
  定义体: (μ.parts.map (hsymm σ R)).prod

@[simp]

Depends on / 依赖: parts.map
-/
def hsymmPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (hsymm σ R)).prod

@[simp]
/--
theorem `hsymm_zero` / 定理 `hsymm_zero`

English:
theorem hsymm_zero
  statement: hsymm σ R 0 = 1
  proof: by simp [hsymm, eq_nil_of_card_zero]

@[simp]

中文:
定理 hsymm_zero
  结论: hsymm σ R 0 = 1
  证明: by simp [hsymm, eq_nil_of_card_zero]

@[simp]

Depends on / 依赖: eq_nil_of_card_zero
-/
theorem hsymm_zero : hsymm σ R 0 = 1 := by simp [hsymm, eq_nil_of_card_zero]

@[simp]
/--
theorem `hsymm_one` / 定理 `hsymm_one`

English:
theorem hsymm_one
  statement: hsymm σ R 1 = ∑ i, X i
  proof: by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]

中文:
定理 hsymm_one
  结论: hsymm σ R 1 = ∑ i, X i
  证明: by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]

Depends on / 依赖: Fintype, Fintype.sum_equiv, Multiset, Multiset.map_singleton, Multiset.prod_singleton, implies_true, map_singleton, oneEquiv, oneEquiv_apply, prod_singleton, sum_equiv
-/
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]

/--
theorem `hsymmPart_zero` / 定理 `hsymmPart_zero`

English:
theorem hsymmPart_zero
  statement: hsymmPart σ R (.indiscrete 0) = 1
  proof: by simp [hsymmPart]

@[simp]

中文:
定理 hsymmPart_zero
  结论: hsymmPart σ R (.indiscrete 0) = 1
  证明: by simp [hsymmPart]

@[simp]

Depends on / 依赖: hsymmPart
-/
theorem hsymmPart_zero : hsymmPart σ R (.indiscrete 0) = 1 := by simp [hsymmPart]

@[simp]
/--
theorem `hsymmPart_indiscrete` / 定理 `hsymmPart_indiscrete`

English:
theorem hsymmPart_indiscrete
  given: (n : Nat)
  statement: hsymmPart σ R (.indiscrete n) = hsymm σ R n
  proof: by
  cases n <;> simp [hsymmPart]

中文:
定理 hsymmPart_indiscrete
  条件: (n : 自然数)
  结论: hsymmPart σ R (.indiscrete n) = hsymm σ R n
  证明: by
  cases n <;> simp [hsymmPart]

Depends on / 依赖: hsymmPart
-/
theorem hsymmPart_indiscrete (n : Nat) : hsymmPart σ R (.indiscrete n) = hsymm σ R n := by
  cases n <;> simp [hsymmPart]

/--
theorem `map_hsymm` / 定理 `map_hsymm`

English:
theorem map_hsymm
  given: (n : Nat) (f : R ->+* S)
  statement: map f (hsymm σ R n) = hsymm σ S n
  proof: by
  simp [hsymm, ← Multiset.prod_hom']

中文:
定理 map_hsymm
  条件: (n : 自然数) (f : R ->+* S)
  结论: map f (hsymm σ R n) = hsymm σ S n
  证明: by
  simp [hsymm, ← Multiset.prod_hom']

Depends on / 依赖: Multiset, Multiset.prod_hom, prod_hom
-/
theorem map_hsymm (n : Nat) (f : R ->+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp [hsymm, ← Multiset.prod_hom']

/--
theorem `rename_hsymm` / 定理 `rename_hsymm`

English:
theorem rename_hsymm
  given: (n : Nat) (e : σ ≃ τ)
  statement: rename e (hsymm σ R n) = hsymm τ R n
  proof: by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp

中文:
定理 rename_hsymm
  条件: (n : 自然数) (e : σ ≃ τ)
  结论: rename e (hsymm σ R n) = hsymm τ R n
  证明: by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp

Depends on / 依赖: Fintype, Fintype.sum_equiv, equivCongr, map_sum, prod_hom, rename_X, simp_rw, sum_equiv
-/
theorem rename_hsymm (n : Nat) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp

/--
theorem `hsymm_isSymmetric` / 定理 `hsymm_isSymmetric`

English:
theorem hsymm_isSymmetric
  given: (n : Nat)
  statement: IsSymmetric (hsymm σ R n)
  proof: rename_hsymm _ _ n

中文:
定理 hsymm_isSymmetric
  条件: (n : 自然数)
  结论: IsSymmetric (hsymm σ R n)
  证明: rename_hsymm _ _ n

Depends on / 依赖: rename_hsymm
-/
theorem hsymm_isSymmetric (n : Nat) : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

section PowerSum

open Finset

/--
Definition of `psum` / `psum` 的定义

English:
definition psum
  signature: (n : Nat)
  body: ∑ i, X i ^ n

中文:
定义 psum
  签名: (n : 自然数)
  定义体: ∑ i, X i ^ n
-/
def psum (n : Nat) : MvPolynomial σ R := ∑ i, X i ^ n

/--
Definition of `psumPart` / `psumPart` 的定义

English:
definition psumPart
  signature: {n : Nat} (μ : n.Partition)
  body: (μ.parts.map (psum σ R)).prod

@[simp]

中文:
定义 psumPart
  签名: {n : 自然数} (μ : n.分拆)
  定义体: (μ.parts.map (psum σ R)).prod

@[simp]

Depends on / 依赖: parts.map
-/
def psumPart {n : Nat} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (psum σ R)).prod

@[simp]
/--
theorem `psum_zero` / 定理 `psum_zero`

English:
theorem psum_zero
  statement: psum σ R 0 = Fintype.card σ
  proof: by simp [psum]

@[simp]

中文:
定理 psum_zero
  结论: psum σ R 0 = 有限类型.card σ
  证明: by simp [psum]

@[simp]
-/
theorem psum_zero : psum σ R 0 = Fintype.card σ := by simp [psum]

@[simp]
/--
theorem `psum_one` / 定理 `psum_one`

English:
theorem psum_one
  statement: psum σ R 1 = ∑ i, X i
  proof: by simp [psum]

@[simp]

中文:
定理 psum_one
  结论: psum σ R 1 = ∑ i, X i
  证明: by simp [psum]

@[simp]
-/
theorem psum_one : psum σ R 1 = ∑ i, X i := by simp [psum]

@[simp]
/--
theorem `psumPart_zero` / 定理 `psumPart_zero`

English:
theorem psumPart_zero
  statement: psumPart σ R (.indiscrete 0) = 1
  proof: by simp [psumPart]

@[simp]

中文:
定理 psumPart_zero
  结论: psumPart σ R (.indiscrete 0) = 1
  证明: by simp [psumPart]

@[simp]

Depends on / 依赖: psumPart
-/
theorem psumPart_zero : psumPart σ R (.indiscrete 0) = 1 := by simp [psumPart]

@[simp]
/--
theorem `psumPart_indiscrete` / 定理 `psumPart_indiscrete`

English:
theorem psumPart_indiscrete
  given: {n : Nat} (npos : n != 0)
  proof: by simp [psumPart, npos]

@[simp]

中文:
定理 psumPart_indiscrete
  条件: {n : 自然数} (npos : n != 0)
  证明: by simp [psumPart, npos]

@[simp]

Depends on / 依赖: psumPart
-/
theorem psumPart_indiscrete {n : Nat} (npos : n != 0) :
    psumPart σ R (.indiscrete n) = psum σ R n := by simp [psumPart, npos]

@[simp]
/--
theorem `rename_psum` / 定理 `rename_psum`

English:
theorem rename_psum
  given: (n : Nat) (e : σ ≃ τ)
  statement: rename e (psum σ R n) = psum τ R n
  proof: by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

中文:
定理 rename_psum
  条件: (n : 自然数) (e : σ ≃ τ)
  结论: rename e (psum σ R n) = psum τ R n
  证明: by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

Depends on / 依赖: e.sum_comp, map_pow, map_sum, rename_X, simp_rw, sum_comp
-/
theorem rename_psum (n : Nat) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

/--
theorem `psum_isSymmetric` / 定理 `psum_isSymmetric`

English:
theorem psum_isSymmetric
  given: (n : Nat)
  statement: IsSymmetric (psum σ R n)
  proof: rename_psum _ _ n

中文:
定理 psum_isSymmetric
  条件: (n : 自然数)
  结论: IsSymmetric (psum σ R n)
  证明: rename_psum _ _ n

Depends on / 依赖: rename_psum
-/
theorem psum_isSymmetric (n : Nat) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section MonomialSymmetric

variable [DecidableEq σ] [DecidableEq τ] {n : Nat}

/--
Definition of `msymm` / `msymm` 的定义

English:
definition msymm
  signature: (μ : n.Partition)
  body: ∑ s : {a : Sym σ n // .ofSym a = μ}, (s.1.1.map X).prod

@[simp]

中文:
定义 msymm
  签名: (μ : n.分拆)
  定义体: ∑ s : {a : Sym σ n // .ofSym a = μ}, (s.1.1.map X).prod

@[simp]
-/
def msymm (μ : n.Partition) : MvPolynomial σ R :=
  ∑ s : {a : Sym σ n // .ofSym a = μ}, (s.1.1.map X).prod

@[simp]
/--
theorem `msymm_zero` / 定理 `msymm_zero`

English:
theorem msymm_zero
  statement: msymm σ R (.indiscrete 0) = 1
  proof: by
  rw [msymm]; rw [Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0)]; rw [rfl⟩]
  simp

@[simp]

中文:
定理 msymm_zero
  结论: msymm σ R (.indiscrete 0) = 1
  证明: by
  rw [msymm]; rw [Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0)]; rw [rfl⟩]
  simp

@[simp]

Depends on / 依赖: Fintype, Fintype.sum_subsingleton, Sym.nil, sum_subsingleton
-/
theorem msymm_zero : msymm σ R (.indiscrete 0) = 1 := by
  rw [msymm]; rw [Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0)]; rw [rfl⟩]
  simp

@[simp]
/--
theorem `msymm_one` / 定理 `msymm_one`

English:
theorem msymm_one
  statement: msymm σ R (.indiscrete 1) = ∑ i, X i
  proof: by
  have : (fun (x : Sym σ 1) => x in Set.univ) =
      (fun x => Nat.Partition.ofSym x = Nat.Partition.indiscrete 1) := by
    simp_rw [Set.mem_univ, Nat.Partition.ofSym_one]
  symm
  rw [Fintype.sum_equiv (Equiv.trans Sym.oneEquiv (Equiv.Set.univ (Sym σ 1)).symm)
    _ (fun s => (s.1.1.map X).prod)]
  · apply Fintype.sum_equiv (Equiv.subtypeEquivProp this)
    intro x
    congr
  · intro x
    rw [← Multiset.prod_singleton (X x)]; rw [← Multiset.map_singleton]
    congr

@[simp]

中文:
定理 msymm_one
  结论: msymm σ R (.indiscrete 1) = ∑ i, X i
  证明: by
  have : (fun (x : Sym σ 1) => x in Set.univ) =
      (fun x => Nat.Partition.ofSym x = Nat.Partition.indiscrete 1) := by
    simp_rw [Set.mem_univ, Nat.Partition.ofSym_one]
  symm
  rw [Fintype.sum_equiv (Equiv.trans Sym.oneEquiv (Equiv.Set.univ (Sym σ 1)).symm)
    _ (fun s => (s.1.1.map X).prod)]
  · apply Fintype.sum_equiv (Equiv.subtypeEquivProp this)
    intro x
    congr
  · intro x
    rw [← Multiset.prod_singleton (X x)]; rw [← Multiset.map_singleton]
    congr

@[simp]

Depends on / 依赖: Equiv.Set.univ, Equiv.subtypeEquivProp, Equiv.trans, Fintype, Fintype.sum_equiv, Multiset, Multiset.map_singleton, Multiset.prod_singleton, Nat.Partition.indiscrete, Nat.Partition.ofSym, Nat.Partition.ofSym_one, Partition, Set.mem_univ, Set.univ, Sym.oneEquiv, indiscrete, map_singleton, mem_univ, ofSym_one, oneEquiv
-/
theorem msymm_one : msymm σ R (.indiscrete 1) = ∑ i, X i := by
  have : (fun (x : Sym σ 1) => x in Set.univ) =
      (fun x => Nat.Partition.ofSym x = Nat.Partition.indiscrete 1) := by
    simp_rw [Set.mem_univ, Nat.Partition.ofSym_one]
  symm
  rw [Fintype.sum_equiv (Equiv.trans Sym.oneEquiv (Equiv.Set.univ (Sym σ 1)).symm)
    _ (fun s => (s.1.1.map X).prod)]
  · apply Fintype.sum_equiv (Equiv.subtypeEquivProp this)
    intro x
    congr
  · intro x
    rw [← Multiset.prod_singleton (X x)]; rw [← Multiset.map_singleton]
    congr

@[simp]
/--
theorem `rename_msymm` / 定理 `rename_msymm`

English:
theorem rename_msymm
  given: (μ : n.Partition) (e : σ ≃ τ)
  proof: by
  rw [msymm]; rw [map_sum]
  apply Fintype.sum_equiv (Nat.Partition.ofSymShapeEquiv μ e)
  intro
  rw [← Multiset.prod_hom]; rw [Multiset.map_map]; rw [Nat.Partition.ofSymShapeEquiv]
  simp

中文:
定理 rename_msymm
  条件: (μ : n.分拆) (e : σ ≃ τ)
  证明: by
  rw [msymm]; rw [map_sum]
  apply Fintype.sum_equiv (Nat.Partition.ofSymShapeEquiv μ e)
  intro
  rw [← Multiset.prod_hom]; rw [Multiset.map_map]; rw [Nat.Partition.ofSymShapeEquiv]
  simp

Depends on / 依赖: Fintype, Fintype.sum_equiv, Multiset, Multiset.map_map, Multiset.prod_hom, Nat.Partition.ofSymShapeEquiv, Partition, map_map, map_sum, ofSymShapeEquiv, prod_hom, sum_equiv
-/
theorem rename_msymm (μ : n.Partition) (e : σ ≃ τ) :
    rename e (msymm σ R μ) = msymm τ R μ := by
  rw [msymm]; rw [map_sum]
  apply Fintype.sum_equiv (Nat.Partition.ofSymShapeEquiv μ e)
  intro
  rw [← Multiset.prod_hom]; rw [Multiset.map_map]; rw [Nat.Partition.ofSymShapeEquiv]
  simp

/--
theorem `msymm_isSymmetric` / 定理 `msymm_isSymmetric`

English:
theorem msymm_isSymmetric
  given: (μ : n.Partition)
  statement: IsSymmetric (msymm σ R μ)
  proof: rename_msymm _ _ μ

中文:
定理 msymm_isSymmetric
  条件: (μ : n.分拆)
  结论: IsSymmetric (msymm σ R μ)
  证明: rename_msymm _ _ μ

Depends on / 依赖: rename_msymm
-/
theorem msymm_isSymmetric (μ : n.Partition) : IsSymmetric (msymm σ R μ) :=
  rename_msymm _ _ μ

end MonomialSymmetric

end MvPolynomial
