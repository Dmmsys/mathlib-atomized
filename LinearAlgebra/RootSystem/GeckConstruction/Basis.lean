/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basis.Base
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-!
# The basis obtained from Geck's construction of Lie algebras from root systems

The Geck construction of a Lie algebra associated to a root system,
`RootPairing.GeckConstruction.lieAlgebra`, yields a simple Lie algebra with distinguished basis
which we construct here.

## Main definitions / results:

* `RootPairing.GeckConstruction.basis`: the Geck construction yields a basis.
* `RootPairing.GeckConstruction.equivRootSystem`: up to equivalence,
  `LieAlgebra.IsKilling.rootSystem` is left inverse to `RootPairing.GeckConstruction.lieAlgebra`.

-/

@[expose] public section

noncomputable section

open Set

namespace RootPairing.GeckConstruction

variable {ι K M N : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] [P.IsRootSystem]
  (b : P.Base)

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: :
  body: b.cartanMatrix
  h i := ⟨h i, h_mem_lieAlgebra i⟩
  e i := ⟨e i, e_mem_lieAlgebra i⟩
  f i := ⟨f i, f_mem_lieAlgebra i⟩
  cartan_eq_lieSpan := by
    rw [cartanSubalgebra']; rw [cartanSubalgebra_eq_lieSpan]; rw [← LieSubalgebra.comap_lieSpan_range_eq]
    rfl
  nondegen := b.cartanMatrix_nondegenera

中文:
定义 basis
  签名: :
  定义体: b.cartanMatrix
  h i := ⟨h i, h_mem_lieAlgebra i⟩
  e i := ⟨e i, e_mem_lieAlgebra i⟩
  f i := ⟨f i, f_mem_lieAlgebra i⟩
  cartan_eq_lieSpan := by
    rw [cartanSubalgebra']; rw [cartanSubalgebra_eq_lieSpan]; rw [← LieSubalgebra.comap_lieSpan_range_eq]
    rfl
  nondegen := b.cartanMatrix_nondegenera

Depends on / 依赖: b.cartanMatrix, cartanMatrix
-/
def basis :
    LieAlgebra.Basis b.support (cartanSubalgebra' b) where
  A := b.cartanMatrix
  h i := ⟨h i, h_mem_lieAlgebra i⟩
  e i := ⟨e i, e_mem_lieAlgebra i⟩
  f i := ⟨f i, f_mem_lieAlgebra i⟩
  cartan_eq_lieSpan := by
    rw [cartanSubalgebra']; rw [cartanSubalgebra_eq_lieSpan]; rw [← LieSubalgebra.comap_lieSpan_range_eq]
    rfl
  nondegen := b.cartanMatrix_nondegenerate
  linInd := by
    apply LinearIndependent.of_comp (lieAlgebra b).subtype
    exact linearIndependent_h b
  sl2 i :=
    let t := isSl2Triple i
    { h_ne_zero := by simp [Subtype.ext_iff, t.h_ne_zero]
      lie_e_f := by simp [Subtype.ext_iff, t.lie_e_f]
      lie_h_e_nsmul := by simp [Subtype.ext_iff, t.lie_h_e_nsmul]
      lie_h_f_nsmul := by simp [Subtype.ext_iff, t.lie_h_f_nsmul] }
  lie_h_h i j := by simp [Subtype.ext_iff, lie_h_h]
  lie_h_e i j := by simp [Subtype.ext_iff, lie_h_e]
  lie_h_f i j := by simp [Subtype.ext_iff, lie_h_f]
  lie_e_f_ne i j hij := by simp [Subtype.ext_iff, lie_e_f_ne hij]
  span_ef := by
    let h₀ (i : b.support) : lieAlgebra b := ⟨h i, h_mem_lieAlgebra i⟩
    let e₀ (i : b.support) : lieAlgebra b := ⟨e i, e_mem_lieAlgebra i⟩
    let f₀ (i : b.support) : lieAlgebra b := ⟨f i, f_mem_lieAlgebra i⟩
    change LieSubalgebra.lieSpan K (lieAlgebra b) (range e₀ union range f₀) = ⊤
    suffices LieSubalgebra.lieSpan K (lieAlgebra b) (range e₀ union range f₀) =
        LieSubalgebra.lieSpan K (lieAlgebra b) (range h₀ union range e₀ union range f₀) by
      have hr : range h₀ union range e₀ union range f₀ = Subtype.val ⁻¹' (range h union range e union range f) := by
        aesop
      rw [this]; rw [hr]
      exact LieSubalgebra.lieSpan_lieSpan_coe_preimage
    simp only [union_assoc]
    refine le_antisymm (LieSubalgebra.lieSpan_mono <| by simp) ?_
    rw [LieSubalgebra.lieSpan_le]
    refine union_subset ?_ LieSubalgebra.subset_lieSpan
    rintro - ⟨i, rfl⟩
    have hef : h₀ i = ⁅e₀ i, f₀ i⁆ := by ext1; simp [h₀, e₀, f₀, (isSl2Triple i).lie_e_f]
    rw [hef]
    apply LieSubalgebra.lie_mem <;>
exact LieSubalgebra.subset_lieSpan by simp

/--
lemma `basis_A_eq` / 引理 `basis_A_eq`

English:
lemma basis_A_eq
  statement: (basis b).A = b.cartanMatrix
  proof: rfl

中文:
引理 basis_A_eq
  结论: (basis b).A = b.cartanMatrix
  证明: rfl
-/
@[simp] lemma basis_A_eq : (basis b).A = b.cartanMatrix := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cartanSubalgebra' b).IsCartanSubalgebra
  body: (basis b).isCartanSubalgebra

中文:
实例 :
  签名: (cartanSubalgebra' b).IsCartanSubalgebra
  定义体: (basis b).isCartanSubalgebra

Depends on / 依赖: isCartanSubalgebra
-/
instance : (cartanSubalgebra' b).IsCartanSubalgebra := (basis b).isCartanSubalgebra

open LieAlgebra.IsKilling in
/--
Definition of `equivRootSystem` / `equivRootSystem` 的定义

English:
definition equivRootSystem
  signature: [IsAlgClosed K]
  body: b.equivOfCartanMatrixEq _ (basis b).baseSupportEquiv by simp [(basis b).cartanMatrix_base_eq]

中文:
定义 equivRootSystem
  签名: [IsAlgClosed K]
  定义体: b.equivOfCartanMatrixEq _ (basis b).baseSupportEquiv by simp [(basis b).cartanMatrix_base_eq]

Depends on / 依赖: b.equivOfCartanMatrixEq, baseSupportEquiv, cartanMatrix_base_eq, equivOfCartanMatrixEq
-/
def equivRootSystem [IsAlgClosed K] :
    P.Equiv (rootSystem (cartanSubalgebra' b)) :=
b.equivOfCartanMatrixEq _ (basis b).baseSupportEquiv by simp [(basis b).cartanMatrix_base_eq]

end RootPairing.GeckConstruction
