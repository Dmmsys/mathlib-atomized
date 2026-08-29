/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Finsupp.SMul

/-!
# `Finsupp`s and sum/product types

This file contains results about modules involving `Finsupp` and sum/product/sigma types.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section Sum

variable (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sumFinsuppEquivProdFinsupp`. -/
@[simps apply symm_apply]
/--
Definition of `sumFinsuppLEquivProdFinsupp` / `sumFinsuppLEquivProdFinsupp` 的定义

English:
definition sumFinsuppLEquivProdFinsupp
  signature: {α β : Type*}
  body: { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        simp only [AddEquiv.toFun_eq_coe, Prod.smul_fst, Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }

中文:
定义 sumFinsuppLEquivProdFinsupp
  签名: {α β : 类型}
  定义体: { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        simp only [AddEquiv.toFun_eq_coe, Prod.smul_fst, Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }

Depends on / 依赖: AddEquiv, AddEquiv.toFun_eq_coe, Prod.smul_fst, Prod.smul_snd, RingHom, RingHom.id_apply, fst_sumFinsuppAddEquivProdFinsupp, id_apply, intros, map_smul, smul_apply, smul_fst, smul_snd, snd_sumFinsuppAddEquivProdFinsupp, sumFinsuppAddEquivProdFinsupp, toFun_eq_coe
-/
def sumFinsuppLEquivProdFinsupp {α β : Type*} : (α oplus β ->₀ M) ≃ₗ[R] (α ->₀ M) × (β ->₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        simp only [AddEquiv.toFun_eq_coe, Prod.smul_fst, Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }

/--
theorem `fst_sumFinsuppLEquivProdFinsupp` / 定理 `fst_sumFinsuppLEquivProdFinsupp`

English:
theorem fst_sumFinsuppLEquivProdFinsupp
  given: {α β : Type*} (f : α oplus β ->₀ M) (x : α)
  proof: rfl

中文:
定理 fst_sumFinsuppLEquivProdFinsupp
  条件: {α β : 类型} (f : α oplus β ->₀ M) (x : α)
  证明: rfl
-/
theorem fst_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (x : α) :
    (sumFinsuppLEquivProdFinsupp R f).1 x = f (Sum.inl x) :=
  rfl

/--
theorem `snd_sumFinsuppLEquivProdFinsupp` / 定理 `snd_sumFinsuppLEquivProdFinsupp`

English:
theorem snd_sumFinsuppLEquivProdFinsupp
  given: {α β : Type*} (f : α oplus β ->₀ M) (y : β)
  proof: rfl

中文:
定理 snd_sumFinsuppLEquivProdFinsupp
  条件: {α β : 类型} (f : α oplus β ->₀ M) (y : β)
  证明: rfl
-/
theorem snd_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (y : β) :
    (sumFinsuppLEquivProdFinsupp R f).2 y = f (Sum.inr y) :=
  rfl

/--
theorem `sumFinsuppLEquivProdFinsupp_symm_inl` / 定理 `sumFinsuppLEquivProdFinsupp_symm_inl`

English:
theorem sumFinsuppLEquivProdFinsupp_symm_inl
  given: {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (x : α)
  proof: rfl

中文:
定理 sumFinsuppLEquivProdFinsupp_symm_inl
  条件: {α β : 类型} (fg : (α ->₀ M) × (β ->₀ M)) (x : α)
  证明: rfl
-/
theorem sumFinsuppLEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (x : α) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inl x) = fg.1 x :=
  rfl

/--
theorem `sumFinsuppLEquivProdFinsupp_symm_inr` / 定理 `sumFinsuppLEquivProdFinsupp_symm_inr`

English:
theorem sumFinsuppLEquivProdFinsupp_symm_inr
  given: {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (y : β)
  proof: rfl

中文:
定理 sumFinsuppLEquivProdFinsupp_symm_inr
  条件: {α β : 类型} (fg : (α ->₀ M) × (β ->₀ M)) (y : β)
  证明: rfl
-/
theorem sumFinsuppLEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α ->₀ M) × (β ->₀ M)) (y : β) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section Sigma

variable {η : Type*} [Fintype η] {ιs : η -> Type*} [Zero α]
variable (R)

/--
Definition of `sigmaFinsuppLEquivPiFinsupp` / `sigmaFinsuppLEquivPiFinsupp` 的定义

English:
definition sigmaFinsuppLEquivPiFinsupp
  signature: {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
  body: { sigmaFinsuppAddEquivPiFinsupp with
    map_smul' := fun c f => by
      ext
      simp }

@[simp]

中文:
定义 sigmaFinsuppLEquivPiFinsupp
  签名: {M : 类型} {ιs : η -> 类型} [AddCommMonoid M]
  定义体: { sigmaFinsuppAddEquivPiFinsupp with
    map_smul' := fun c f => by
      ext
      simp }

@[simp]

Depends on / 依赖: map_smul, sigmaFinsuppAddEquivPiFinsupp
-/
noncomputable def sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
    [Module R M] : ((Σ j, ιs j) ->₀ M) ≃ₗ[R] (j : _) -> (ιs j ->₀ M) :=
  { sigmaFinsuppAddEquivPiFinsupp with
    map_smul' := fun c f => by
      ext
      simp }

@[simp]
/--
theorem `sigmaFinsuppLEquivPiFinsupp_apply` / 定理 `sigmaFinsuppLEquivPiFinsupp_apply`

English:
theorem sigmaFinsuppLEquivPiFinsupp_apply
  statement: {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
  proof: rfl

@[simp]

中文:
定理 sigmaFinsuppLEquivPiFinsupp_apply
  结论: {M : 类型} {ιs : η -> 类型} [AddCommMonoid M]
  证明: rfl

@[simp]
-/
theorem sigmaFinsuppLEquivPiFinsupp_apply {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
    [Module R M] (f : (Σ j, ιs j) ->₀ M) (j i) : sigmaFinsuppLEquivPiFinsupp R f j i = f ⟨j, i⟩ :=
  rfl

@[simp]
/--
theorem `sigmaFinsuppLEquivPiFinsupp_symm_apply` / 定理 `sigmaFinsuppLEquivPiFinsupp_symm_apply`

English:
theorem sigmaFinsuppLEquivPiFinsupp_symm_apply
  statement: {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
  proof: rfl

中文:
定理 sigmaFinsuppLEquivPiFinsupp_symm_apply
  结论: {M : 类型} {ιs : η -> 类型} [AddCommMonoid M]
  证明: rfl
-/
theorem sigmaFinsuppLEquivPiFinsupp_symm_apply {M : Type*} {ιs : η -> Type*} [AddCommMonoid M]
    [Module R M] (f : (j : _) -> (ιs j ->₀ M)) (ji) :
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm f ji = f ji.1 ji.2 :=
  rfl

end Sigma

end Finsupp
