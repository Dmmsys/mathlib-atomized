/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.SubtypeNeLift
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generators of multiple tensor products

Given a finite family of `R`-modules `M i`, if we have, for each `i`,
a family of generators of the module `M i`, then the tensor products
of these elements generate `⨂[R] i, M i`.

In `LinearAlgebra.PiTensorProduct.Finite`, we deduce that if the modules `M i`
are finitely generated, then so is `⨂[R] i, M i`.

-/

@[expose] public section

open TensorProduct

namespace PiTensorProduct

variable (R : Type*)

section equivPiTensorComplSingletonTensor

variable {ι : Type*} [DecidableEq ι] (M : ι -> Type*)
  [CommSemiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]

/--
Definition of `equivPiTensorComplSingletonTensor` / `equivPiTensorComplSingletonTensor` 的定义

English:
definition equivPiTensorComplSingletonTensor
  signature: (i₀ : ι)
  body: (reindex R (s := M) (Equiv.subtypeNeSumPUnit.{0} i₀).symm).trans
    ((tmulEquivDep R (fun i => M (Equiv.subtypeNeSumPUnit i₀ i))).symm.trans
      (LinearEquiv.lTensor _ (subsingletonEquiv Unit.unit)))

中文:
定义 equivPiTensorComplSingletonTensor
  签名: (i₀ : ι)
  定义体: (reindex R (s := M) (Equiv.subtypeNeSumPUnit.{0} i₀).symm).trans
    ((tmulEquivDep R (fun i => M (Equiv.subtypeNeSumPUnit i₀ i))).symm.trans
      (LinearEquiv.lTensor _ (subsingletonEquiv Unit.unit)))

Depends on / 依赖: Equiv.subtypeNeSumPUnit, LinearEquiv, LinearEquiv.lTensor, Unit.unit, lTensor, reindex, subsingletonEquiv, subtypeNeSumPUnit, symm.trans, tmulEquivDep
-/
noncomputable def equivPiTensorComplSingletonTensor (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R] ((⨂[R] (i : ({i₀}ᶜ : Set ι)), M i) otimes[R] M i₀) :=
  (reindex R (s := M) (Equiv.subtypeNeSumPUnit.{0} i₀).symm).trans
    ((tmulEquivDep R (fun i => M (Equiv.subtypeNeSumPUnit i₀ i))).symm.trans
      (LinearEquiv.lTensor _ (subsingletonEquiv Unit.unit)))

variable (i₀ : ι)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `equivPiTensorComplSingletonTensor_tprod` / 引理 `equivPiTensorComplSingletonTensor_tprod`

English:
lemma equivPiTensorComplSingletonTensor_tprod
  given: (i₀ : ι) (m : forall i, M i)
  proof: by
  dsimp [equivPiTensorComplSingletonTensor]
  have : (reindex R M (Equiv.subtypeNeSumPUnit.{0} i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((Equiv.subtypeNeSumPUnit.{0} i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  rw [dsimp% this]; rw [dsimp% tmulEquivDep_symm_apply R
    (fun i => M ((Equiv.subtypeNeSumPUnit.{0} i₀) i))]
  exact (LinearEquiv.lTensor_tmul _ _ _ _).trans (by congr; simp)

中文:
引理 equivPiTensorComplSingletonTensor_tprod
  条件: (i₀ : ι) (m : 对任意 i, M i)
  证明: by
  dsimp [equivPiTensorComplSingletonTensor]
  have : (reindex R M (Equiv.subtypeNeSumPUnit.{0} i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((Equiv.subtypeNeSumPUnit.{0} i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  rw [dsimp% this]; rw [dsimp% tmulEquivDep_symm_apply R
    (fun i => M ((Equiv.subtypeNeSumPUnit.{0} i₀) i))]
  exact (LinearEquiv.lTensor_tmul _ _ _ _).trans (by congr; simp)

Depends on / 依赖: Equiv.subtypeNeSumPUnit, Equiv.symm_symm, LinearEquiv, LinearEquiv.lTensor_tmul, equivPiTensorComplSingletonTensor, lTensor_tmul, reindex, reindex_tprod, simp_rw, subtypeNeSumPUnit, symm_symm, tmulEquivDep_symm_apply
-/
lemma equivPiTensorComplSingletonTensor_tprod (i₀ : ι) (m : forall i, M i) :
    equivPiTensorComplSingletonTensor R M i₀ (⨂ₜ[R] i, m i) =
      (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) otimesₜ m i₀:= by
  dsimp [equivPiTensorComplSingletonTensor]
  have : (reindex R M (Equiv.subtypeNeSumPUnit.{0} i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((Equiv.subtypeNeSumPUnit.{0} i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  rw [dsimp% this]; rw [dsimp% tmulEquivDep_symm_apply R
    (fun i => M ((Equiv.subtypeNeSumPUnit.{0} i₀) i))]
  exact (LinearEquiv.lTensor_tmul _ _ _ _).trans (by congr; simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `equivPiTensorComplSingletonTensor_symm_tmul` / 引理 `equivPiTensorComplSingletonTensor_symm_tmul`

English:
lemma equivPiTensorComplSingletonTensor_symm_tmul
  statement: (i₀ : ι)
  proof: by
  apply (equivPiTensorComplSingletonTensor R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivPiTensorComplSingletonTensor_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq _ _ _ _ hi]
  rfl

中文:
引理 equivPiTensorComplSingletonTensor_symm_tmul
  结论: (i₀ : ι)
  证明: by
  apply (equivPiTensorComplSingletonTensor R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivPiTensorComplSingletonTensor_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq _ _ _ _ hi]
  rfl

Depends on / 依赖: Function, Function.subtypeNeLift_of_neq, Function.subtypeNeLift_self, LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, equivPiTensorComplSingletonTensor, equivPiTensorComplSingletonTensor_tprod, injective, subtypeNeLift_of_neq, subtypeNeLift_self
-/
lemma equivPiTensorComplSingletonTensor_symm_tmul (i₀ : ι)
    (m : forall (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀) :
    (equivPiTensorComplSingletonTensor R M i₀).symm
      ((⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) otimesₜ x) =
    (⨂ₜ[R] i, Function.subtypeNeLift i₀ m x i) := by
  apply (equivPiTensorComplSingletonTensor R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivPiTensorComplSingletonTensor_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq _ _ _ _ hi]
  rfl

end equivPiTensorComplSingletonTensor

variable {R} {ι : Type*} [Finite ι] {M : ι -> Type*} {N : Type*} {γ : ι -> Type*}

section AddCommMonoid

variable [CommSemiring R] [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  [AddCommMonoid N] [Module R N] {g : ⦃i : ι⦄ -> (j : γ i) -> M i}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ext_of_span_eq_top` / 引理 `ext_of_span_eq_top`

English:
lemma ext_of_span_eq_top
  proof: by
  obtain ⟨n, hι⟩ : exists (n : Nat), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    ext x
have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right Finite.not_infinite ‹_›
    obtain rfl : x = fun i => @g i (isEmptyElim i) := Subsingleton.elim _ _
    apply h
  | succ n hn =>
    classical
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    have i₀ : ι := Classical.arbitrary _
    let e := (equivPiTensorComplSingletonTensor R M i₀).trans (TensorProduct.comm _ _ _)
    obtain ⟨ψ, rfl⟩ : exists ψ, φ = LinearMap.comp ψ e.toLinearMap :=
      ⟨φ.comp e.symm.toLinearMap, by ext; simp⟩
    obtain ⟨ψ', rfl⟩ : exists ψ', φ' = LinearMap.comp ψ' e.toLinearMap :=
      ⟨φ'.comp e.symm.toLinearMap, by ext; simp⟩
    dsimp [e] at h
    congr 1
    apply (TensorProduct.lift.equiv _ _ _ _).symm.injective
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (hg i₀)]
    rintro ⟨_, ⟨g₀, rfl⟩⟩
    apply hn (g := fun i (j : γ i.1) => by exact g j)
    · intro
      exact hg _
    · intro j
      have : (g g₀ otimesₜ[R] (tprod R) fun i => g (j i)) =
          TensorProduct.comm R _ _ ((equivPiTensorComplSingletonTensor R M i₀)
            (⨂ₜ[R] (i : ι), g (Function.subtypeNeLift i₀ j g₀ i))) := by
        simp only [equivPiTensorComplSingletonTensor_tprod, Function.subtypeNeLift_self]
        congr
        ext ⟨x, hx⟩
        congr
        rw [Function.subtypeNeLift_of_neq _ _ _ _ (by assumption)]
        rfl
      simpa only [lift.equiv_symm_apply, this] using h (Function.subtypeNeLift i₀ j g₀)
    · exact Set.ncard_compl_of_ncard_eq_add _ (by simpa)

中文:
引理 ext_of_span_eq_top
  证明: by
  obtain ⟨n, hι⟩ : exists (n : Nat), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    ext x
have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right Finite.not_infinite ‹_›
    obtain rfl : x = fun i => @g i (isEmptyElim i) := Subsingleton.elim _ _
    apply h
  | succ n hn =>
    classical
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    have i₀ : ι := Classical.arbitrary _
    let e := (equivPiTensorComplSingletonTensor R M i₀).trans (TensorProduct.comm _ _ _)
    obtain ⟨ψ, rfl⟩ : exists ψ, φ = LinearMap.comp ψ e.toLinearMap :=
      ⟨φ.comp e.symm.toLinearMap, by ext; simp⟩
    obtain ⟨ψ', rfl⟩ : exists ψ', φ' = LinearMap.comp ψ' e.toLinearMap :=
      ⟨φ'.comp e.symm.toLinearMap, by ext; simp⟩
    dsimp [e] at h
    congr 1
    apply (TensorProduct.lift.equiv _ _ _ _).symm.injective
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (hg i₀)]
    rintro ⟨_, ⟨g₀, rfl⟩⟩
    apply hn (g := fun i (j : γ i.1) => by exact g j)
    · intro
      exact hg _
    · intro j
      have : (g g₀ otimesₜ[R] (tprod R) fun i => g (j i)) =
          TensorProduct.comm R _ _ ((equivPiTensorComplSingletonTensor R M i₀)
            (⨂ₜ[R] (i : ι), g (Function.subtypeNeLift i₀ j g₀ i))) := by
        simp only [equivPiTensorComplSingletonTensor_tprod, Function.subtypeNeLift_self]
        congr
        ext ⟨x, hx⟩
        congr
        rw [Function.subtypeNeLift_of_neq _ _ _ _ (by assumption)]
        rfl
      simpa only [lift.equiv_symm_apply, this] using h (Function.subtypeNeLift i₀ j g₀)
    · exact Set.ncard_compl_of_ncard_eq_add _ (by simpa)

Depends on / 依赖: Classical, Classical.arbitrary, Finite, Finite.not_infinite, IsEmpty, Nat.card, Nat.card_eq_zero, Nat.card_pos_iff, Nonempty, Subsingleton, Subsingleton.elim, TensorProduct, TensorProduct.comm, arbitrary, card_eq_zero, card_pos_iff, classical, equivPiTensorComplSingletonTensor, generalizing, isEmptyElim
-/
lemma ext_of_span_eq_top
    (hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) ->ₗ[R] N}
    (h : forall (j : (i : ι) -> γ i),
      φ (tprod _ (fun i => g (j i))) = φ' (tprod _ (fun i => g (j i)))) :
    φ = φ' := by
  obtain ⟨n, hι⟩ : exists (n : Nat), Nat.card ι = n := ⟨_, rfl⟩
  induction n generalizing ι with
  | zero =>
    ext x
have : IsEmpty ι := (Nat.card_eq_zero.1 hι).resolve_right Finite.not_infinite ‹_›
    obtain rfl : x = fun i => @g i (isEmptyElim i) := Subsingleton.elim _ _
    apply h
  | succ n hn =>
    classical
    have : Nonempty ι := ((Nat.card_pos_iff (α := ι)).1 (by omega)).1
    have i₀ : ι := Classical.arbitrary _
    let e := (equivPiTensorComplSingletonTensor R M i₀).trans (TensorProduct.comm _ _ _)
    obtain ⟨ψ, rfl⟩ : exists ψ, φ = LinearMap.comp ψ e.toLinearMap :=
      ⟨φ.comp e.symm.toLinearMap, by ext; simp⟩
    obtain ⟨ψ', rfl⟩ : exists ψ', φ' = LinearMap.comp ψ' e.toLinearMap :=
      ⟨φ'.comp e.symm.toLinearMap, by ext; simp⟩
    dsimp [e] at h
    congr 1
    apply (TensorProduct.lift.equiv _ _ _ _).symm.injective
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (hg i₀)]
    rintro ⟨_, ⟨g₀, rfl⟩⟩
    apply hn (g := fun i (j : γ i.1) => by exact g j)
    · intro
      exact hg _
    · intro j
      have : (g g₀ otimesₜ[R] (tprod R) fun i => g (j i)) =
          TensorProduct.comm R _ _ ((equivPiTensorComplSingletonTensor R M i₀)
            (⨂ₜ[R] (i : ι), g (Function.subtypeNeLift i₀ j g₀ i))) := by
        simp only [equivPiTensorComplSingletonTensor_tprod, Function.subtypeNeLift_self]
        congr
        ext ⟨x, hx⟩
        congr
        rw [Function.subtypeNeLift_of_neq _ _ _ _ (by assumption)]
        rfl
      simpa only [lift.equiv_symm_apply, this] using h (Function.subtypeNeLift i₀ j g₀)
    · exact Set.ncard_compl_of_ncard_eq_add _ (by simpa)

/--
lemma `_root_.MultilinearMap.ext_of_span_eq_top` / 引理 `_root_.MultilinearMap.ext_of_span_eq_top`

English:
lemma _root_.MultilinearMap.ext_of_span_eq_top
  proof: by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j => by simpa using h j)

中文:
引理 _root_.多重线性映射.ext_of_span_eq_top
  证明: by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j => by simpa using h j)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, PiTensorProduct, PiTensorProduct.ext_of_span_eq_top, congr_fun, ext_of_span_eq_top
-/
lemma _root_.MultilinearMap.ext_of_span_eq_top
    (hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : forall (j : (i : ι) -> γ i), φ (fun i => g (j i)) = φ' (fun i => g (j i))) :
    φ = φ' := by
  suffices lift φ = lift φ' by
    ext m
    simpa using DFunLike.congr_fun this (tprod _ m)
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j => by simpa using h j)

end AddCommMonoid

variable [CommRing R] [forall i, AddCommGroup (M i)] [forall i, Module R (M i)]
  [AddCommMonoid N] [Module R N] {g : ⦃i : ι⦄ -> (j : γ i) -> M i}

/--
lemma `submodule_span_eq_top` / 引理 `submodule_span_eq_top`

English:
lemma submodule_span_eq_top
  proof: by
  rw [← (Submodule.span R _).ker_mkQ]; rw [LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j => ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

中文:
引理 submodule_span_eq_top
  证明: by
  rw [← (Submodule.span R _).ker_mkQ]; rw [LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j => ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.ker_eq_top, LinearMap.zero_apply, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.mkQ_apply, Submodule.span, Submodule.subset_span, ext_of_span_eq_top, ker_eq_top, ker_mkQ, mkQ_apply, mk_eq_zero, subset_span, zero_apply
-/
lemma submodule_span_eq_top
    (hg : forall i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) -> γ i) =>
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  rw [← (Submodule.span R _).ker_mkQ]; rw [LinearMap.ker_eq_top]
  refine ext_of_span_eq_top hg (fun j => ?_)
  simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨j, rfl⟩

end PiTensorProduct
