/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Descend finiteness along quotients by nilpotent ideals -/

public section

open TensorProduct

/--
lemma `Module.finite_of_surjective_of_ker_le_nilradical` / 引理 `Module.finite_of_surjective_of_ker_le_nilradical`

English:
lemma Module.finite_of_surjective_of_ker_le_nilradical
  proof: by
  have : Module.Finite R (S ⧸ RingHom.ker f) :=
    let e := Ideal.quotientKerAlgEquivOfSurjective hf₁
    .of_surjective e.symm.toLinearMap e.symm.surjective
  generalize hI : RingHom.ker f = I at *
  suffices forall i, Module.Finite R (S ⧸ I ^ i) by
    obtain ⟨n, hn : _ = ⊥⟩ := hf₃.isNilpotent

中文:
引理 Module.finite_of_surjective_of_ker_le_nilradical
  证明: by
  have : Module.Finite R (S ⧸ RingHom.ker f) :=
    let e := Ideal.quotientKerAlgEquivOfSurjective hf₁
    .of_surjective e.symm.toLinearMap e.symm.surjective
  generalize hI : RingHom.ker f = I at *
  suffices forall i, Module.Finite R (S ⧸ I ^ i) by
    obtain ⟨n, hn : _ = ⊥⟩ := hf₃.isNilpotent

Depends on / 依赖: AlgEquiv, AlgEquiv.quotientBot, Finite, Ideal.one_eq_top, Ideal.quotientKerAlgEquivOfSurjective, Module, Module.Finite, RingHom, RingHom.ker, e.surjective, e.symm.surjective, e.symm.toLinearMap, e.toLinearMap, generalize, infer_instan, isNilpotent_iff_le_nilradical, isNilpotent_iff_le_nilradical.mpr, of_surjective, one_eq_top, pow_zero
-/
lemma Module.finite_of_surjective_of_ker_le_nilradical
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R T] (f : S ->ₐ[R] T)
    (hf₁ : Function.Surjective f) (hf₂ : RingHom.ker f <= nilradical S)
    (hf₃ : (RingHom.ker f).FG) :
    Module.Finite R S := by
  have : Module.Finite R (S ⧸ RingHom.ker f) :=
    let e := Ideal.quotientKerAlgEquivOfSurjective hf₁
    .of_surjective e.symm.toLinearMap e.symm.surjective
  generalize hI : RingHom.ker f = I at *
  suffices forall i, Module.Finite R (S ⧸ I ^ i) by
    obtain ⟨n, hn : _ = ⊥⟩ := hf₃.isNilpotent_iff_le_nilradical.mpr hf₂
    let e : (S ⧸ I ^ n) ≃ₐ[R] S := hn ▸ (AlgEquiv.quotientBot R S)
    exact .of_surjective e.toLinearMap e.surjective
  intro n
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; infer_instance
  | succ n IH =>
    let φ : (S ⧸ I ^ (n + 1)) ->ₐ[S] S ⧸ I ^ n :=
      Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right n.le_succ)
    have hφ : Function.Surjective φ :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
    have hφ' : φ.toLinearMap ∘ₗ (I ^ (n + 1)).mkQ = (I ^ n).mkQ := rfl
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (φ.toLinearMap.restrictScalars R) ?_ ?_⟩
    · simpa [LinearMap.range_eq_top_of_surjective (φ.toLinearMap.restrictScalars R) hφ] using
        Module.Finite.fg_top
    · have : Module.Finite R ((S ⧸ I) otimes[S] ↑(I ^ n)) := by
        have : Module.Finite S ↑(I ^ n) := .of_fg (.pow hf₃ _)
        exact .trans (S ⧸ I) _
      let ψ : (S ⧸ I) otimes[S] ↑(I ^ n) ->ₗ[S] (S ⧸ I ^ (n + 1)) := by
        refine ?_ ∘ₗ (TensorProduct.quotTensorEquivQuotSMul _ I).toLinearMap
        refine Submodule.liftQ _ ((Submodule.mkQ _).comp (I ^ n).subtype) ?_
        rw [LinearMap.ker_comp]; rw [← Submodule.map_le_map_iff_of_injective (I ^ n).subtype_injective]; rw [Submodule.map_smul'']; rw [Submodule.map_comap_eq]
        simpa [pow_succ'] using Ideal.mul_le_right (I := I) (J := I ^ n)
      convert! Module.Finite.fg_top.map (ψ.restrictScalars R) using 1
      suffices LinearMap.ker φ.toLinearMap = Submodule.map (I ^ (n + 1)).mkQ (I ^ n) by
        simpa [LinearMap.range_restrictScalars, ψ, LinearMap.range_comp, Submodule.range_liftQ]
      apply Submodule.comap_injective_of_surjective (I ^ (n + 1)).mkQ_surjective
      simpa [← LinearMap.ker_comp, hφ'] using Ideal.pow_le_pow_right n.le_succ
