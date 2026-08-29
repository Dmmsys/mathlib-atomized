/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Stability of finiteness conditions in commutative algebra

In this file we show that `Algebra.FiniteType` and `Algebra.FinitePresentation` are
stable under base change.

-/

public section

open scoped TensorProduct

universe w₁ w₂ w₃

variable {R : Type w₁} [CommRing R]
variable {A : Type w₂} [CommRing A] [Algebra R A]
variable (B : Type w₃) [CommRing B] [Algebra R B]

namespace Algebra

namespace FiniteType

/--
theorem `baseChangeAux_surj` / 定理 `baseChangeAux_surj`

English:
theorem baseChangeAux_surj
  given: {σ : Type*} {f : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f)
  proof: by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf

中文:
定理 baseChangeAux_surj
  条件: {σ : 类型} {f : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f)
  证明: by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf

Depends on / 依赖: AlgHom, AlgHom.id, Function, Function.RightInverse.surjective, Function.Surjective, RightInverse, Surjective, TensorProduct, TensorProduct.map, TensorProduct.map_surjective, map_surjective, surjective
-/
theorem baseChangeAux_surj {σ : Type*} {f : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id B B) f) := by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf

/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [hfa : FiniteType R A]
  body: by
  rw [iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use n, AlgHom.comp g (MvPolynomial.algebraTensorAlgEq

中文:
实例 baseChange
  签名: [hfa : FiniteType R A]
  定义体: by
  rw [iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use n, AlgHom.comp g (MvPolynomial.algebraTensorAlgEq

Depends on / 依赖: AlgHom, AlgHom.comp, AlgHom.id, Algebra, Algebra.TensorProduct.map, Function, Function.Surjective, MvPolynomial, MvPolynomial.algebraTensorAlgEquiv, Surjective, TensorProduct, algebraTensorAlgEquiv, baseChangeAux_surj, iff_quotient_mvPolynomial, otimes, symm.toAlgHom, toAlgHom
-/
instance baseChange [hfa : FiniteType R A] : Algebra.FiniteType B (B otimes[R] A) := by
  rw [iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use n, AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  simpa

end FiniteType

namespace FinitePresentation

/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [FinitePresentation R A]
  body: by
  obtain ⟨n, f, hsurj, hfg⟩ := ‹FinitePresentation R A›
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker g = Idea

中文:
实例 baseChange
  签名: [FinitePresentation R A]
  定义体: by
  obtain ⟨n, f, hsurj, hfg⟩ := ‹FinitePresentation R A›
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker g = Idea

Depends on / 依赖: AlgHom, AlgHom.id, Algebra, Algebra.FiniteType.baseChangeAux_surj, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.lTensor_ker, Algebra.TensorProduct.map, FinitePresentation, FiniteType, Function, Function.Surjective, Ideal.FG, Ideal.FG.map, Ideal.map, MvPolynomial, RingHom, RingHom.ker, Surjective, TensorProduct, baseChangeAux_surj
-/
instance baseChange [FinitePresentation R A] : FinitePresentation B (B otimes[R] A) := by
  obtain ⟨n, f, hsurj, hfg⟩ := ‹FinitePresentation R A›
  let g : B otimes[R] MvPolynomial (Fin n) R ->ₐ[B] B otimes[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker g = Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker f) :=
    Algebra.TensorProduct.lTensor_ker f hsurj
  have hfgg : Ideal.FG (RingHom.ker g) := by
    rw [hker_eq]
    exact Ideal.FG.map hfg _
  let g' : MvPolynomial (Fin n) B ->ₐ[B] B otimes[R] A :=
    AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  refine ⟨n, g', ?_, Ideal.fg_ker_comp _ _ ?_ hfgg ?_⟩
  · simp_all [g, g']
  · change Ideal.FG (RingHom.ker (AlgEquiv.symm (MvPolynomial.algebraTensorAlgEquiv R B)))
    simp only [RingHom.ker_equiv]
    exact Submodule.fg_bot
  · simpa using EquivLike.surjective _

end FinitePresentation

end Algebra
