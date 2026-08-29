/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Tensor products of dual spaces

## Main definitions

* `PiTensorProduct.dualDistrib`: The canonical linear map from `⨂[R] i, Dual R (M i)` to
  `Dual R (⨂[R] i, M i)`, sending `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the linear equivalence `⨂[R] i, R →ₗ R` given by multiplication.

* `PiTensorProduct.dualDistribEquiv`: A linear equivalence between `⨂[R] i, Dual R (M i)`
  and `Dual R (⨂[R] i, M i)` when all `M i` are finite free modules. If
  `f : (i : ι) → Dual R (M i)`, then this equivalence sends `⨂ₜ[R] i, f i` to the composition of
  `PiTensorProduct.map f` with the natural isomorphism `⨂[R] i, R ≃ R` given by multiplication.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct LinearMap Module TensorProduct

variable {ι : Type*}

section SemiRing

variable {R : Type*} {M : ι -> Type*} [CommSemiring R] [Π i, AddCommMonoid (M i)]
  [Π i, Module R (M i)]

/--
Definition of `dualDistrib` / `dualDistrib` 的定义

English:
definition dualDistrib
  signature: [Finite ι]
  body: haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

@[simp]

中文:
定义 dualDistrib
  签名: [有限 ι]
  定义体: haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

@[simp]

Depends on / 依赖: Fintype, Fintype.ofFinite, LinearMap, LinearMap.compRight, compRight, constantBaseRingEquiv, ofFinite, piTensorHomMap, toLinearMap
-/
noncomputable def dualDistrib [Finite ι] : (⨂[R] i, Dual R (M i)) ->ₗ[R] Dual R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  (LinearMap.compRight _ (constantBaseRingEquiv ι R).toLinearMap) ∘ₗ piTensorHomMap

@[simp]
/--
theorem `dualDistrib_apply` / 定理 `dualDistrib_apply`

English:
theorem dualDistrib_apply
  given: [Fintype ι] (f : Π i, Dual R (M i)) (m : Π i, M i)
  proof: by
  rw [dualDistrib]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

中文:
定理 dualDistrib_apply
  条件: [有限类型 ι] (f : Π i, 对偶 R (M i)) (m : Π i, M i)
  证明: by
  rw [dualDistrib]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

Depends on / 依赖: Fintype, Fintype.ofFinite, Subsingleton, Subsingleton.elim, dualDistrib, ofFinite
-/
theorem dualDistrib_apply [Fintype ι] (f : Π i, Dual R (M i)) (m : Π i, M i) :
    dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i) := by
  rw [dualDistrib]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

end SemiRing

section Ring

variable {R : Type*} {κ : ι -> Type*} {M : ι -> Type*} [CommRing R] [Π i, AddCommGroup (M i)]
  [Π i, Module R (M i)]

open scoped Classical in
/--
Definition of `dualDistribInvOfBasis` / `dualDistribInvOfBasis` 的定义

English:
definition dualDistribInvOfBasis
  signature: [Finite ι] [forall i, Finite (κ i)]
  body: haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R Nat _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

中文:
定义 dualDistribInvOfBasis
  签名: [有限 ι] [对任意 i, 有限 (κ i)]
  定义体: haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R Nat _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

Depends on / 依赖: Fintype, Fintype.ofFinite, dualBasis, ofFinite, ringLmapEquivSelf
-/
noncomputable def dualDistribInvOfBasis [Finite ι] [forall i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    Dual R (⨂[R] i, M i) ->ₗ[R] ⨂[R] i, Dual R (M i) :=
  haveI := Fintype.ofFinite ι
  haveI := fun i => Fintype.ofFinite (κ i)
  ∑ p : (Π i, κ i), (ringLmapEquivSelf R Nat _).symm (⨂ₜ[R] i, (b i).dualBasis (p i)) ∘ₗ
    (applyₗ (⨂ₜ[R] i, b i (p i)))

open scoped Classical in
@[simp]
/--
theorem `dualDistribInvOfBasis_apply` / 定理 `dualDistribInvOfBasis_apply`

English:
theorem dualDistribInvOfBasis_apply
  statement: [Fintype ι] [forall i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i))
  proof: by
  simp only [dualDistribInvOfBasis, Basis.coe_dualBasis, ringLmapEquivSelf_symm_apply, coe_sum,
    coe_comp, coe_smulRight, End.one_apply, Finset.sum_apply, Function.comp_apply,
    applyₗ_apply_apply]
  convert! rfl

中文:
定理 dualDistribInvOfBasis_apply
  结论: [有限类型 ι] [对任意 i, 有限类型 (κ i)] (b : Π i, 基 (κ i) R (M i))
  证明: by
  simp only [dualDistribInvOfBasis, Basis.coe_dualBasis, ringLmapEquivSelf_symm_apply, coe_sum,
    coe_comp, coe_smulRight, End.one_apply, Finset.sum_apply, Function.comp_apply,
    applyₗ_apply_apply]
  convert! rfl

Depends on / 依赖: Basis.coe_dualBasis, End.one_apply, Finset, Finset.sum_apply, Function, Function.comp_apply, coe_comp, coe_dualBasis, coe_smulRight, coe_sum, comp_apply, convert, dualDistribInvOfBasis, one_apply, ringLmapEquivSelf_symm_apply, sum_apply
-/
theorem dualDistribInvOfBasis_apply [Fintype ι] [forall i, Fintype (κ i)] (b : Π i, Basis (κ i) R (M i))
    (f : Dual R (⨂[R] i, M i)) : dualDistribInvOfBasis b f =
    ∑ p : (Π i, κ i), f (⨂ₜ[R] i, b i (p i)) • (⨂ₜ[R] i, (b i).dualBasis (p i)) := by
  simp only [dualDistribInvOfBasis, Basis.coe_dualBasis, ringLmapEquivSelf_symm_apply, coe_sum,
    coe_comp, coe_smulRight, End.one_apply, Finset.sum_apply, Function.comp_apply,
    applyₗ_apply_apply]
  convert! rfl

/--
theorem `dualDistrib_dualDistribInvOfBasis_left_inverse` / 定理 `dualDistrib_dualDistribInvOfBasis_left_inverse`

English:
theorem dualDistrib_dualDistribInvOfBasis_left_inverse
  statement: [Finite ι] [forall i, Finite (κ i)]
  proof: by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p => ?_)
  refine (Basis.piTensorProduct b).ext (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

中文:
定理 dualDistrib_dualDistribInvOfBasis_left_inverse
  结论: [有限 ι] [对任意 i, 有限 (κ i)]
  证明: by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p => ?_)
  refine (Basis.piTensorProduct b).ext (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

Depends on / 依赖: Basis.piTensorProduct, Finsupp, Finsupp.single_apply, Fintype, Fintype.ofFinite, Fintype.prod_ite_zero, classical, dualBasis, dualBasis.ext, funext_iff, ofFinite, piTensorProduct, prod_ite_zero, single_apply
-/
theorem dualDistrib_dualDistribInvOfBasis_left_inverse [Finite ι] [forall i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistrib) ∘ₗ (dualDistribInvOfBasis b) = LinearMap.id := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct b).dualBasis.ext (fun p => ?_)
  refine (Basis.piTensorProduct b).ext (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

/--
theorem `dualDistrib_dualDistribInvOfBasis_right_inverse` / 定理 `dualDistrib_dualDistribInvOfBasis_right_inverse`

English:
theorem dualDistrib_dualDistribInvOfBasis_right_inverse
  statement: [Finite ι] [forall i, Finite (κ i)]
  proof: by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext (fun p => ?_)
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

中文:
定理 dualDistrib_dualDistribInvOfBasis_right_inverse
  结论: [有限 ι] [对任意 i, 有限 (κ i)]
  证明: by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext (fun p => ?_)
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

Depends on / 依赖: Basis.piTensorProduct, Finsupp, Finsupp.single_apply, Fintype, Fintype.ofFinite, Fintype.prod_ite_zero, classical, dualBasis, ext_elem, funext_iff, ofFinite, piTensorProduct, prod_ite_zero, single_apply
-/
theorem dualDistrib_dualDistribInvOfBasis_right_inverse [Finite ι] [forall i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) :
    (dualDistribInvOfBasis b) ∘ₗ dualDistrib = LinearMap.id := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (κ i)
  classical
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext (fun p => ?_)
  refine (Basis.piTensorProduct (fun i => (b i).dualBasis)).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)`
given bases for all `M i`. If `f : (i : ι) → Dual R (s i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simps!]
/--
Definition of `dualDistribEquivOfBasis` / `dualDistribEquivOfBasis` 的定义

English:
definition dualDistribEquivOfBasis
  signature: [Finite ι] [forall i, Finite (κ i)]
  body: LinearEquiv.ofLinearMap dualDistrib (dualDistribInvOfBasis b)
    (dualDistrib_dualDistribInvOfBasis_left_inverse _)
    (dualDistrib_dualDistribInvOfBasis_right_inverse _)

中文:
定义 dualDistribEquivOfBasis
  签名: [有限 ι] [对任意 i, 有限 (κ i)]
  定义体: LinearEquiv.ofLinearMap dualDistrib (dualDistribInvOfBasis b)
    (dualDistrib_dualDistribInvOfBasis_left_inverse _)
    (dualDistrib_dualDistribInvOfBasis_right_inverse _)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, dualDistrib, dualDistribInvOfBasis, dualDistrib_dualDistribInvOfBasis_left_inverse, dualDistrib_dualDistribInvOfBasis_right_inverse, ofLinearMap
-/
noncomputable def dualDistribEquivOfBasis [Finite ι] [forall i, Finite (κ i)]
    (b : Π i, Basis (κ i) R (M i)) : (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  LinearEquiv.ofLinearMap dualDistrib (dualDistribInvOfBasis b)
    (dualDistrib_dualDistribInvOfBasis_left_inverse _)
    (dualDistrib_dualDistribInvOfBasis_right_inverse _)

variable [Π i, Module.Finite R (M i)] [Π i, Module.Free R (M i)]

/-- A linear equivalence between `⨂[R] i, Dual R (M i)` and `Dual R (⨂[R] i, M i)` when all
`M i` are finite free modules. If `f : (i : ι) → Dual R (M i)`, then this equivalence sends
`⨂ₜ[R] i, f i` to the composition of `PiTensorProduct.map f` with the natural
isomorphism `⨂[R] i, R ≃ R` given by multiplication (`constantBaseRingEquiv`). -/
@[simp]
/--
Definition of `dualDistribEquiv` / `dualDistribEquiv` 的定义

English:
definition dualDistribEquiv
  signature: [Finite ι]
  body: dualDistribEquivOfBasis (fun i => Module.Free.chooseBasis R (M i))

中文:
定义 dualDistribEquiv
  签名: [有限 ι]
  定义体: dualDistribEquivOfBasis (fun i => Module.Free.chooseBasis R (M i))

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, dualDistribEquivOfBasis
-/
noncomputable def dualDistribEquiv [Finite ι] :
    (⨂[R] i, Dual R (M i)) ≃ₗ[R] Dual R (⨂[R] i, M i) :=
  dualDistribEquivOfBasis (fun i => Module.Free.chooseBasis R (M i))

end Ring

end PiTensorProduct
