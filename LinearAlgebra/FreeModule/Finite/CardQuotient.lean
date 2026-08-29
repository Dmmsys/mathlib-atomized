/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Xavier Roblot
-/
module

public import Mathlib.Data.Int.Associated
public import Mathlib.Data.Int.NatAbs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Cardinal of quotient of free finite `ℤ`-modules by submodules of full rank

## Main results

* `Submodule.natAbs_det_basis_change`: let `b` be a `ℤ`-basis for a module `M` over `ℤ` and
  let `bN` be a basis for a submodule `N` of the same dimension. Then the cardinal of `M ⧸ N`
  is given by taking the determinant of `bN` over `b`.

-/

public section

open Module Submodule

section Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free Int M] [Module.Finite Int M]

/--
theorem `Submodule.natAbs_det_equiv` / 定理 `Submodule.natAbs_det_equiv`

English:
theorem Submodule.natAbs_det_equiv
  statement: (N : Submodule Int M) {E : Type*} [EquivLike E M N]
  proof: by
  let b := Module.Free.chooseBasis Int M
  -- Since `e : M ≃ₗ[ℤ] N`, the submodule `N` has full rank.
  have h : Module.finrank Int N = Module.finrank Int M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[Int] N).symm.finrank_eq
  -- Use the Smith normal form to choose a nice basis for `N`.
  let a :=

中文:
定理 Submodule.natAbs_det_equiv
  结论: (N : Submodule 整数 M) {E : 类型} [EquivLike E M N]
  证明: by
  let b := Module.Free.chooseBasis Int M
  -- Since `e : M ≃ₗ[ℤ] N`, the submodule `N` has full rank.
  have h : Module.finrank Int N = Module.finrank Int M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[Int] N).symm.finrank_eq
  -- Use the Smith normal form to choose a nice basis for `N`.
  let a :=

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis
-/
theorem Submodule.natAbs_det_equiv (N : Submodule Int M) {E : Type*} [EquivLike E M N]
    [AddEquivClass E M N] (e : E) :
    Int.natAbs
      (LinearMap.det
        (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M ->+ N))) =
      Nat.card (M ⧸ N) := by
  let b := Module.Free.chooseBasis Int M
  -- Since `e : M ≃ₗ[ℤ] N`, the submodule `N` has full rank.
  have h : Module.finrank Int N = Module.finrank Int M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[Int] N).symm.finrank_eq
  -- Use the Smith normal form to choose a nice basis for `N`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[Int] N := b'.equiv ab (Equiv.refl _)
  let f : M ->ₗ[Int] M := N.subtype.comp (e' : M ->ₗ[Int] N)
  let f_apply : forall x, f x = b'.equiv ab (Equiv.refl _) x := fun x => rfl
  suffices (LinearMap.det f).natAbs = Nat.card (M ⧸ N) by
    calc
      _ = (LinearMap.det (N.subtype ∘ₗ
            (AddEquiv.toIntLinearEquiv e : M ≃ₗ[Int] N))).natAbs := rfl
      _ = (LinearMap.det (N.subtype ∘ₗ _)).natAbs :=
            Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
      _ = Nat.card (M ⧸ N) := this
  have ha : forall i, f (b' i) = a i • b' i := by
    intro i
    rw [f_apply]; rw [b'.equiv_apply]; rw [Equiv.refl_apply]
    exact ab_eq i
  calc
    Int.natAbs (LinearMap.det f) = Int.natAbs (LinearMap.toMatrix b' b' f).det := by
      rw [LinearMap.det_toMatrix]
    _ = Int.natAbs (Matrix.diagonal a).det := ?_
    _ = Int.natAbs (∏ i, a i) := by rw [Matrix.det_diagonal]
    _ = ∏ i, Int.natAbs (a i) := map_prod Int.natAbsHom a Finset.univ
    _ = Nat.card (M ⧸ N) := ?_
  -- since `LinearMap.toMatrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  · congr 2; ext i j
    rw [LinearMap.toMatrix_apply]; rw [ha]; rw [map_smul]; rw [Basis.repr_self]; rw [Finsupp.smul_single]; rw [smul_eq_mul]; rw [mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → ℤ)`,
  -- which maps `(M ⧸ N)` to `Π i, ZMod (a i).nat_abs`.
  simp_rw [Nat.card_congr (quotientEquivPiZMod N b h).toEquiv, Nat.card_pi, Nat.card_zmod, a]

/--
theorem `Submodule.natAbs_det_basis_change` / 定理 `Submodule.natAbs_det_basis_change`

English:
theorem Submodule.natAbs_det_basis_change
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int M)
  proof: by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M ->ₗ[Int] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

中文:
定理 Submodule.natAbs_det_basis_change
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] (b : Basis ι 整数 M)
  证明: by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M ->ₗ[Int] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

Depends on / 依赖: Basis.det_comp_basis, Equiv.refl, LinearMap, LinearMap.det, N.subtype, b.det, b.equiv, det_comp_basis, natAbs, natAbs_det_equiv, subtype
-/
theorem Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int M)
    (N : Submodule Int M) (bN : Basis ι Int N) :
    (b.det ((↑) ∘ bN)).natAbs = Nat.card (M ⧸ N) := by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M ->ₗ[Int] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

end Submodule

section AddSubgroup

/--
theorem `AddSubgroup.index_eq_natAbs_det` / 定理 `AddSubgroup.index_eq_natAbs_det`

English:
theorem AddSubgroup.index_eq_natAbs_det
  statement: {E : Type*} [AddCommGroup E] {ι : Type*}
  proof: have : Module.Free Int E := Module.Free.of_basis bE
  have : Module.Finite Int E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

中文:
定理 AddSubgroup.index_eq_natAbs_det
  结论: {E : 类型} [AddCommGroup E] {ι : 类型}
  证明: have : Module.Free Int E := Module.Free.of_basis bE
  have : Module.Finite Int E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

Depends on / 依赖: Finite, Module, Module.Finite, Module.Finite.of_basis, Module.Free, Module.Free.of_basis, N.toIntSubmodule, Submodule, Submodule.natAbs_det_basis_change, natAbs_det_basis_change, of_basis, toIntSubmodule
-/
theorem AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (bE : Basis ι Int E) (N : AddSubgroup E) (bN : Basis ι Int N) :
    N.index = (bE.det (bN ·)).natAbs :=
  have : Module.Free Int E := Module.Free.of_basis bE
  have : Module.Finite Int E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AddSubgroup.relIndex_eq_natAbs_det` / 定理 `AddSubgroup.relIndex_eq_natAbs_det`

English:
theorem AddSubgroup.relIndex_eq_natAbs_det
  statement: {E : Type*} [AddCommGroup E]
  proof: by
  rw [relIndex]; rw [index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

中文:
定理 AddSubgroup.relIndex_eq_natAbs_det
  结论: {E : 类型} [AddCommGroup E]
  证明: by
  rw [relIndex]; rw [index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

Depends on / 依赖: addSubgroupOfEquivOfLe, index_eq_natAbs_det, relIndex, toIntLinearEquiv, toIntLinearEquiv.symm
-/
theorem AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι Int L₁.toIntSubmodule) (b₂ : Basis ι Int L₂.toIntSubmodule) :
    L₁.relIndex L₂ = (b₂.det (fun i => ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs := by
  rw [relIndex]; rw [index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `AddSubgroup.relIndex_eq_abs_det` / 定理 `AddSubgroup.relIndex_eq_abs_det`

English:
theorem AddSubgroup.relIndex_eq_abs_det
  statement: {E : Type*} [AddCommGroup E] [Module Rat E]
  proof: by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂)]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  change |algebraMap Int Rat _| = _
  rw [Basis.det_apply]; rw [Basis.det_apply]; rw [RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix

中文:
定理 AddSubgroup.relIndex_eq_abs_det
  结论: {E : 类型} [AddCommGroup E] [Module Rat E]
  证明: by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂)]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  change |algebraMap Int Rat _| = _
  rw [Basis.det_apply]; rw [Basis.det_apply]; rw [RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix

Depends on / 依赖: AddSubgroup, AddSubgroup.relIndex_eq_natAbs_det, Basis.det_apply, Basis.toMatrix_apply, Int.cast_abs, Nat.cast_natAbs, RingHom, RingHom.map_det, addSubgroupOfClosure, algebraMap, cast_abs, cast_natAbs, det_apply, map_det, relIndex_eq_natAbs_det, toMatrix_apply
-/
theorem AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module Rat E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ <= L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι Rat E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂)]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]
  change |algebraMap Int Rat _| = _
  rw [Basis.det_apply]; rw [Basis.det_apply]; rw [RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix_apply]

end AddSubgroup
