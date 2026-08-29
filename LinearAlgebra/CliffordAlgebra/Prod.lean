/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Clifford algebras of a direct sum of two vector spaces

We show that the Clifford algebra of a direct sum is the graded tensor product of the Clifford
algebras, as `CliffordAlgebra.equivProd`.

## Main definitions:

* `CliffordAlgebra.equivProd : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂)`

## TODO

Introduce morphisms and equivalences of graded algebras, and upgrade `CliffordAlgebra.equivProd`
to a graded algebra equivalence.

-/

@[expose] public section

suppress_compilation

variable {R M₁ M₂ N : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
variable [Module R M₁] [Module R M₂] [Module R N]
variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Qₙ : QuadraticForm R N)

open scoped TensorProduct

namespace CliffordAlgebra


section map_mul_map

variable {Q₁ Q₂ Qₙ}
variable (f₁ : Q₁ ->qᵢ Qₙ) (f₂ : Q₂ ->qᵢ Qₙ) (hf : forall x y, Qₙ.IsOrtho (f₁ x) (f₂ y))
variable (m₁ : CliffordAlgebra Q₁) (m₂ : CliffordAlgebra Q₂)
include hf

/-- If `m₁` and `m₂` are both homogeneous,
and the quadratic spaces `Q₁` and `Q₂` map into
orthogonal subspaces of `Qₙ` (for instance, when `Qₙ = Q₁.prod Q₂`),
then the product of the embedding in `CliffordAlgebra Q` commutes up to a sign factor. -/
nonrec theorem map_mul_map_of_isOrtho_of_mem_evenOdd
    {i₁ i₂ : ZMod 2} (hm₁ : m₁ in evenOdd Q₁ i₁) (hm₂ : m₂ in evenOdd Q₂ i₂) :
    map f₁ m₁ * map f₂ m₂ = (-1 : Intˣ) ^ (i₂ * i₁) • (map f₂ m₂ * map f₁ m₁) := by
  -- for each variable, induct on powers of `ι`, then on the exponent of each power
  induction hm₁ using Submodule.iSup_induction' with
  | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
  | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
  | mem i₁' m₁' hm₁ =>
    obtain ⟨i₁n, rfl⟩ := i₁'
    dsimp only at *
    induction hm₁ using Submodule.pow_induction_on_left' with
    | algebraMap =>
      rw [AlgHom.commutes]; rw [Nat.cast_zero]; rw [mul_zero]; rw [uzpow_zero]; rw [one_smul]; rw [Algebra.commutes]
    | add _ _ _ _ _ ihx ihy =>
      rw [map_add]; rw [add_mul]; rw [mul_add]; rw [ihx]; rw [ihy]; rw [smul_add]
    | mem_mul m₁ hm₁ i x₁ _hx₁ ih₁ =>
      obtain ⟨v₁, rfl⟩ := hm₁
      -- This is the first interesting goal.
      rw [map_mul]; rw [mul_assoc]; rw [ih₁]; rw [mul_smul_comm]; rw [map_apply_ι]; rw [Nat.cast_succ]; rw [mul_add_one]; rw [uzpow_add]; rw [mul_smul]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← smul_mul_assoc ((-1) ^ i₂)]
      clear ih₁
      congr 2
      induction hm₂ using Submodule.iSup_induction' with
      | zero => rw [map_zero, zero_mul, mul_zero, smul_zero]
      | add _ _ _ _ ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy, smul_add]
      | mem i₂' m₂' hm₂ =>
        clear m₂
        obtain ⟨i₂n, rfl⟩ := i₂'
        dsimp only at *
        induction hm₂ using Submodule.pow_induction_on_left' with
        | algebraMap =>
          rw [AlgHom.commutes]; rw [Nat.cast_zero]; rw [uzpow_zero]; rw [one_smul]; rw [Algebra.commutes]
        | add _ _ _ _ _ ihx ihy =>
          rw [map_add]; rw [add_mul]; rw [mul_add]; rw [ihx]; rw [ihy]; rw [smul_add]
        | mem_mul m₂ hm₂ i x₂ _hx₂ ih₂ =>
          obtain ⟨v₂, rfl⟩ := hm₂
          -- This is the second interesting goal.
          rw [map_mul]; rw [map_apply_ι]; rw [Nat.cast_succ]; rw [← mul_assoc]; rw [ι_mul_ι_comm_of_isOrtho (hf _ _)]; rw [neg_mul]; rw [mul_assoc]; rw [ih₂]; rw [mul_smul_comm]; rw [← mul_assoc]; rw [← Units.neg_smul]; rw [uzpow_add]; rw [uzpow_one]; rw [mul_neg_one]

/--
theorem `commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left` / 定理 `commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left`

English:
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
  proof: (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

中文:
定理 commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
  证明: (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

Depends on / 依赖: map_mul_map_of_isOrtho_of_mem_evenOdd
-/
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_left
    {i₂ : ZMod 2} (hm₁ : m₁ in evenOdd Q₁ 0) (hm₂ : m₂ in evenOdd Q₂ i₂) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
(map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

/--
theorem `commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right` / 定理 `commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right`

English:
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
  proof: (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

中文:
定理 commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
  证明: (map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

Depends on / 依赖: map_mul_map_of_isOrtho_of_mem_evenOdd
-/
theorem commute_map_mul_map_of_isOrtho_of_mem_evenOdd_zero_right
    {i₁ : ZMod 2} (hm₁ : m₁ in evenOdd Q₁ i₁) (hm₂ : m₂ in evenOdd Q₂ 0) :
    Commute (map f₁ m₁) (map f₂ m₂) :=
(map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂).trans by simp

/--
theorem `map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one` / 定理 `map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one`

English:
theorem map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
  proof: by
  simp [map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂]

中文:
定理 map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
  证明: by
  simp [map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂]

Depends on / 依赖: map_mul_map_of_isOrtho_of_mem_evenOdd
-/
theorem map_mul_map_eq_neg_of_isOrtho_of_mem_evenOdd_one
    (hm₁ : m₁ in evenOdd Q₁ 1) (hm₂ : m₂ in evenOdd Q₂ 1) :
    map f₁ m₁ * map f₂ m₂ = -map f₂ m₂ * map f₁ m₁ := by
  simp [map_mul_map_of_isOrtho_of_mem_evenOdd _ _ hf _ _ hm₁ hm₂]

end map_mul_map

/--
Definition of `ofProd` / `ofProd` 的定义

English:
definition ofProd
  signature: : CliffordAlgebra (Q₁.prod Q₂) ->ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂)
  body: lift _ ⟨
    LinearMap.coprod
      ((GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₁ 1).subtype ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((GradedTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₂ 1).subtype ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      simp_rw [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticMap.prod_apply, Submodule.coe_subtype,
        GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, map_add,
        add_mul, mul_add, GradedTensorProduct.algebraMap_def,
        GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
        LinearMap.codRestrict_apply, one_mul, uzpow_one, Units.neg_smul, one_smul, ι_sq_scalar,
        mul_one, ← GradedTensorProduct.algebraMap_def, ← GradedTensorProduct.algebraMap_def']
      abel⟩

@[simp]

中文:
定义 ofProd
  签名: : CliffordAlgebra (Q₁.乘积 Q₂) ->ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂)
  定义体: lift _ ⟨
    LinearMap.coprod
      ((GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₁ 1).subtype ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((GradedTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₂ 1).subtype ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      simp_rw [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticMap.prod_apply, Submodule.coe_subtype,
        GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, map_add,
        add_mul, mul_add, GradedTensorProduct.algebraMap_def,
        GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
        LinearMap.codRestrict_apply, one_mul, uzpow_one, Units.neg_smul, one_smul, ι_sq_scalar,
        mul_one, ← GradedTensorProduct.algebraMap_def, ← GradedTensorProduct.algebraMap_def']
      abel⟩

@[simp]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, Function, Function.comp_apply, GradedTensorProduc, GradedTensorProduct, GradedTensorProduct.includeLeft, GradedTensorProduct.includeRight, LinearMap, LinearMap.coe_comp, LinearMap.coprod, LinearMap.coprod_apply, QuadraticMap, QuadraticMap.prod_apply, Submodule, Submodule.coe_subtype, codRestrict, coe_comp, coe_subtype, comp_apply
-/
def ofProd : CliffordAlgebra (Q₁.prod Q₂) ->ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂) :=
  lift _ ⟨
    LinearMap.coprod
      ((GradedTensorProduct.includeLeft (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₁ 1).subtype ∘ₗ (ι Q₁).codRestrict _ (ι_mem_evenOdd_one Q₁))
      ((GradedTensorProduct.includeRight (evenOdd Q₁) (evenOdd Q₂)).toLinearMap
          ∘ₗ (evenOdd Q₂ 1).subtype ∘ₗ (ι Q₂).codRestrict _ (ι_mem_evenOdd_one Q₂)),
    fun m => by
      simp_rw [LinearMap.coprod_apply, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, QuadraticMap.prod_apply, Submodule.coe_subtype,
        GradedTensorProduct.includeLeft_apply, GradedTensorProduct.includeRight_apply, map_add,
        add_mul, mul_add, GradedTensorProduct.algebraMap_def,
        GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_one_mul_coe_tmul,
        GradedTensorProduct.tmul_coe_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
        LinearMap.codRestrict_apply, one_mul, uzpow_one, Units.neg_smul, one_smul, ι_sq_scalar,
        mul_one, ← GradedTensorProduct.algebraMap_def, ← GradedTensorProduct.algebraMap_def']
      abel⟩

@[simp]
/--
lemma `ofProd_ι_mk` / 引理 `ofProd_ι_mk`

English:
lemma ofProd_ι_mk
  given: (m₁ : M₁) (m₂ : M₂)
  proof: by
  rw [ofProd]; rw [lift_ι_apply]
  rfl

中文:
引理 ofProd_ι_mk
  条件: (m₁ : M₁) (m₂ : M₂)
  证明: by
  rw [ofProd]; rw [lift_ι_apply]
  rfl

Depends on / 依赖: ofProd
-/
lemma ofProd_ι_mk (m₁ : M₁) (m₂ : M₂) :
    ofProd Q₁ Q₂ (ι _ (m₁, m₂)) = ι Q₁ m₁ ᵍotimesₜ 1 + 1 ᵍotimesₜ ι Q₂ m₂ := by
  rw [ofProd]; rw [lift_ι_apply]
  rfl

/--
Definition of `toProd` / `toProd` 的定义

English:
definition toProd
  signature: : evenOdd Q₁ ᵍotimes[R] evenOdd Q₂ ->ₐ[R] CliffordAlgebra (Q₁.prod Q₂)
  body: GradedTensorProduct.lift _ _
    (CliffordAlgebra.map <| .inl _ _)
    (CliffordAlgebra.map <| .inr _ _)
    fun _i₁ _i₂ x₁ x₂ => map_mul_map_of_isOrtho_of_mem_evenOdd _ _ (QuadraticMap.IsOrtho.inl_inr) _
      _ x₁.prop x₂.prop

@[simp]

中文:
定义 toProd
  签名: : evenOdd Q₁ ᵍotimes[R] evenOdd Q₂ ->ₐ[R] CliffordAlgebra (Q₁.乘积 Q₂)
  定义体: GradedTensorProduct.lift _ _
    (CliffordAlgebra.map <| .inl _ _)
    (CliffordAlgebra.map <| .inr _ _)
    fun _i₁ _i₂ x₁ x₂ => map_mul_map_of_isOrtho_of_mem_evenOdd _ _ (QuadraticMap.IsOrtho.inl_inr) _
      _ x₁.prop x₂.prop

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.map, GradedTensorProduct, GradedTensorProduct.lift, IsOrtho, QuadraticMap, QuadraticMap.IsOrtho.inl_inr, inl_inr, map_mul_map_of_isOrtho_of_mem_evenOdd
-/
def toProd : evenOdd Q₁ ᵍotimes[R] evenOdd Q₂ ->ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  GradedTensorProduct.lift _ _
    (CliffordAlgebra.map <| .inl _ _)
    (CliffordAlgebra.map <| .inr _ _)
    fun _i₁ _i₂ x₁ x₂ => map_mul_map_of_isOrtho_of_mem_evenOdd _ _ (QuadraticMap.IsOrtho.inl_inr) _
      _ x₁.prop x₂.prop

@[simp]
/--
lemma `toProd_ι_tmul_one` / 引理 `toProd_ι_tmul_one`

English:
lemma toProd_ι_tmul_one
  given: (m₁ : M₁)
  statement: toProd Q₁ Q₂ (ι _ m₁ ᵍotimesₜ 1) = ι _ (m₁, 0)
  proof: by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [mul_one]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inl_apply]

@[simp]

中文:
引理 toProd_ι_tmul_one
  条件: (m₁ : M₁)
  结论: toProd Q₁ Q₂ (ι _ m₁ ᵍotimesₜ 1) = ι _ (m₁, 0)
  证明: by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [mul_one]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inl_apply]

@[simp]

Depends on / 依赖: GradedTensorProduct, GradedTensorProduct.lift_tmul, Isometry, QuadraticMap, QuadraticMap.Isometry.inl_apply, inl_apply, lift_tmul, map_one, mul_one, toProd
-/
lemma toProd_ι_tmul_one (m₁ : M₁) : toProd Q₁ Q₂ (ι _ m₁ ᵍotimesₜ 1) = ι _ (m₁, 0) := by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [mul_one]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inl_apply]

@[simp]
/--
lemma `toProd_one_tmul_ι` / 引理 `toProd_one_tmul_ι`

English:
lemma toProd_one_tmul_ι
  given: (m₂ : M₂)
  statement: toProd Q₁ Q₂ (1 ᵍotimesₜ ι _ m₂) = ι _ (0, m₂)
  proof: by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [one_mul]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inr_apply]

中文:
引理 toProd_one_tmul_ι
  条件: (m₂ : M₂)
  结论: toProd Q₁ Q₂ (1 ᵍotimesₜ ι _ m₂) = ι _ (0, m₂)
  证明: by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [one_mul]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inr_apply]

Depends on / 依赖: GradedTensorProduct, GradedTensorProduct.lift_tmul, Isometry, QuadraticMap, QuadraticMap.Isometry.inr_apply, inr_apply, lift_tmul, map_one, one_mul, toProd
-/
lemma toProd_one_tmul_ι (m₂ : M₂) : toProd Q₁ Q₂ (1 ᵍotimesₜ ι _ m₂) = ι _ (0, m₂) := by
  rw [toProd]; rw [GradedTensorProduct.lift_tmul]; rw [map_one]; rw [one_mul]; rw [map_apply_ι]; rw [QuadraticMap.Isometry.inr_apply]

/--
lemma `toProd_comp_ofProd` / 引理 `toProd_comp_ofProd`

English:
lemma toProd_comp_ofProd
  statement: (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = AlgHom.id _ _
  proof: by
  ext m <;> dsimp
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, add_zero]
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, zero_add]

中文:
引理 toProd_comp_ofProd
  结论: (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = 代数态射.id _ _
  证明: by
  ext m <;> dsimp
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, add_zero]
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, zero_add]

Depends on / 依赖: Prod.mk_zero_zero, add_zero, map_add, map_zero, mk_zero_zero, zero_add
-/
lemma toProd_comp_ofProd : (toProd Q₁ Q₂).comp (ofProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext m <;> dsimp
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, add_zero]
  · rw [ofProd_ι_mk, map_add, toProd_one_tmul_ι, toProd_ι_tmul_one, Prod.mk_zero_zero,
      map_zero, zero_add]

/--
lemma `ofProd_comp_toProd` / 引理 `ofProd_comp_toProd`

English:
lemma ofProd_comp_toProd
  statement: (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = AlgHom.id _ _
  proof: by
  ext <;> simp

中文:
引理 ofProd_comp_toProd
  结论: (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = 代数态射.id _ _
  证明: by
  ext <;> simp
-/
lemma ofProd_comp_toProd : (ofProd Q₁ Q₂).comp (toProd Q₁ Q₂) = AlgHom.id _ _ := by
  ext <;> simp

/-- The Clifford algebra over an orthogonal direct sum of quadratic vector spaces is isomorphic
as an algebra to the graded tensor product of the Clifford algebras of each space.

This is `CliffordAlgebra.toProd` and `CliffordAlgebra.ofProd` as an equivalence. -/
@[simps!]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂)
  body: AlgEquiv.ofAlgHom (ofProd Q₁ Q₂) (toProd Q₁ Q₂) (ofProd_comp_toProd _ _) (toProd_comp_ofProd _ _)

中文:
定义 prodEquiv
  签名: : CliffordAlgebra (Q₁.乘积 Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂)
  定义体: AlgEquiv.ofAlgHom (ofProd Q₁ Q₂) (toProd Q₁ Q₂) (ofProd_comp_toProd _ _) (toProd_comp_ofProd _ _)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, ofAlgHom, ofProd, ofProd_comp_toProd, toProd, toProd_comp_ofProd
-/
def prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ᵍotimes[R] evenOdd Q₂) :=
  AlgEquiv.ofAlgHom (ofProd Q₁ Q₂) (toProd Q₁ Q₂) (ofProd_comp_toProd _ _) (toProd_comp_ofProd _ _)

end CliffordAlgebra
