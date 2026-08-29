/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.RingTheory.Flat.Basic

/-!

# The Jacobi-Zariski exact sequence

Given algebras $R \to S \to T$, the Jacobi-Zariski exact sequence is a long exact sequence
relating the first homology of the naive cotangent complexes and the Kähler differentials of
the respective algebras. It takes the form:
$$
H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R} \to \Omega_{T/S} \to 0
$$
The maps in the sequence are
- `Algebra.H1Cotangent.map`
- `Algebra.H1Cotangent.δ`
- `KaehlerDifferential.mapBaseChange`
- `KaehlerDifferential.map`

The exactness lemmas are
- `Algebra.H1Cotangent.exact_map_δ`
- `Algebra.H1Cotangent.exact_δ_mapBaseChange`
- `KaehlerDifferential.exact_mapBaseChange_map`
- `KaehlerDifferential.map_surjective`

When $T$ is flat over $S$, the left bottom part of the snake lemma diagram used in
the construction of the connecting homomorphism `Algebra.Generators.H1Cotangent.δ`
naturally extends via a base change map. The exactness lemma is
`Algebra.Generators.H1Cotangent.exact_liftBaseChange_map_of_flat`. Globally, this extends
the Jacobi-Zariski exact sequence to the left via a natural base change map, taking the form
$$
T \otimes_S H_1(L_{S/R}) \to H_1(L_{T/R}) \to H_1(L_{T/S})
$$
The exactness lemma is `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`.

# TODO

The flatness assumption in `Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat`
is stronger than the `Tor`-vanishing conditions required in the full statement of
[Stacks Project, 00S2], this should be refactored and generalized once more API
for `Tor` modules is available.

-/

@[expose] public section

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

-- `Generators.{w, u₁, u₂}` depends on three universe variables and
-- to improve performance of universe unification, it should hold that
-- `w > u₁` and `w > u₂` in the lexicographic order. For more details
-- see https://github.com/leanprover-community/mathlib4/issues/26018
-- TODO: this remains an unsolved problem, ideally the lexicographic
-- order does not affect performance
universe w₁ w₂ w₃ w₄ w₅ u₁ u₂ u₃

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {ι' : Type w₃} {σ : Type w₂} {σ' : Type w₄} {τ : Type w₅}
variable (Q : Generators S T ι) (P : Generators R S σ)
variable (Q' : Generators S T ι') (P' : Generators R S σ') (W : Generators R T τ)

attribute [local instance] SMulCommClass.of_commMonoid

namespace Generators

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Cotangent.surjective_map_ofComp` / 引理 `Cotangent.surjective_map_ofComp`

English:
lemma Cotangent.surjective_map_ofComp
  proof: by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  have : x in Q.ker := hx
  rw [← map_ofComp_ker Q P]; rw [Ideal.mem_map_iff_of_surjective
    _ (toAlgHom_ofComp_surjective Q P)] at this
  obtain ⟨x, hx', rfl⟩ := this
  exact ⟨.mk ⟨x, hx'⟩, Extension.Cotangent.map_mk _ _⟩

中文:
引理 Cotangent.surjective_map_ofComp
  证明: by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  have : x in Q.ker := hx
  rw [← map_ofComp_ker Q P]; rw [Ideal.mem_map_iff_of_surjective
    _ (toAlgHom_ofComp_surjective Q P)] at this
  obtain ⟨x, hx', rfl⟩ := this
  exact ⟨.mk ⟨x, hx'⟩, Extension.Cotangent.map_mk _ _⟩

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.map_mk, Extension.Cotangent.mk_surjective, Ideal.mem_map_iff_of_surjective, Q.ker, map_mk, map_ofComp_ker, mem_map_iff_of_surjective, mk_surjective, toAlgHom_ofComp_surjective
-/
lemma Cotangent.surjective_map_ofComp :
    Function.Surjective (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  have : x in Q.ker := hx
  rw [← map_ofComp_ker Q P]; rw [Ideal.mem_map_iff_of_surjective
    _ (toAlgHom_ofComp_surjective Q P)] at this
  obtain ⟨x, hx', rfl⟩ := this
  exact ⟨.mk ⟨x, hx'⟩, Extension.Cotangent.map_mk _ _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open Extension.Cotangent in
/--
lemma `Cotangent.exact` / 引理 `Cotangent.exact`

English:
lemma Cotangent.exact
  proof: by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp,
      EmbeddingLike.map_eq_zero_iff]
    ext x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    simp only [map_mk, val_mk, LinearMap.zero_apply, val_zero]
    co

中文:
引理 Cotangent.exact
  证明: by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp,
      EmbeddingLike.map_eq_zero_iff]
    ext x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    simp only [map_mk, val_mk, LinearMap.zero_apply, val_zero]
    co

Depends on / 依赖: Cotangent, EmbeddingLike, EmbeddingLike.map_eq_zero_iff, Extension, Extension.Cotangent.map_comp, Extension.Cotangent.mk_surjective, IsScalarTower, IsScalarTower.toAlgHom, LinearMap, LinearMap.exact_of_comp_of_mem_range, LinearMap.liftBaseChange_comp, LinearMap.zero_apply, MvPolynomial, MvPolynomial.algHom_ext, P.Ring, Q.ker.toCotangent.map_zero, Q.ofComp, Q.toComp, algHom_ext, convert
-/
lemma Cotangent.exact :
    Function.Exact
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp,
      EmbeddingLike.map_eq_zero_iff]
    ext x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    simp only [map_mk, val_mk, LinearMap.zero_apply, val_zero]
    convert! Q.ker.toCotangent.map_zero
    trans ((IsScalarTower.toAlgHom R _ _).comp (IsScalarTower.toAlgHom R P.Ring S)) x
    · congr
      refine MvPolynomial.algHom_ext fun i => ?_
      change (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom (X i)) = _
      simp
    · simp [aeval_val_eq_zero hx]
  · intro x hx
    obtain ⟨⟨x : (Q.comp P).Ring, hx'⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    replace hx : (Q.ofComp P).toAlgHom x in Q.ker ^ 2 := by
      simpa only [map_mk, val_mk, val_zero, Ideal.toCotangent_eq_zero] using! congr(($hx).val)
    rw [pow_two]; rw [← map_ofComp_ker (P := P)]; rw [← Ideal.map_mul]; rw [Ideal.mem_map_iff_of_surjective
      _ (toAlgHom_ofComp_surjective Q P)] at hx
    obtain ⟨y, hy, e⟩ := hx
    rw [eq_comm]; rw [← sub_eq_zero]; rw [← map_sub]; rw [← RingHom.mem_ker]; rw [← map_toComp_ker] at e
    rw [LinearMap.range_liftBaseChange]
    let z : (Q.comp P).ker := ⟨x - y, Ideal.sub_mem _ hx' (Ideal.mul_le_right hy)⟩
    have hz : z.1 in P.ker.map (Q.toComp P).toAlgHom.toRingHom := e
    have : Extension.Cotangent.mk (P := (Q.comp P).toExtension) ⟨x, hx'⟩ =
      Extension.Cotangent.mk z := by
      ext; simpa only [val_mk, Ideal.toCotangent_eq, sub_sub_cancel, pow_two, z]
    rw [this]; rw [← Submodule.restrictScalars_mem (Q.comp P).Ring]; rw [← Submodule.mem_comap]; rw [← Submodule.span_singleton_le_iff_mem]; rw [← Submodule.map_le_map_iff_of_injective
      (f := Submodule.subtype _) Subtype.val_injective]; rw [Submodule.map_subtype_span_singleton]; rw [Submodule.span_singleton_le_iff_mem]
    refine (show Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker <= _ from ?_) hz
    rw [Ideal.map_le_iff_le_comap]
    rintro w hw
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_comap, RingHom.coe_coe,
      Submodule.mem_map, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right,
      toExtension_Ring]
    refine ⟨?_, Submodule.subset_span ⟨Extension.Cotangent.mk ⟨w, hw⟩, ?_⟩⟩
    · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker, Hom.algebraMap_toAlgHom]
      rw [aeval_val_eq_zero hw]; rw [map_zero]
    · rw [map_mk]
      rfl

/-- Given `R[X] → S` and `S[Y] → T`, the cotangent space of `R[X][Y] → T` is isomorphic
to the direct product of the cotangent space of `S[Y] → T` and `R[X] → S` (base changed to `T`). -/
noncomputable
/--
Definition of `CotangentSpace.compEquiv` / `CotangentSpace.compEquiv` 的定义

English:
definition CotangentSpace.compEquiv
  signature: :
  body: (Q.comp P).cotangentSpaceBasis.repr.trans
    (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange T)).repr.symm

中文:
定义 CotangentSpace.compEquiv
  签名: :
  定义体: (Q.comp P).cotangentSpaceBasis.repr.trans
    (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange T)).repr.symm

Depends on / 依赖: P.cotangentSpaceBasis.baseChange, Q.comp, Q.cotangentSpaceBasis.prod, baseChange, cotangentSpaceBasis, cotangentSpaceBasis.repr.trans, repr.symm
-/
def CotangentSpace.compEquiv :
    (Q.comp P).toExtension.CotangentSpace ≃ₗ[T]
      Q.toExtension.CotangentSpace × (T otimes[S] P.toExtension.CotangentSpace) :=
  (Q.comp P).cotangentSpaceBasis.repr.trans
    (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange T)).repr.symm

/--
lemma `CotangentSpace.compEquiv_symm_inr` / 引理 `CotangentSpace.compEquiv_symm_inr`

English:
lemma CotangentSpace.compEquiv_symm_inr
  proof: by
  classical
  apply (P.cotangentSpaceBasis.baseChange T).ext
  intro i
  apply (Q.comp P).cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Basis.baseChange_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    F

中文:
引理 CotangentSpace.compEquiv_symm_inr
  证明: by
  classical
  apply (P.cotangentSpaceBasis.baseChange T).ext
  intro i
  apply (Q.comp P).cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Basis.baseChange_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    F

Depends on / 依赖: Basis.baseChange_apply, Basis.repr_linearCombination, Basis.repr_symm_apply, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.trans_symm, LinearMap, LinearMap.coe_comp, LinearMap.coe_inr, LinearMap.liftBaseChange_tmul, P.cotangentSpaceBasis.baseChange, Q.comp, baseChange, baseChange_apply, classical, coe_coe
-/
lemma CotangentSpace.compEquiv_symm_inr :
    (compEquiv Q P).symm.toLinearMap ∘ₗ
      LinearMap.inr T Q.toExtension.CotangentSpace (T otimes[S] P.toExtension.CotangentSpace) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T := by
  classical
  apply (P.cotangentSpaceBasis.baseChange T).ext
  intro i
  apply (Q.comp P).cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Basis.baseChange_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    Function.comp_apply, LinearEquiv.trans_apply, Basis.repr_symm_apply, pderiv_X, toComp_val,
    Basis.repr_linearCombination, LinearMap.liftBaseChange_tmul, one_smul, repr_CotangentSpaceMap]
  obtain (j | j) := j <;>
    simp only [Basis.prod_repr_inr, Basis.baseChange_repr_tmul,
      Basis.repr_self, Basis.prod_repr_inl, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_apply,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Sum.inr.injEq,
      MonoidWithZeroHom.map_ite_one_zero, reduceCtorEq]

/--
lemma `CotangentSpace.compEquiv_symm_zero` / 引理 `CotangentSpace.compEquiv_symm_zero`

English:
lemma CotangentSpace.compEquiv_symm_zero
  given: (x)
  proof: DFunLike.congr_fun (compEquiv_symm_inr Q P) x

中文:
引理 CotangentSpace.compEquiv_symm_zero
  条件: (x)
  证明: DFunLike.congr_fun (compEquiv_symm_inr Q P) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, compEquiv_symm_inr, congr_fun
-/
lemma CotangentSpace.compEquiv_symm_zero (x) :
    (compEquiv Q P).symm (0, x) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T x :=
  DFunLike.congr_fun (compEquiv_symm_inr Q P) x

/--
lemma `CotangentSpace.fst_compEquiv` / 引理 `CotangentSpace.fst_compEquiv`

English:
lemma CotangentSpace.fst_compEquiv
  proof: by
  classical
  apply (Q.comp P).cotangentSpaceBasis.ext
  intro i
  apply Q.cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ofComp_val,
    LinearEquiv.trans_apply, Basis.repr_self, LinearMap.fst_apply, repr_Cotangent

中文:
引理 CotangentSpace.fst_compEquiv
  证明: by
  classical
  apply (Q.comp P).cotangentSpaceBasis.ext
  intro i
  apply Q.cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ofComp_val,
    LinearEquiv.trans_apply, Basis.repr_self, LinearMap.fst_apply, repr_Cotangent

Depends on / 依赖: Basis.prod_apply, Basis.repr_se, Basis.repr_self, Basis.repr_symm_apply, Finsupp, Finsupp.linearCombination_single, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_inl, LinearMap.coe_inr, LinearMap.fst_apply, Q.comp, Q.cotangentSpaceBasis.repr.injective, Sum.elim_inl, classical
-/
lemma CotangentSpace.fst_compEquiv :
    LinearMap.fst T Q.toExtension.CotangentSpace (T otimes[S] P.toExtension.CotangentSpace) ∘ₗ
      (compEquiv Q P).toLinearMap = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom := by
  classical
  apply (Q.comp P).cotangentSpaceBasis.ext
  intro i
  apply Q.cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ofComp_val,
    LinearEquiv.trans_apply, Basis.repr_self, LinearMap.fst_apply, repr_CotangentSpaceMap]
  obtain (i | i) := i <;>
    simp only [Basis.repr_symm_apply, Finsupp.linearCombination_single, Basis.prod_apply,
      LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl, Function.comp_apply, one_smul,
      Basis.repr_self, Finsupp.single_apply, pderiv_X, Pi.single_apply,
      Sum.elim_inr, Function.comp_apply, Basis.baseChange_apply, one_smul,
      MonoidWithZeroHom.map_ite_one_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, derivation_C]

/--
lemma `CotangentSpace.fst_compEquiv_apply` / 引理 `CotangentSpace.fst_compEquiv_apply`

English:
lemma CotangentSpace.fst_compEquiv_apply
  given: (x)
  proof: DFunLike.congr_fun (fst_compEquiv Q P) x

中文:
引理 CotangentSpace.fst_compEquiv_apply
  条件: (x)
  证明: DFunLike.congr_fun (fst_compEquiv Q P) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, fst_compEquiv
-/
lemma CotangentSpace.fst_compEquiv_apply (x) :
    (compEquiv Q P x).1 = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom x :=
  DFunLike.congr_fun (fst_compEquiv Q P) x

/--
lemma `CotangentSpace.map_toComp_injective` / 引理 `CotangentSpace.map_toComp_injective`

English:
lemma CotangentSpace.map_toComp_injective
  proof: by
  rw [← compEquiv_symm_inr]
  apply (compEquiv Q P).symm.injective.comp
  exact Prod.mk_right_injective _

中文:
引理 CotangentSpace.map_toComp_injective
  证明: by
  rw [← compEquiv_symm_inr]
  apply (compEquiv Q P).symm.injective.comp
  exact Prod.mk_right_injective _

Depends on / 依赖: Prod.mk_right_injective, compEquiv, compEquiv_symm_inr, injective, mk_right_injective, symm.injective.comp
-/
lemma CotangentSpace.map_toComp_injective :
    Function.Injective
      ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T) := by
  rw [← compEquiv_symm_inr]
  apply (compEquiv Q P).symm.injective.comp
  exact Prod.mk_right_injective _

/--
lemma `CotangentSpace.map_ofComp_surjective` / 引理 `CotangentSpace.map_ofComp_surjective`

English:
lemma CotangentSpace.map_ofComp_surjective
  proof: by
  rw [← fst_compEquiv]
  exact (Prod.fst_surjective).comp (compEquiv Q P).surjective

中文:
引理 CotangentSpace.map_ofComp_surjective
  证明: by
  rw [← fst_compEquiv]
  exact (Prod.fst_surjective).comp (compEquiv Q P).surjective

Depends on / 依赖: Prod.fst_surjective, compEquiv, fst_compEquiv, fst_surjective, surjective
-/
lemma CotangentSpace.map_ofComp_surjective :
    Function.Surjective (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv]
  exact (Prod.fst_surjective).comp (compEquiv Q P).surjective

/--
lemma `CotangentSpace.exact` / 引理 `CotangentSpace.exact`

English:
lemma CotangentSpace.exact
  proof: by
  rw [← fst_compEquiv]; rw [← compEquiv_symm_inr]
  conv_rhs => rw [← LinearEquiv.symm_symm (compEquiv Q P)]
  rw [LinearEquiv.conj_exact_iff_exact]
  exact Function.Exact.inr_fst

中文:
引理 CotangentSpace.exact
  证明: by
  rw [← fst_compEquiv]; rw [← compEquiv_symm_inr]
  conv_rhs => rw [← LinearEquiv.symm_symm (compEquiv Q P)]
  rw [LinearEquiv.conj_exact_iff_exact]
  exact Function.Exact.inr_fst

Depends on / 依赖: Function, Function.Exact.inr_fst, LinearEquiv, LinearEquiv.conj_exact_iff_exact, LinearEquiv.symm_symm, compEquiv, compEquiv_symm_inr, conj_exact_iff_exact, conv_rhs, fst_compEquiv, inr_fst, symm_symm
-/
lemma CotangentSpace.exact :
    Function.Exact ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv]; rw [← compEquiv_symm_inr]
  conv_rhs => rw [← LinearEquiv.symm_symm (compEquiv Q P)]
  rw [LinearEquiv.conj_exact_iff_exact]
  exact Function.Exact.inr_fst

namespace H1Cotangent

variable (R) in
/--
Given `0 → I → S[Y] → T → 0`, this is an auxiliary map from `S[Y]` to `T ⊗[S] Ω[S⁄R]` whose
restriction to `ker(I/I² → ⊕ S dyᵢ)` is the connecting homomorphism in the Jacobi-Zariski sequence.
-/
noncomputable
/--
Definition of `δAux` / `δAux` 的定义

English:
definition δAux
  signature: :
  body: Finsupp.lsum R (R := R) (fun f =>
    (TensorProduct.mk S T _ (f.prod (Q.val · ^ ·))).restrictScalars R ∘ₗ (D R S).toLinearMap)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).toLinearMap

中文:
定义 δAux
  签名: :
  定义体: Finsupp.lsum R (R := R) (fun f =>
    (TensorProduct.mk S T _ (f.prod (Q.val · ^ ·))).restrictScalars R ∘ₗ (D R S).toLinearMap)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).toLinearMap

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffLinearEquiv, Finsupp, Finsupp.lsum, Q.val, TensorProduct, TensorProduct.mk, coeffLinearEquiv, f.prod, restrictScalars, toLinearMap
-/
def δAux :
    Q.Ring ->ₗ[R] T otimes[S] Ω[S⁄R] :=
  Finsupp.lsum R (R := R) (fun f =>
    (TensorProduct.mk S T _ (f.prod (Q.val · ^ ·))).restrictScalars R ∘ₗ (D R S).toLinearMap)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv _).toLinearMap

/--
lemma `δAux_monomial` / 引理 `δAux_monomial`

English:
lemma δAux_monomial
  given: (n r)
  proof: by simp [δAux]

@[simp]

中文:
引理 δAux_monomial
  条件: (n r)
  证明: by simp [δAux]

@[simp]
-/
lemma δAux_monomial (n r) :
    δAux R Q (monomial n r) = (n.prod (Q.val · ^ ·)) otimesₜ D R S r := by simp [δAux]

@[simp]
/--
lemma `δAux_X` / 引理 `δAux_X`

English:
lemma δAux_X
  given: (i)
  proof: by
  rw [X]; rw [δAux_monomial]
  simp only [Derivation.map_one_eq_zero, tmul_zero]

中文:
引理 δAux_X
  条件: (i)
  证明: by
  rw [X]; rw [δAux_monomial]
  simp only [Derivation.map_one_eq_zero, tmul_zero]

Depends on / 依赖: Derivation, Derivation.map_one_eq_zero, map_one_eq_zero, tmul_zero
-/
lemma δAux_X (i) :
    δAux R Q (X i) = 0 := by
  rw [X]; rw [δAux_monomial]
  simp only [Derivation.map_one_eq_zero, tmul_zero]

/--
lemma `δAux_mul` / 引理 `δAux_mul`

English:
lemma δAux_mul
  given: (x y)
  proof: by
  induction x using MvPolynomial.induction_on' with
  | monomial n r =>
    induction y using MvPolynomial.induction_on' with
    | monomial m s =>
      simp only [monomial_mul, δAux_monomial, Derivation.leibniz, tmul_add, tmul_smul,
        smul_tmul', Algebra.smul_def, algebraMap_apply, aeval_

中文:
引理 δAux_mul
  条件: (x y)
  证明: by
  induction x using MvPolynomial.induction_on' with
  | monomial n r =>
    induction y using MvPolynomial.induction_on' with
    | monomial m s =>
      simp only [monomial_mul, δAux_monomial, Derivation.leibniz, tmul_add, tmul_smul,
        smul_tmul', Algebra.smul_def, algebraMap_apply, aeval_

Depends on / 依赖: Algebra, Algebra.smul_def, Derivation, Derivation.leibniz, Finsupp, Finsupp.prod_add_index, MvPolynomial, MvPolynomial.induction_on, add_smul, aeval_monomial, algebraMap_apply, implies_true, induction_on, leibniz, m.prod, map_add, monomial, monomial_mul, mul_add, mul_assoc
-/
lemma δAux_mul (x y) :
    δAux R Q (x * y) = x • (δAux R Q y) + y • (δAux R Q x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial n r =>
    induction y using MvPolynomial.induction_on' with
    | monomial m s =>
      simp only [monomial_mul, δAux_monomial, Derivation.leibniz, tmul_add, tmul_smul,
        smul_tmul', Algebra.smul_def, algebraMap_apply, aeval_monomial, mul_assoc]
      rw [mul_comm (m.prod _) (n.prod _)]
      simp only [pow_zero, implies_true, pow_add, Finsupp.prod_add_index']
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, smul_add, hy₁, hy₂, mul_add, add_smul]; abel
  | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂, add_smul, smul_add]; abel

/--
lemma `δAux_C` / 引理 `δAux_C`

English:
lemma δAux_C
  given: (r)
  proof: by
  rw [← monomial_zero']; rw [δAux_monomial]; rw [Finsupp.prod_zero_index]

中文:
引理 δAux_C
  条件: (r)
  证明: by
  rw [← monomial_zero']; rw [δAux_monomial]; rw [Finsupp.prod_zero_index]

Depends on / 依赖: Finsupp, Finsupp.prod_zero_index, monomial_zero, prod_zero_index
-/
lemma δAux_C (r) :
    δAux R Q (C r) = 1 otimesₜ D R S r := by
  rw [← monomial_zero']; rw [δAux_monomial]; rw [Finsupp.prod_zero_index]

set_option backward.isDefEq.respectTransparency false in
variable {Q} {Q'} in
/--
lemma `δAux_toAlgHom` / 引理 `δAux_toAlgHom`

English:
lemma δAux_toAlgHom
  given: (f : Hom Q Q') (x)
  proof: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower Q.Ring Q.Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s => simp [MvPolynomial.algebraMap_eq, δAux_C]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add]
  

中文:
引理 δAux_toAlgHom
  条件: (f : Hom Q Q') (x)
  证明: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower Q.Ring Q.Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s => simp [MvPolynomial.algebraMap_eq, δAux_C]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add]
  

Depends on / 依赖: AddCommGroup, Hom.algebraMap_toAlgHom, Hom.toAlgHom_X, IsScalarTower, IsScalarTower.algebraMap_smul, IsScalarTower.left, MvPolynomial, MvPolynomial.algebraMap_eq, MvPolynomial.induction_on, Q.Ring, RingHom, RingHom.id_apply, add_add_add_comm, algebraMap_apply, algebraMap_eq, algebraMap_self, algebraMap_smul, algebraMap_toAlgHom, id_apply, induction_on
-/
lemma δAux_toAlgHom (f : Hom Q Q') (x) :
    δAux R Q' (f.toAlgHom x) = δAux R Q x + Finsupp.linearCombination _ (δAux R Q' ∘ f.val)
      (Q.cotangentSpaceBasis.repr ((1 : T) otimesₜ[Q.Ring] D S Q.Ring x :)) := by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower Q.Ring Q.Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s => simp [MvPolynomial.algebraMap_eq, δAux_C]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add]
    rw [add_add_add_comm]
  | mul_X p n IH =>
    simp only [map_mul, Hom.toAlgHom_X, δAux_mul, algebraMap_apply, Hom.algebraMap_toAlgHom,
      ← @IsScalarTower.algebraMap_smul Q'.Ring T, algebraMap_self, δAux_X,
      RingHom.id_apply, coe_eval₂Hom, IH, Hom.aeval_val, smul_add, map_aeval, tmul_add, tmul_smul,
      ← @IsScalarTower.algebraMap_smul Q.Ring T, smul_zero, aeval_X, zero_add, Derivation.leibniz,
      Basis.repr_self, map_add, one_smul, map_smul, Finsupp.linearCombination_single,
      RingHomCompTriple.comp_eq, Function.comp_apply, ← cotangentSpaceBasis_apply]
    rw [add_left_comm]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δAux_ofComp` / 引理 `δAux_ofComp`

English:
lemma δAux_ofComp
  given: (x : (Q.comp P).Ring)
  proof: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower (Q.comp P).Ring (Q.comp P).Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s =>
    simp only [algHom_C, δAux_C, derivation_C, Derivation.map_algebraMap,
      tmul_zero, map_

中文:
引理 δAux_ofComp
  条件: (x : (Q.comp P).Ring)
  证明: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower (Q.comp P).Ring (Q.comp P).Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s =>
    simp only [algHom_C, δAux_C, derivation_C, Derivation.map_algebraMap,
      tmul_zero, map_

Depends on / 依赖: AddCommGroup, Derivation, Derivation.map_algebraMap, Hom.toAlgHom_X, IsScalarTo, IsScalarTower, IsScalarTower.left, MvPolynomial, MvPolynomial.algebraMap_apply, MvPolynomial.induction_on, Prod.snd_add, Prod.snd_zero, Q.comp, algHom_C, algebraMap_apply, derivation_C, induction_on, map_add, map_algebraMap, map_mul
-/
lemma δAux_ofComp (x : (Q.comp P).Ring) :
    δAux R Q ((Q.ofComp P).toAlgHom x) =
      P.toExtension.toKaehler.baseChange T (CotangentSpace.compEquiv Q P
        (1 otimesₜ[(Q.comp P).Ring] (D R (Q.comp P).Ring) x : _)).2 := by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  have : IsScalarTower (Q.comp P).Ring (Q.comp P).Ring T := IsScalarTower.left _
  induction x using MvPolynomial.induction_on with
  | C s =>
    simp only [algHom_C, δAux_C, derivation_C, Derivation.map_algebraMap,
      tmul_zero, map_zero, MvPolynomial.algebraMap_apply, Prod.snd_zero]
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, hx₁, hx₂, tmul_add, Prod.snd_add]
  | mul_X p n IH =>
    simp only [map_mul, Hom.toAlgHom_X, ofComp_val, δAux_mul,
      ← @IsScalarTower.algebraMap_smul Q.Ring T, algebraMap_apply, Hom.algebraMap_toAlgHom,
      algebraMap_self, map_aeval, RingHomCompTriple.comp_eq, comp_val, RingHom.id_apply,
      IH, Derivation.leibniz, tmul_add, tmul_smul, ← cotangentSpaceBasis_apply, coe_eval₂Hom,
      ← @IsScalarTower.algebraMap_smul (Q.comp P).Ring T, aeval_X, map_smul, Prod.snd_add,
      Prod.smul_snd, map_add]
    obtain (n | n) := n
    · simp only [Sum.elim_inl, δAux_X, smul_zero, aeval_X,
        CotangentSpace.compEquiv, LinearEquiv.trans_apply, Basis.repr_symm_apply, zero_add,
        Basis.repr_self, Finsupp.linearCombination_single, Basis.prod_apply, LinearMap.coe_inl,
        LinearMap.coe_inr, Function.comp_apply, one_smul, map_zero]
    · simp only [Sum.elim_inr, Function.comp_apply, algHom_C, δAux_C,
        CotangentSpace.compEquiv, LinearEquiv.trans_apply, Basis.repr_symm_apply,
        algebraMap_smul, Basis.repr_self, Finsupp.linearCombination_single, Basis.prod_apply,
        LinearMap.coe_inr, Basis.baseChange_apply, one_smul, LinearMap.baseChange_tmul,
        toKaehler_cotangentSpaceBasis, add_left_inj, LinearMap.coe_inl]
      rfl

/--
lemma `map_comp_cotangentComplex_baseChange` / 引理 `map_comp_cotangentComplex_baseChange`

English:
lemma map_comp_cotangentComplex_baseChange
  proof: by
  ext x; simp [Extension.CotangentSpace.map_cotangentComplex]

中文:
引理 map_comp_cotangentComplex_baseChange
  证明: by
  ext x; simp [Extension.CotangentSpace.map_cotangentComplex]

Depends on / 依赖: CotangentSpace, Extension, Extension.CotangentSpace.map_cotangentComplex, map_cotangentComplex
-/
lemma map_comp_cotangentComplex_baseChange :
    (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T ∘ₗ
      P.toExtension.cotangentComplex.baseChange T =
    (Q.comp P).toExtension.cotangentComplex ∘ₗ
      (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T := by
  ext x; simp [Extension.CotangentSpace.map_cotangentComplex]

open Generators in
/--
The connecting homomorphism in the Jacobi-Zariski sequence for given presentations.
Given representations `0 → I → R[X] → S → 0` and `0 → K → S[Y] → T → 0`,
we may consider the induced representation `0 → J → R[X, Y] → T → 0`,
and this map is obtained by applying snake lemma to the following diagram
```
    T ⊗[S] Ω[S/R] → Ω[T/R] → Ω[T/S] → 0
        ↑ ↑ ↑
0 → T ⊗[S] (⨁ₓ S dx) → (⨁ₓ T dx) ⊕ (⨁ᵧ T dy) → ⨁ᵧ T dy → 0
        ↑ ↑ ↑
    T ⊗[S] (I/I²) → J/J² → K/K² → 0
                                  ↑ ↑
                             H¹(L_{T/R}) → H¹(L_{T/S})

```
This is independent from the presentations chosen. See `H1Cotangent.δ_comp_equiv`.
-/
noncomputable
/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: :
  body: SnakeLemma.δ'
    (P.toExtension.cotangentComplex.baseChange T)
    (Q.comp P).toExtension.cotangentComplex
    Q.toExtension.cotangentComplex
    ((Extension.Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.Cotangent.map (ofComp Q P).toExtensionHom)
    (Cotangent.exact Q

中文:
定义 δ
  签名: :
  定义体: SnakeLemma.δ'
    (P.toExtension.cotangentComplex.baseChange T)
    (Q.comp P).toExtension.cotangentComplex
    Q.toExtension.cotangentComplex
    ((Extension.Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.Cotangent.map (ofComp Q P).toExtensionHom)
    (Cotangent.exact Q

Depends on / 依赖: Cotangent, Cotangent.exact, CotangentSpace, CotangentSpace.exact, Extension, Extension.Cotangent.map, Extension.CotangentSpace.map, P.toExtension.cotangentComplex.baseChange, Q.comp, Q.toExtension.cotangentComplex, SnakeLemma, baseChange, cotangentComplex, liftBaseChange, map_comp_cotangentComplex_baseChange, ofComp, toComp, toExtension, toExtension.cotangentComplex, toExtensionHom
-/
def δ :
    Q.toExtension.H1Cotangent ->ₗ[T] T otimes[S] Ω[S⁄R] :=
  SnakeLemma.δ'
    (P.toExtension.cotangentComplex.baseChange T)
    (Q.comp P).toExtension.cotangentComplex
    Q.toExtension.cotangentComplex
    ((Extension.Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.Cotangent.map (ofComp Q P).toExtensionHom)
    (Cotangent.exact Q P)
    ((Extension.CotangentSpace.map (toComp Q P).toExtensionHom).liftBaseChange T)
    (Extension.CotangentSpace.map (ofComp Q P).toExtensionHom)
    (CotangentSpace.exact Q P)
    (map_comp_cotangentComplex_baseChange Q P)
    (by ext; exact Extension.CotangentSpace.map_cotangentComplex (ofComp Q P).toExtensionHom _)
    Q.toExtension.h1Cotangentι
    (LinearMap.exact_subtype_ker_map _)
    (N₁ := T otimes[S] P.toExtension.CotangentSpace)
    (P.toExtension.toKaehler.baseChange T)
    (lTensor_exact T P.toExtension.exact_cotangentComplex_toKaehler
      P.toExtension.toKaehler_surjective)
    (Cotangent.surjective_map_ofComp Q P)
    (CotangentSpace.map_toComp_injective Q P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `exact_δ_map` / 引理 `exact_δ_map`

English:
lemma exact_δ_map
  proof: by
  simp only [δ]
  apply SnakeLemma.exact_δ_left (π₂ := (Q.comp P).toExtension.toKaehler)
    (hπ₂ := (Q.comp P).toExtension.exact_cotangentComplex_toKaehler)
  · apply (P.cotangentSpaceBasis.baseChange T).ext
    intro i
    simp only [Basis.baseChange_apply, LinearMap.coe_comp, Function.comp_app

中文:
引理 exact_δ_map
  证明: by
  simp only [δ]
  apply SnakeLemma.exact_δ_left (π₂ := (Q.comp P).toExtension.toKaehler)
    (hπ₂ := (Q.comp P).toExtension.exact_cotangentComplex_toKaehler)
  · apply (P.cotangentSpaceBasis.baseChange T).ext
    intro i
    simp only [Basis.baseChange_apply, LinearMap.coe_comp, Function.comp_app

Depends on / 依赖: Basis.baseChange_apply, Cotangen, Extension, Extension.Cotangen, Function, Function.comp_apply, LinearMap, LinearMap.baseChange_tmul, LinearMap.coe_comp, LinearMap.liftBaseChange_tmul, P.cotangentSpaceBasis.baseChange, Q.comp, SnakeLemma, SnakeLemma.exact_, baseChange, baseChange_apply, baseChange_tmul, coe_comp, comp_apply, conv_rhs
-/
lemma exact_δ_map :
    Function.Exact (δ Q P) (mapBaseChange R S T) := by
  simp only [δ]
  apply SnakeLemma.exact_δ_left (π₂ := (Q.comp P).toExtension.toKaehler)
    (hπ₂ := (Q.comp P).toExtension.exact_cotangentComplex_toKaehler)
  · apply (P.cotangentSpaceBasis.baseChange T).ext
    intro i
    simp only [Basis.baseChange_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.baseChange_tmul, toKaehler_cotangentSpaceBasis, mapBaseChange_tmul, map_D,
      one_smul, LinearMap.liftBaseChange_tmul]
    rw [cotangentSpaceBasis_apply]
    conv_rhs => enter [2]; tactic => exact Extension.CotangentSpace.map_tmul ..
    simp only [map_one, mapBaseChange_tmul, map_D, one_smul]
    simp [Extension.Hom.toAlgHom]
  · exact LinearMap.lTensor_surjective T P.toExtension.toKaehler_surjective

/--
lemma `δ_eq` / 引理 `δ_eq`

English:
lemma δ_eq
  statement: (x : Q.toExtension.H1Cotangent) (y)
  proof: by
  simp only [δ]
  apply SnakeLemma.δ_eq
  exacts [hy, hz]

中文:
引理 δ_eq
  结论: (x : Q.toExtension.H1Cotangent) (y)
  证明: by
  simp only [δ]
  apply SnakeLemma.δ_eq
  exacts [hy, hz]

Depends on / 依赖: SnakeLemma, exacts
-/
lemma δ_eq (x : Q.toExtension.H1Cotangent) (y)
    (hy : Extension.Cotangent.map (ofComp Q P).toExtensionHom y = x.1) (z)
    (hz : (Extension.CotangentSpace.map (toComp Q P).toExtensionHom).liftBaseChange T z =
      (Q.comp P).toExtension.cotangentComplex y) :
    δ Q P x = P.toExtension.toKaehler.baseChange T z := by
  simp only [δ]
  apply SnakeLemma.δ_eq
  exacts [hy, hz]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `δ_eq_δAux` / 引理 `δ_eq_δAux`

English:
lemma δ_eq_δAux
  given: (x : Q.ker) (hx)
  proof: by
  let y := Extension.Cotangent.mk (P := (Q.comp P).toExtension) (Q.kerCompPreimage P x)
  have hy : (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) y = Extension.Cotangent.mk x := by
    simp only [y, Extension.Cotangent.map_mk]
    congr
    exact ofComp_kerCompPreimage Q P x
  let z := (C

中文:
引理 δ_eq_δAux
  条件: (x : Q.ker) (hx)
  证明: by
  let y := Extension.Cotangent.mk (P := (Q.comp P).toExtension) (Q.kerCompPreimage P x)
  have hy : (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) y = Extension.Cotangent.mk x := by
    simp only [y, Extension.Cotangent.map_mk]
    congr
    exact ofComp_kerCompPreimage Q P x
  let z := (C

Depends on / 依赖: Cotangent, CotangentSpace, CotangentSpace.compEquiv, CotangentSpace.compEquiv_symm, Extension, Extension.Cotangent.map, Extension.Cotangent.map_mk, Extension.Cotangent.mk, H1Cotangent, Q.comp, Q.kerCompPreimage, Q.ofComp, compEquiv, compEquiv_symm, cotangentComplex, kerCompPreimage, map_mk, ofComp, ofComp_kerCompPreimage, toExtension
-/
lemma δ_eq_δAux (x : Q.ker) (hx) :
    δ Q P ⟨.mk x, hx⟩ = δAux R Q x.1 := by
  let y := Extension.Cotangent.mk (P := (Q.comp P).toExtension) (Q.kerCompPreimage P x)
  have hy : (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) y = Extension.Cotangent.mk x := by
    simp only [y, Extension.Cotangent.map_mk]
    congr
    exact ofComp_kerCompPreimage Q P x
  let z := (CotangentSpace.compEquiv Q P ((Q.comp P).toExtension.cotangentComplex y)).2
  rw [H1Cotangent.δ_eq (y := y) (z := z)]
  · rw [← ofComp_kerCompPreimage Q P x, δAux_ofComp]
    rfl
  · exact hy
  · rw [← CotangentSpace.compEquiv_symm_inr]
    apply (CotangentSpace.compEquiv Q P).injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr, Function.comp_apply,
      LinearEquiv.apply_symm_apply, z]
    ext
    swap; · rfl
    change 0 = (LinearMap.fst T Q.toExtension.CotangentSpace
        (T otimes[S] P.toExtension.CotangentSpace) ∘ₗ (CotangentSpace.compEquiv Q P).toLinearMap)
      ((Q.comp P).toExtension.cotangentComplex y)
    rw [CotangentSpace.fst_compEquiv]; rw [Extension.CotangentSpace.map_cotangentComplex]; rw [hy]; rw [hx]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `δ_C` / 引理 `δ_C`

English:
lemma δ_C
  given: {r : S} (hr : C r in Q.ker)
  proof: by
  rw [δ_eq_δAux]; rw [δAux_C]

中文:
引理 δ_C
  条件: {r : S} (hr : C r in Q.ker)
  证明: by
  rw [δ_eq_δAux]; rw [δAux_C]
-/
lemma δ_C {r : S} (hr : C r in Q.ker) :
    δ Q P ⟨Extension.Cotangent.mk ⟨C r, hr⟩, Extension.Cotangent.mk_C_mem_ker_cotangentComplex ..⟩
      = 1 otimesₜ[S] D R S r := by
  rw [δ_eq_δAux]; rw [δAux_C]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `δ_eq_δ` / 引理 `δ_eq_δ`

English:
lemma δ_eq_δ
  statement: δ Q P = δ Q P'
  proof: by
  ext ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [δ_eq_δAux]; rw [δ_eq_δAux]

中文:
引理 δ_eq_δ
  结论: δ Q P = δ Q P'
  证明: by
  ext ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [δ_eq_δAux]; rw [δ_eq_δAux]

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.mk_surjective, mk_surjective
-/
lemma δ_eq_δ : δ Q P = δ Q P' := by
  ext ⟨x, hx⟩
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  rw [δ_eq_δAux]; rw [δ_eq_δAux]

/--
lemma `exact_map_δ` / 引理 `exact_map_δ`

English:
lemma exact_map_δ
  proof: by
  simp only [δ]
  apply SnakeLemma.exact_δ_right
    (ι₂ := (Q.comp P).toExtension.h1Cotangentι)
    (hι₂ := LinearMap.exact_subtype_ker_map _)
  · ext x; rfl
  · exact Subtype.val_injective

中文:
引理 exact_map_δ
  证明: by
  simp only [δ]
  apply SnakeLemma.exact_δ_right
    (ι₂ := (Q.comp P).toExtension.h1Cotangentι)
    (hι₂ := LinearMap.exact_subtype_ker_map _)
  · ext x; rfl
  · exact Subtype.val_injective

Depends on / 依赖: LinearMap, LinearMap.exact_subtype_ker_map, Q.comp, SnakeLemma, SnakeLemma.exact_, Subtype, Subtype.val_injective, exact_subtype_ker_map, toExtension, toExtension.h1Cotangent, val_injective
-/
lemma exact_map_δ :
    Function.Exact (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) (δ Q P) := by
  simp only [δ]
  apply SnakeLemma.exact_δ_right
    (ι₂ := (Q.comp P).toExtension.h1Cotangentι)
    (hι₂ := LinearMap.exact_subtype_ker_map _)
  · ext x; rfl
  · exact Subtype.val_injective

set_option backward.isDefEq.respectTransparency false in
/--
lemma `δ_map` / 引理 `δ_map`

English:
lemma δ_map
  given: (f : Hom Q' Q) (x)
  proof: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  obtain ⟨x, hx⟩ := x
  obtain ⟨⟨y, hy⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  change δ _ _ ⟨_, _⟩ = δ _ _ _
  replace hx : (1 : T) otimesₜ[Q'.Ring] (D S Q'.Ring) y = 0 := by
    simpa only [LinearMap.mem_ker, Extension.cotangentC

中文:
引理 δ_map
  条件: (f : Hom Q' Q) (x)
  证明: by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  obtain ⟨x, hx⟩ := x
  obtain ⟨⟨y, hy⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  change δ _ _ ⟨_, _⟩ = δ _ _ _
  replace hx : (1 : T) otimesₜ[Q'.Ring] (D S Q'.Ring) y = 0 := by
    simpa only [LinearMap.mem_ker, Extension.cotangentC

Depends on / 依赖: AddCommGroup, Cotangent, Extension, Extension.Cotangent.map_mk, Extension.Cotangent.mk_surjective, Extension.cotangentComplex_mk, LinearMap, LinearMap.domRestrict_apply, LinearMap.mem_ker, RingHom, RingHom.mem_ker, add_zero, cotangentComplex_mk, domRestrict_apply, map_mk, map_zero, mem_ker, mk_surjective, otimes, replace
-/
lemma δ_map (f : Hom Q' Q) (x) :
    δ Q P (Extension.H1Cotangent.map f.toExtensionHom x) = δ Q' P' x := by
  let : AddCommGroup (T otimes[S] Ω[S⁄R]) := inferInstance
  obtain ⟨x, hx⟩ := x
  obtain ⟨⟨y, hy⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  change δ _ _ ⟨_, _⟩ = δ _ _ _
  replace hx : (1 : T) otimesₜ[Q'.Ring] (D S Q'.Ring) y = 0 := by
    simpa only [LinearMap.mem_ker, Extension.cotangentComplex_mk, ker, RingHom.mem_ker] using! hx
  simp only [LinearMap.domRestrict_apply, Extension.Cotangent.map_mk, δ_eq_δAux]
  refine (δAux_toAlgHom f _).trans ?_
  rw [hx]; rw [map_zero]; rw [map_zero]; rw [add_zero]

/--
lemma `δ_comp_equiv` / 引理 `δ_comp_equiv`

English:
lemma δ_comp_equiv
  proof: by
  ext x
  exact δ_map Q P Q' P' _ _

中文:
引理 δ_comp_equiv
  证明: by
  ext x
  exact δ_map Q P Q' P' _ _
-/
lemma δ_comp_equiv :
    δ Q P ∘ₗ (H1Cotangent.equiv _ _).toLinearMap = δ Q' P' := by
  ext x
  exact δ_map Q P Q' P' _ _

/--
lemma `exact_map_δ'` / 引理 `exact_map_δ'`

English:
lemma exact_map_δ'
  given: (f : Hom W Q)
  proof: by
  refine (H1Cotangent.equiv (Q.comp P) W).surjective.comp_exact_iff_exact.mp ?_
  change Function.Exact ((Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
    (Extension.H1Cotangent.map _)) (δ Q P)
  rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq _ (Q.ofCo

中文:
引理 exact_map_δ'
  条件: (f : Hom W Q)
  证明: by
  refine (H1Cotangent.equiv (Q.comp P) W).surjective.comp_exact_iff_exact.mp ?_
  change Function.Exact ((Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
    (Extension.H1Cotangent.map _)) (δ Q P)
  rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq _ (Q.ofCo

Depends on / 依赖: Extension, Extension.H1Cotangent.map, Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq, Function, Function.Exact, H1Cotangent, H1Cotangent.equiv, Q.comp, Q.ofComp, comp_exact_iff_exact, f.toExtensionHom, map_comp, map_eq, ofComp, restrictScalars, surjective, surjective.comp_exact_iff_exact.mp, toExtensionHom
-/
lemma exact_map_δ' (f : Hom W Q) :
    Function.Exact (Extension.H1Cotangent.map f.toExtensionHom) (δ Q P) := by
  refine (H1Cotangent.equiv (Q.comp P) W).surjective.comp_exact_iff_exact.mp ?_
  change Function.Exact ((Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
    (Extension.H1Cotangent.map _)) (δ Q P)
  rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq _ (Q.ofComp P).toExtensionHom]
  exact exact_map_δ Q P

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/--
lemma `liftBaseChange_range_le` / 引理 `liftBaseChange_range_le`

English:
lemma liftBaseChange_range_le
  proof: by
  rw [range_liftBaseChange]; rw [coe_range]; rw [Submodule.span_le]; rw [Set.range_subset_iff]
  rintro ⟨x, _⟩
  obtain ⟨⟨(x : P.Ring), x_in⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  ext; suffices (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom x) in Q.toExtension.ker ^ 2 by
    simpa [Ideal.t

中文:
引理 liftBaseChange_range_le
  证明: by
  rw [range_liftBaseChange]; rw [coe_range]; rw [Submodule.span_le]; rw [Set.range_subset_iff]
  rintro ⟨x, _⟩
  obtain ⟨⟨(x : P.Ring), x_in⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  ext; suffices (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom x) in Q.toExtension.ker ^ 2 by
    simpa [Ideal.t

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.mk_surjective, Generators, Generators.algebraMap_eq, Generators.ker, Generators.ker_eq_ker_aeval_val, Ideal.toCotangent_eq_zero, P.Ring, Q.ofComp, Q.toComp, Q.toExtension.ker, RingHom, RingHom.coe_coe, Set.range_subset_iff, Submodule, Submodule.span_le, algebraMap_eq, coe_coe, coe_range
-/
lemma liftBaseChange_range_le :
    (liftBaseChange T (Extension.H1Cotangent.map (Q.toComp P).toExtensionHom)).range <=
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom).ker := by
  rw [range_liftBaseChange]; rw [coe_range]; rw [Submodule.span_le]; rw [Set.range_subset_iff]
  rintro ⟨x, _⟩
  obtain ⟨⟨(x : P.Ring), x_in⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  ext; suffices (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom x) in Q.toExtension.ker ^ 2 by
    simpa [Ideal.toCotangent_eq_zero]
  rw [← Generators.ker]; rw [Generators.ker_eq_ker_aeval_val] at x_in
  rw [toComp_toAlgHom]; rw [toAlgHom_ofComp_rename]; rw [Generators.algebraMap_eq]; rw [RingHom.coe_coe]; rw [x_in]; rw [RingHom.map_zero]
  exact Ideal.zero_mem _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `auxMemKer` / 引理 `auxMemKer`

English:
lemma auxMemKer
  given: (z : T otimes[S] P.toExtension.H1Cotangent)
  proof: by
  induction z with
  | zero => simp
  | tmul x y => simp [← Extension.CotangentSpace.map_cotangentComplex]
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

中文:
引理 auxMemKer
  条件: (z : T otimes[S] P.toExtension.H1Cotangent)
  证明: by
  induction z with
  | zero => simp
  | tmul x y => simp [← Extension.CotangentSpace.map_cotangentComplex]
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
-/
private lemma auxMemKer (z : T otimes[S] P.toExtension.H1Cotangent) :
    LinearMap.liftBaseChange T (Extension.Cotangent.map (Q.toComp P).toExtensionHom)
      ((LinearMap.lTensor T Extension.h1Cotangentι) z) in
        (Q.comp P).toExtension.cotangentComplex.ker := by
  induction z with
  | zero => simp
  | tmul x y => simp [← Extension.CotangentSpace.map_cotangentComplex]
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/--
theorem `exact_liftBaseChange_map_of_flat` / 定理 `exact_liftBaseChange_map_of_flat`

English:
theorem exact_liftBaseChange_map_of_flat
  given: [Module.Flat S T]
  proof: by
  rw [exact_iff]
  refine le_antisymm ?_ (liftBaseChange_range_le Q P)
  rintro ⟨x, x_in⟩ hx
  replace hx : Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 := by
    simpa [← Extension.h1Cotangentι_injective.eq_iff] using hx
  rw [← mem_ker]; rw [(Cotangent.exact Q P).linearMap_ker_eq] 

中文:
定理 exact_liftBaseChange_map_of_flat
  条件: [Module.Flat S T]
  证明: by
  rw [exact_iff]
  refine le_antisymm ?_ (liftBaseChange_range_le Q P)
  rintro ⟨x, x_in⟩ hx
  replace hx : Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 := by
    simpa [← Extension.h1Cotangentι_injective.eq_iff] using hx
  rw [← mem_ker]; rw [(Cotangent.exact Q P).linearMap_ker_eq] 

Depends on / 依赖: Cotangent, Cotangent.exact, CotangentSpace, CotangentSpace.map_toComp_injective, Extension, Extension.Cotangent.map, Extension.h1Cotangent, Q.ofComp, Submod, _injective.eq_iff, comp_apply, eq_iff, exact_iff, ker_eq_bot, ker_eq_bot.mpr, le_antisymm, liftBaseChange_range_le, linearMap_ker_eq, map_comp_cotangentComplex_baseChange, map_toComp_injective
-/
theorem exact_liftBaseChange_map_of_flat [Module.Flat S T] :
    Function.Exact ((Extension.H1Cotangent.map (toComp Q P).toExtensionHom).liftBaseChange T)
      (Extension.H1Cotangent.map (ofComp Q P).toExtensionHom) := by
  rw [exact_iff]
  refine le_antisymm ?_ (liftBaseChange_range_le Q P)
  rintro ⟨x, x_in⟩ hx
  replace hx : Extension.Cotangent.map (Q.ofComp P).toExtensionHom x = 0 := by
    simpa [← Extension.h1Cotangentι_injective.eq_iff] using hx
  rw [← mem_ker]; rw [(Cotangent.exact Q P).linearMap_ker_eq] at hx
  rcases hx with ⟨x, rfl⟩
  rw [mem_ker]; rw [← comp_apply]; rw [← map_comp_cotangentComplex_baseChange]; rw [comp_apply]; rw [← mem_ker]; rw [ker_eq_bot.mpr (CotangentSpace.map_toComp_injective Q P)]; rw [Submodule.mem_bot]; rw [baseChange_eq_ltensor]; rw [← mem_ker]; rw [(Module.Flat.lTensor_exact T
      P.toExtension.exact_hCotangentι_cotangentComplex).linearMap_ker_eq] at x_in
  rcases x_in with ⟨x, rfl⟩
  use x; induction x with
  | zero => ext; simp
  | tmul x y => ext; simp
  | add x y hx hy => ext; simp [hx (auxMemKer Q P x), hy (auxMemKer Q P y)]

/--
theorem `exact_liftBaseChange_map_of_flat'` / 定理 `exact_liftBaseChange_map_of_flat'`

English:
theorem exact_liftBaseChange_map_of_flat'
  given: [Module.Flat S T] (f : Hom W Q) (g : Hom P W)
  proof: by
  rw [← LinearEquiv.conj_exact_iff_exact _ _ (H1Cotangent.equiv W (Q.comp P))]
  convert! exact_liftBaseChange_map_of_flat Q P
  · change Extension.H1Cotangent.map (W.defaultHom (Q.comp P)).toExtensionHom ∘ₗ _ = _
    rw [LinearMap.liftBaseChange_comp]; rw [← Extension.H1Cotangent.map_comp]; rw [

中文:
定理 exact_liftBaseChange_map_of_flat'
  条件: [Module.Flat S T] (f : Hom W Q) (g : Hom P W)
  证明: by
  rw [← LinearEquiv.conj_exact_iff_exact _ _ (H1Cotangent.equiv W (Q.comp P))]
  convert! exact_liftBaseChange_map_of_flat Q P
  · change Extension.H1Cotangent.map (W.defaultHom (Q.comp P)).toExtensionHom ∘ₗ _ = _
    rw [LinearMap.liftBaseChange_comp]; rw [← Extension.H1Cotangent.map_comp]; rw [

Depends on / 依赖: Extension, Extension.H1Cotangent.map, Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq, H1Cotangent, H1Cotangent.equiv, LinearEquiv, LinearEquiv.conj_exact_iff_exact, LinearMap, LinearMap.liftBaseChange_comp, Q.comp, W.defaultHom, conj_exact_iff_exact, convert, defaultHom, exact_liftBaseChange_map_of_flat, f.toExtensionHom, liftBaseChange_comp, map_comp, map_eq
-/
theorem exact_liftBaseChange_map_of_flat' [Module.Flat S T] (f : Hom W Q) (g : Hom P W) :
    Function.Exact ((Extension.H1Cotangent.map g.toExtensionHom).liftBaseChange T)
      (Extension.H1Cotangent.map f.toExtensionHom) := by
  rw [← LinearEquiv.conj_exact_iff_exact _ _ (H1Cotangent.equiv W (Q.comp P))]
  convert! exact_liftBaseChange_map_of_flat Q P
  · change Extension.H1Cotangent.map (W.defaultHom (Q.comp P)).toExtensionHom ∘ₗ _ = _
    rw [LinearMap.liftBaseChange_comp]; rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]
  · change (Extension.H1Cotangent.map f.toExtensionHom).restrictScalars T ∘ₗ
      (Extension.H1Cotangent.map _) = _
    rw [← Extension.H1Cotangent.map_comp]; rw [Extension.H1Cotangent.map_eq]

end H1Cotangent

end Generators

variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable (R S T)

/-- The connecting homomorphism in the Jacobi-Zariski sequence. -/
noncomputable
/--
Definition of `H1Cotangent.δ` / `H1Cotangent.δ` 的定义

English:
definition H1Cotangent.δ
  signature: : H1Cotangent S T ->ₗ[T] T otimes[S] Ω[S⁄R]
  body: Generators.H1Cotangent.δ (Generators.self S T) (Generators.self R S)

中文:
定义 H1Cotangent.δ
  签名: : H1Cotangent S T ->ₗ[T] T otimes[S] Ω[S⁄R]
  定义体: Generators.H1Cotangent.δ (Generators.self S T) (Generators.self R S)

Depends on / 依赖: Generators, Generators.H1Cotangent, Generators.self, H1Cotangent
-/
def H1Cotangent.δ : H1Cotangent S T ->ₗ[T] T otimes[S] Ω[S⁄R] :=
  Generators.H1Cotangent.δ (Generators.self S T) (Generators.self R S)

/-- Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/R}) \to H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R}$
is exact. -/
@[stacks 00S2]
/--
lemma `H1Cotangent.exact_map_δ` / 引理 `H1Cotangent.exact_map_δ`

English:
lemma H1Cotangent.exact_map_δ
  statement: Function.Exact (map R S T T) (δ R S T)
  proof: Generators.H1Cotangent.exact_map_δ' (Generators.self S T)
    (Generators.self R S) (Generators.self R T) (Generators.defaultHom _ _)

中文:
引理 H1Cotangent.exact_map_δ
  结论: Function.Exact (map R S T T) (δ R S T)
  证明: Generators.H1Cotangent.exact_map_δ' (Generators.self S T)
    (Generators.self R S) (Generators.self R T) (Generators.defaultHom _ _)

Depends on / 依赖: Generators, Generators.H1Cotangent.exact_map_, Generators.defaultHom, Generators.self, H1Cotangent, defaultHom
-/
lemma H1Cotangent.exact_map_δ : Function.Exact (map R S T T) (δ R S T) :=
  Generators.H1Cotangent.exact_map_δ' (Generators.self S T)
    (Generators.self R S) (Generators.self R T) (Generators.defaultHom _ _)

/-- Given algebras $R \to S \to T$, the sequence
$H_1(L_{T/S}) \to T \otimes_S \Omega_{S/R} \to \Omega_{T/R}$
is exact. -/
@[stacks 00S2]
/--
lemma `H1Cotangent.exact_δ_mapBaseChange` / 引理 `H1Cotangent.exact_δ_mapBaseChange`

English:
lemma H1Cotangent.exact_δ_mapBaseChange
  statement: Function.Exact (δ R S T) (mapBaseChange R S T)
  proof: Generators.H1Cotangent.exact_δ_map (Generators.self S T) (Generators.self R S)

中文:
引理 H1Cotangent.exact_δ_mapBaseChange
  结论: Function.Exact (δ R S T) (mapBaseChange R S T)
  证明: Generators.H1Cotangent.exact_δ_map (Generators.self S T) (Generators.self R S)

Depends on / 依赖: Generators, Generators.H1Cotangent.exact_, Generators.self, H1Cotangent
-/
lemma H1Cotangent.exact_δ_mapBaseChange : Function.Exact (δ R S T) (mapBaseChange R S T) :=
  Generators.H1Cotangent.exact_δ_map (Generators.self S T) (Generators.self R S)

/-- Given algebras $R \to S \to T$ and $T$ flat over $S$, the sequence
$T \otimes_S H_1(L_{S/R}) \to H_1(L_{T/R}) \to H_1(L_{T/S})$
is exact. -/
@[stacks 00S2]
/--
lemma `H1Cotangent.exact_liftBaseChange_map_of_flat` / 引理 `H1Cotangent.exact_liftBaseChange_map_of_flat`

English:
lemma H1Cotangent.exact_liftBaseChange_map_of_flat
  given: [Module.Flat S T]
  proof: Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'
    (Generators.self S T) (Generators.self R S) (Generators.self R T)
    (Generators.defaultHom _ _) (Generators.defaultHom _ _)

中文:
引理 H1Cotangent.exact_liftBaseChange_map_of_flat
  条件: [Module.Flat S T]
  证明: Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'
    (Generators.self S T) (Generators.self R S) (Generators.self R T)
    (Generators.defaultHom _ _) (Generators.defaultHom _ _)

Depends on / 依赖: Generators, Generators.H1Cotangent.exact_liftBaseChange_map_of_flat, Generators.defaultHom, Generators.self, H1Cotangent, defaultHom, exact_liftBaseChange_map_of_flat
-/
lemma H1Cotangent.exact_liftBaseChange_map_of_flat [Module.Flat S T] :
    Function.Exact ((map R R S T).liftBaseChange T) (map R S T T) :=
  Generators.H1Cotangent.exact_liftBaseChange_map_of_flat'
    (Generators.self S T) (Generators.self R S) (Generators.self R T)
    (Generators.defaultHom _ _) (Generators.defaultHom _ _)

end Algebra
