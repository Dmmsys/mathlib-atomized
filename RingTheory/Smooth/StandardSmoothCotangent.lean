/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Etale.Basic

/-!
# Cotangent complex of a submersive presentation

Let `P` be a submersive presentation of `S` as an `R`-algebra and
denote by `I` the kernel `R[X] → S`. We show

- `SubmersivePresentation.free_cotangent`: `I ⧸ I ^ 2` is `S`-free on the classes of `P.relation i`.
- `SubmersivePresentation.subsingleton_h1Cotangent`: `H¹(L_{S/R}) = 0`.
- `SubmersivePresentation.free_kaehlerDifferential`: `Ω[S⁄R]` is `S`-free on the images of `dxᵢ`
  where `i ∉ Set.range P.map`.
- `SubmersivePresentation.rank_kaehlerDifferential`: If `S` is non-trivial, the rank of
  `Ω[S⁄R]` is the dimension of `P`.

We also provide the corresponding instances for standard smooth algebras as corollaries.

We keep the notation `I = ker(R[X] → S)` in all docstrings of this file.
-/

@[expose] public section

namespace Algebra

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

section

open Extension Module MvPolynomial

namespace PreSubmersivePresentation

/--
Definition of `cotangentComplexAux` / `cotangentComplexAux` 的定义

English:
definition cotangentComplexAux
  signature: [Finite σ] (P : PreSubmersivePresentation R S ι σ)
  body: Finsupp.linearEquivFunOnFinite S S σ ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

中文:
定义 cotangentComplexAux
  签名: [有限 σ] (P : PreSubmersivePresentation R S ι σ)
  定义体: Finsupp.linearEquivFunOnFinite S S σ ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

Depends on / 依赖: Finsupp, Finsupp.lcomapDomain, Finsupp.linearEquivFunOnFinite, P.cotangentSpaceBasis.repr.toLinearMap, P.map_inj, P.toExtension.cotangentComplex, cotangentComplex, cotangentSpaceBasis, lcomapDomain, linearEquivFunOnFinite, map_inj, toExtension, toLinearMap
-/
noncomputable def cotangentComplexAux [Finite σ] (P : PreSubmersivePresentation R S ι σ) :
    P.toExtension.Cotangent ->ₗ[S] σ -> S :=
  Finsupp.linearEquivFunOnFinite S S σ ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentComplexAux_apply` / 引理 `cotangentComplexAux_apply`

English:
lemma cotangentComplexAux_apply
  statement: [Finite σ] (P : PreSubmersivePresentation R S ι σ)
  proof: by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]

中文:
引理 cotangentComplexAux_apply
  结论: [有限 σ] (P : PreSubmersivePresentation R S ι σ)
  证明: by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]

Depends on / 依赖: Finsupp, Finsupp.comapDomain_apply, Finsupp.lcomapDomain_apply, Finsupp.linearEquivFunOnFinite_apply, Function, Function.comp_apply, Generators, Generators.cotangentSpaceBasis_repr_tmul, Generators.toExtension_Ring, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, comapDomain_apply, comp_apply, cotangentComplexAux, cotangentComplex_mk, cotangentSpaceBasis_repr_tmul
-/
lemma cotangentComplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ)
    (x : P.ker) (i : σ) :
    P.cotangentComplexAux (Cotangent.mk x) i = (aeval P.val) (pderiv (P.map i) x.val) := by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]

/--
lemma `cotangentComplexAux_zero_iff` / 引理 `cotangentComplexAux_zero_iff`

English:
lemma cotangentComplexAux_zero_iff
  given: [Finite σ] {P : PreSubmersivePresentation R S ι σ} (x : P.ker)
  proof: by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

中文:
引理 cotangentComplexAux_zero_iff
  条件: [有限 σ] {P : PreSubmersivePresentation R S ι σ} (x : P.ker)
  证明: by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

Depends on / 依赖: Pi.zero_apply, cotangentComplexAux_apply, funext_iff, simp_rw, zero_apply
-/
lemma cotangentComplexAux_zero_iff [Finite σ] {P : PreSubmersivePresentation R S ι σ} (x : P.ker) :
    P.cotangentComplexAux (Cotangent.mk x) = 0 ↔
      forall i : σ, (aeval P.val) (pderiv (P.map i) x.val) = 0 := by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

end PreSubmersivePresentation

namespace SubmersivePresentation

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cotangentComplexAux_injective` / 引理 `cotangentComplexAux_injective`

English:
lemma cotangentComplexAux_injective
  statement: Function.Injective P.cotangentComplexAux
  proof: by
  rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot]; rw [Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker]; rw [P.cotangentComplexAux_zero_iff] at hx
  have : x.val in Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : σ) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a => a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i in c.support,
      aeval P.val (c i) • (fun j => aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : σ) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i => aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  change _ in P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

中文:
引理 cotangentComplexAux_injective
  结论: 函数.单射 P.cotangentComplexAux
  证明: by
  rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot]; rw [Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker]; rw [P.cotangentComplexAux_zero_iff] at hx
  have : x.val in Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : σ) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a => a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i in c.support,
      aeval P.val (c i) • (fun j => aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : σ) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i => aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  change _ in P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

Depends on / 依赖: Cotangent, Cotangent.mk_eq_zero_iff, Cotangent.mk_surjective, Finsupp, Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp, Ideal.span, LinearMap, LinearMap.ker_eq_bot, LinearMap.mem_ker, P.cotangentComplexAux_zero_iff, P.ker, P.map, P.relation, P.span_range_relation_eq_ker, P.val, Set.range, Submodule, Submodule.mem_bot, c.sum, cotangentComplexAux_zero_iff
-/
lemma cotangentComplexAux_injective : Function.Injective P.cotangentComplexAux := by
  rw [← LinearMap.ker_eq_bot]; rw [eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot]; rw [Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker]; rw [P.cotangentComplexAux_zero_iff] at hx
  have : x.val in Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : σ) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a => a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i in c.support,
      aeval P.val (c i) • (fun j => aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : σ) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i => aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  change _ in P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cotangentComplexAux_surjective` / 引理 `cotangentComplexAux_surjective`

English:
lemma cotangentComplexAux_surjective
  statement: Function.Surjective P.cotangentComplexAux
  proof: by
  rw [← LinearMap.range_eq_top]; rw [_root_.eq_top_iff]; rw [← P.basisDeriv.span_eq]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp

中文:
引理 cotangentComplexAux_surjective
  结论: 函数.满射 P.cotangentComplexAux
  证明: by
  rw [← LinearMap.range_eq_top]; rw [_root_.eq_top_iff]; rw [← P.basisDeriv.span_eq]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp

Depends on / 依赖: Cotangent, Cotangent.mk, LinearMap, LinearMap.range_eq_top, P.basisDeriv.span_eq, P.cotangentComplexAux_apply, P.relation, P.relation_mem_ker, Submodule, Submodule.span_le, _root_, _root_.eq_top_iff, basisDeriv, cotangentComplexAux_apply, eq_top_iff, range_eq_top, relation, relation_mem_ker, span_eq, span_le
-/
lemma cotangentComplexAux_surjective : Function.Surjective P.cotangentComplexAux := by
  rw [← LinearMap.range_eq_top]; rw [_root_.eq_top_iff]; rw [← P.basisDeriv.span_eq]; rw [Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp

/-- The isomorphism of `S`-modules between `I ⧸ I ^ 2` and `σ → S` given
by `P.relation i ↦ ∂ⱼ (P.relation i)`. -/
@[simps! apply]
/--
Definition of `cotangentEquiv` / `cotangentEquiv` 的定义

English:
definition cotangentEquiv
  signature: : P.toExtension.Cotangent ≃ₗ[S] σ -> S
  body: LinearEquiv.ofBijective _ ⟨P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective⟩

中文:
定义 cotangentEquiv
  签名: : P.toExtension.余切 ≃ₗ[S] σ -> S
  定义体: LinearEquiv.ofBijective _ ⟨P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective, cotangentComplexAux_injective, cotangentComplexAux_surjective, ofBijective
-/
noncomputable def cotangentEquiv : P.toExtension.Cotangent ≃ₗ[S] σ -> S :=
  LinearEquiv.ofBijective _ ⟨P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective⟩

/--
lemma `cotangentComplex_injective` / 引理 `cotangentComplex_injective`

English:
lemma cotangentComplex_injective
  statement: Function.Injective P.toExtension.cotangentComplex
  proof: by
  have := P.cotangentComplexAux_injective
  simp only [PreSubmersivePresentation.cotangentComplexAux, LinearMap.coe_comp,
    LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp <| Function.Injective.of_comp this)

中文:
引理 cotangentComplex_injective
  结论: 函数.单射 P.toExtension.cotangentComplex
  证明: by
  have := P.cotangentComplexAux_injective
  simp only [PreSubmersivePresentation.cotangentComplexAux, LinearMap.coe_comp,
    LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp <| Function.Injective.of_comp this)

Depends on / 依赖: Function, Function.Injective.of_comp, Injective, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, P.cotangentComplexAux_injective, PreSubmersivePresentation, PreSubmersivePresentation.cotangentComplexAux, coe_coe, coe_comp, cotangentComplexAux, cotangentComplexAux_injective, of_comp
-/
lemma cotangentComplex_injective : Function.Injective P.toExtension.cotangentComplex := by
  have := P.cotangentComplexAux_injective
  simp only [PreSubmersivePresentation.cotangentComplexAux, LinearMap.coe_comp,
    LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp <| Function.Injective.of_comp this)

/--
Instance `subsingleton_h1Cotangent` / 实例 `subsingleton_h1Cotangent`

English:
instance subsingleton_h1Cotangent
  signature: : Subsingleton P.toExtension.H1Cotangent
  body: by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

中文:
实例 subsingleton_h1Cotangent
  签名: : 子单例 P.toExtension.H1Cotangent
  定义体: by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

Depends on / 依赖: Algebra, Algebra.Extension.subsingleton_h1Cotangent, Extension, cotangentComplex_injective, subsingleton_h1Cotangent
-/
instance subsingleton_h1Cotangent : Subsingleton P.toExtension.H1Cotangent := by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

/-- The classes of `P.relation i` form a basis of `I ⧸ I ^ 2`. -/
@[stacks 00T7 "(3)"]
/--
Definition of `basisCotangent` / `basisCotangent` 的定义

English:
definition basisCotangent
  signature: : Basis σ S P.toExtension.Cotangent
  body: P.basisDeriv.map P.cotangentEquiv.symm

中文:
定义 basisCotangent
  签名: : 基 σ S P.toExtension.余切
  定义体: P.basisDeriv.map P.cotangentEquiv.symm

Depends on / 依赖: P.basisDeriv.map, P.cotangentEquiv.symm, basisDeriv, cotangentEquiv
-/
noncomputable def basisCotangent : Basis σ S P.toExtension.Cotangent :=
  P.basisDeriv.map P.cotangentEquiv.symm

/--
lemma `basisCotangent_apply` / 引理 `basisCotangent_apply`

English:
lemma basisCotangent_apply
  given: (r : σ)
  proof: by
  symm
  apply P.cotangentEquiv.injective
  ext
  simp_rw [basisCotangent, Basis.map_apply, LinearEquiv.apply_symm_apply, basisDeriv_apply]
  apply P.toPreSubmersivePresentation.cotangentComplexAux_apply _ _

@[stacks 00T7 "(3)"]

中文:
引理 basisCotangent_apply
  条件: (r : σ)
  证明: by
  symm
  apply P.cotangentEquiv.injective
  ext
  simp_rw [basisCotangent, Basis.map_apply, LinearEquiv.apply_symm_apply, basisDeriv_apply]
  apply P.toPreSubmersivePresentation.cotangentComplexAux_apply _ _

@[stacks 00T7 "(3)"]

Depends on / 依赖: Basis.map_apply, LinearEquiv, LinearEquiv.apply_symm_apply, P.cotangentEquiv.injective, P.toPreSubmersivePresentation.cotangentComplexAux_apply, apply_symm_apply, basisCotangent, basisDeriv_apply, cotangentComplexAux_apply, cotangentEquiv, injective, map_apply, simp_rw, toPreSubmersivePresentation
-/
lemma basisCotangent_apply (r : σ) :
    P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩ := by
  symm
  apply P.cotangentEquiv.injective
  ext
  simp_rw [basisCotangent, Basis.map_apply, LinearEquiv.apply_symm_apply, basisDeriv_apply]
  apply P.toPreSubmersivePresentation.cotangentComplexAux_apply _ _

@[stacks 00T7 "(3)"]
/--
Instance `free_cotangent` / 实例 `free_cotangent`

English:
instance free_cotangent
  signature: : Module.Free S P.toExtension.Cotangent
  body: Module.Free.of_basis P.basisCotangent

中文:
实例 free_cotangent
  签名: : 模.自由 S P.toExtension.余切
  定义体: Module.Free.of_basis P.basisCotangent

Depends on / 依赖: Continuous, Continuous.prodMk_left, Module, Module.Free.of_basis, P.basisCotangent, Prod.mk, basisCotangent, continuousOn, exacts, fun_prop, hs.image, ht.image, isPreconnected_of_forall_pair, of_basis, prodMk_left
-/
instance free_cotangent : Module.Free S P.toExtension.Cotangent :=
  Module.Free.of_basis P.basisCotangent

/--
Definition of `sectionCotangent` / `sectionCotangent` 的定义

English:
definition sectionCotangent
  signature: : P.toExtension.CotangentSpace ->ₗ[S] P.toExtension.Cotangent
  body: (cotangentEquiv P).symm ∘ₗ (Finsupp.linearEquivFunOnFinite S S σ).toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ P.map_inj ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap

中文:
定义 sectionCotangent
  签名: : P.toExtension.CotangentSpace ->ₗ[S] P.toExtension.余切
  定义体: (cotangentEquiv P).symm ∘ₗ (Finsupp.linearEquivFunOnFinite S S σ).toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ P.map_inj ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap

Depends on / 依赖: Finsupp, Finsupp.lcomapDomain, Finsupp.linearEquivFunOnFinite, P.cotangentSpaceBasis.repr.toLinearMap, P.map_inj, cotangentEquiv, cotangentSpaceBasis, lcomapDomain, linearEquivFunOnFinite, map_inj, toLinearMap
-/
noncomputable def sectionCotangent : P.toExtension.CotangentSpace ->ₗ[S] P.toExtension.Cotangent :=
  (cotangentEquiv P).symm ∘ₗ (Finsupp.linearEquivFunOnFinite S S σ).toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ P.map_inj ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap

/--
lemma `sectionCotangent_eq_iff` / 引理 `sectionCotangent_eq_iff`

English:
lemma sectionCotangent_eq_iff
  given: (x : P.toExtension.CotangentSpace) (y : P.toExtension.Cotangent)
  proof: by
  simp only [sectionCotangent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← (cotangentEquiv P).injective.eq_iff]; rw [funext_iff]; rw [LinearEquiv.apply_symm_apply]
  simp

中文:
引理 sectionCotangent_eq_iff
  条件: (x : P.toExtension.CotangentSpace) (y : P.toExtension.余切)
  证明: by
  simp only [sectionCotangent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← (cotangentEquiv P).injective.eq_iff]; rw [funext_iff]; rw [LinearEquiv.apply_symm_apply]
  simp
-/
lemma sectionCotangent_eq_iff (x : P.toExtension.CotangentSpace) (y : P.toExtension.Cotangent) :
    sectionCotangent P x = y ↔
      forall i : σ, P.cotangentSpaceBasis.repr x (P.map i) = (P.cotangentComplexAux y) i := by
  simp only [sectionCotangent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← (cotangentEquiv P).injective.eq_iff]; rw [funext_iff]; rw [LinearEquiv.apply_symm_apply]
  simp

/--
lemma `sectionCotangent_comp` / 引理 `sectionCotangent_comp`

English:
lemma sectionCotangent_comp
  proof: by
  ext : 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [sectionCotangent_eq_iff]
  intro i
  rfl

中文:
引理 sectionCotangent_comp
  证明: by
  ext : 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [sectionCotangent_eq_iff]
  intro i
  rfl
-/
lemma sectionCotangent_comp :
    sectionCotangent P ∘ₗ P.toExtension.cotangentComplex = LinearMap.id := by
  ext : 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [sectionCotangent_eq_iff]
  intro i
  rfl

/--
lemma `sectionCotangent_zero_of_notMem_range` / 引理 `sectionCotangent_zero_of_notMem_range`

English:
lemma sectionCotangent_zero_of_notMem_range
  given: (i : ι) (hi : i ∉ Set.range P.map)
  proof: by
  classical
  contrapose hi
  rw [sectionCotangent_eq_iff] at hi
  simp only [Basis.repr_self, map_zero, Pi.zero_apply, Finsupp.single_apply] at hi
  grind

中文:
引理 sectionCotangent_zero_of_notMem_range
  条件: (i : ι) (hi : i ∉ 集合.range P.map)
  证明: by
  classical
  contrapose hi
  rw [sectionCotangent_eq_iff] at hi
  simp only [Basis.repr_self, map_zero, Pi.zero_apply, Finsupp.single_apply] at hi
  grind

Depends on / 依赖: Basis.repr_self, Finsupp, Finsupp.single_apply, Pi.zero_apply, classical, contrapose, map_zero, repr_self, sectionCotangent_eq_iff, single_apply, zero_apply
-/
lemma sectionCotangent_zero_of_notMem_range (i : ι) (hi : i ∉ Set.range P.map) :
    (sectionCotangent P) (P.cotangentSpaceBasis i) = 0 := by
  classical
  contrapose hi
  rw [sectionCotangent_eq_iff] at hi
  simp only [Basis.repr_self, map_zero, Pi.zero_apply, Finsupp.single_apply] at hi
  grind

/--
Definition of `basisKaehlerOfIsCompl` / `basisKaehlerOfIsCompl` 的定义

English:
definition basisKaehlerOfIsCompl
  signature: {κ : Type*} {f : κ -> ι}
  body: by
  apply P.cotangentSpaceBasis.ofSplitExact (sectionCotangent_comp P)
    Extension.exact_cotangentComplex_toKaehler Extension.toKaehler_surjective hf (b := P.map)
  · intro i
    apply sectionCotangent_zero_of_notMem_range _ _
    simp [← hcompl.compl_eq]
  · simp only [sectionCotangent, LinearMap.coe_comp, Function.comp_assoc, LinearEquiv.coe_coe]
    apply LinearIndependent.map' _ _ P.cotangentEquiv.symm.ker
    convert! (Pi.basisFun S σ).linearIndependent
    classical
    ext i j
    simp only [Function.comp_apply, Basis.repr_self, Finsupp.linearEquivFunOnFinite_apply,
      Pi.basisFun_apply]
    simp [Finsupp.single_eq_pi_single]
  · exact hcompl.2

@[simp]

中文:
定义 basisKaehlerOfIsCompl
  签名: {κ : 类型} {f : κ -> ι}
  定义体: by
  apply P.cotangentSpaceBasis.ofSplitExact (sectionCotangent_comp P)
    Extension.exact_cotangentComplex_toKaehler Extension.toKaehler_surjective hf (b := P.map)
  · intro i
    apply sectionCotangent_zero_of_notMem_range _ _
    simp [← hcompl.compl_eq]
  · simp only [sectionCotangent, LinearMap.coe_comp, Function.comp_assoc, LinearEquiv.coe_coe]
    apply LinearIndependent.map' _ _ P.cotangentEquiv.symm.ker
    convert! (Pi.basisFun S σ).linearIndependent
    classical
    ext i j
    simp only [Function.comp_apply, Basis.repr_self, Finsupp.linearEquivFunOnFinite_apply,
      Pi.basisFun_apply]
    simp [Finsupp.single_eq_pi_single]
  · exact hcompl.2

@[simp]

Depends on / 依赖: Basis.repr, Extension, Extension.exact_cotangentComplex_toKaehler, Extension.toKaehler_surjective, Function, Function.comp_apply, Function.comp_assoc, LinearEquiv, LinearEquiv.coe_coe, LinearIndependent, LinearIndependent.map, LinearMap, LinearMap.coe_comp, P.cotangentEquiv.symm.ker, P.cotangentSpaceBasis.ofSplitExact, P.map, Pi.basisFun, basisFun, classical, coe_coe
-/
noncomputable def basisKaehlerOfIsCompl {κ : Type*} {f : κ -> ι}
    (hf : Function.Injective f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) :
    Basis κ S Ω[S⁄R] := by
  apply P.cotangentSpaceBasis.ofSplitExact (sectionCotangent_comp P)
    Extension.exact_cotangentComplex_toKaehler Extension.toKaehler_surjective hf (b := P.map)
  · intro i
    apply sectionCotangent_zero_of_notMem_range _ _
    simp [← hcompl.compl_eq]
  · simp only [sectionCotangent, LinearMap.coe_comp, Function.comp_assoc, LinearEquiv.coe_coe]
    apply LinearIndependent.map' _ _ P.cotangentEquiv.symm.ker
    convert! (Pi.basisFun S σ).linearIndependent
    classical
    ext i j
    simp only [Function.comp_apply, Basis.repr_self, Finsupp.linearEquivFunOnFinite_apply,
      Pi.basisFun_apply]
    simp [Finsupp.single_eq_pi_single]
  · exact hcompl.2

@[simp]
/--
lemma `basisKaehlerOfIsCompl_apply` / 引理 `basisKaehlerOfIsCompl_apply`

English:
lemma basisKaehlerOfIsCompl_apply
  statement: {κ : Type*} {f : κ -> ι}
  proof: by
  simp [basisKaehlerOfIsCompl]

中文:
引理 basisKaehlerOfIsCompl_apply
  结论: {κ : 类型} {f : κ -> ι}
  证明: by
  simp [basisKaehlerOfIsCompl]

Depends on / 依赖: basisKaehlerOfIsCompl
-/
lemma basisKaehlerOfIsCompl_apply {κ : Type*} {f : κ -> ι}
    (hf : Function.Injective f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) (k : κ) :
    P.basisKaehlerOfIsCompl hf hcompl k = KaehlerDifferential.D _ _ (P.val (f k)) := by
  simp [basisKaehlerOfIsCompl]

/-- Given a submersive presentation of `S` as `R`-algebra, the images of `dxᵢ`
for `i` in the complement of `σ` in `ι` form a basis of `Ω[S⁄R]`. -/
@[stacks 00T7 "(2)"]
/--
Definition of `basisKaehler` / `basisKaehler` 的定义

English:
definition basisKaehler
  signature: :
  body: P.basisKaehlerOfIsCompl Subtype.val_injective by
    rw [Subtype.range_coe_subtype]
    exact IsCompl.symm isCompl_compl

@[simp]

中文:
定义 basisKaehler
  签名: :
  定义体: P.basisKaehlerOfIsCompl Subtype.val_injective by
    rw [Subtype.range_coe_subtype]
    exact IsCompl.symm isCompl_compl

@[simp]

Depends on / 依赖: IsCompl, IsCompl.symm, P.basisKaehlerOfIsCompl, Subtype, Subtype.range_coe_subtype, Subtype.val_injective, basisKaehlerOfIsCompl, isCompl_compl, range_coe_subtype, val_injective
-/
noncomputable def basisKaehler :
    Basis ((Set.range P.map)ᶜ : Set _) S Ω[S⁄R] :=
P.basisKaehlerOfIsCompl Subtype.val_injective by
    rw [Subtype.range_coe_subtype]
    exact IsCompl.symm isCompl_compl

@[simp]
/--
lemma `basisKaehler_apply` / 引理 `basisKaehler_apply`

English:
lemma basisKaehler_apply
  given: (k : ((Set.range P.map)ᶜ : Set _))
  proof: by
  simp [basisKaehler]

中文:
引理 basisKaehler_apply
  条件: (k : ((集合.range P.map)ᶜ : 集合 _))
  证明: by
  simp [basisKaehler]

Depends on / 依赖: basisKaehler
-/
lemma basisKaehler_apply (k : ((Set.range P.map)ᶜ : Set _)) :
    P.basisKaehler k = KaehlerDifferential.D _ _ (P.val k) := by
  simp [basisKaehler]

/-- If `P` is a submersive presentation of `S` as an `R`-algebra, `Ω[S⁄R]` is free. -/
@[stacks 00T7 "(2)"]
/--
theorem `free_kaehlerDifferential` / 定理 `free_kaehlerDifferential`

English:
theorem free_kaehlerDifferential
  given: (P : SubmersivePresentation R S ι σ)
  proof: Module.Free.of_basis P.basisKaehler

中文:
定理 free_kaehlerDifferential
  条件: (P : 浸没呈现 R S ι σ)
  证明: Module.Free.of_basis P.basisKaehler

Depends on / 依赖: Module, Module.Free.of_basis, P.basisKaehler, basisKaehler, of_basis
-/
theorem free_kaehlerDifferential (P : SubmersivePresentation R S ι σ) :
    Module.Free S Ω[S⁄R] :=
  Module.Free.of_basis P.basisKaehler

attribute [local instance] Fintype.ofFinite in
/--
theorem `rank_kaehlerDifferential` / 定理 `rank_kaehlerDifferential`

English:
theorem rank_kaehlerDifferential
  statement: [Nontrivial S] [Finite ι]
  proof: by
  simp only [rank_eq_card_basis P.basisKaehler, Fintype.card_compl_set,
    Presentation.dimension, Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]

中文:
定理 rank_kaehlerDifferential
  结论: [非平凡 S] [有限 ι]
  证明: by
  simp only [rank_eq_card_basis P.basisKaehler, Fintype.card_compl_set,
    Presentation.dimension, Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]

Depends on / 依赖: Fintype, Fintype.card_compl_set, Nat.card_eq_fintype_card, P.basisKaehler, P.map_inj, Presentation, Presentation.dimension, Set.card_range_of_injective, basisKaehler, card_compl_set, card_eq_fintype_card, card_range_of_injective, dimension, map_inj, rank_eq_card_basis
-/
theorem rank_kaehlerDifferential [Nontrivial S] [Finite ι]
    (P : SubmersivePresentation R S ι σ) : Module.rank S Ω[S⁄R] = P.dimension := by
  simp only [rank_eq_card_basis P.basisKaehler, Fintype.card_compl_set,
    Presentation.dimension, Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]

end SubmersivePresentation

section LocalizationAway

variable (r : R) [IsLocalization.Away r S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free S (Generators.localizationAway S r).toExtension.Cotangent
  body: inferInstanceAs
    Module.Free S ((SubmersivePresentation.localizationAway S r).toExtension.Cotangent)

中文:
实例 :
  签名: 模.自由 S (生成元.localizationAway S r).toExtension.余切
  定义体: inferInstanceAs
    Module.Free S ((SubmersivePresentation.localizationAway S r).toExtension.Cotangent)

Depends on / 依赖: Cotangent, Module, Module.Free, SubmersivePresentation, SubmersivePresentation.localizationAway, localizationAway, toExtension, toExtension.Cotangent
-/
instance : Module.Free S (Generators.localizationAway S r).toExtension.Cotangent :=
inferInstanceAs
    Module.Free S ((SubmersivePresentation.localizationAway S r).toExtension.Cotangent)

variable (S) in
/-- The image of `g * X - 1` in `I/I²` if `I` is the kernel of the canonical presentation
of the localization of `S` away from `g`. -/
noncomputable
/--
Definition of `Generators.cMulXSubOneCotangent` / `Generators.cMulXSubOneCotangent` 的定义

English:
abbreviation Generators.cMulXSubOneCotangent
  signature: : (Generators.localizationAway S r).toExtension.Cotangent
  body: Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩

中文:
缩写 生成元.cMulXSubOneCotangent
  签名: : (生成元.localizationAway S r).toExtension.余切
  定义体: Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩

Depends on / 依赖: C_mul_X_sub_one_mem_ker, Cotangent, Extension, Extension.Cotangent.mk
-/
abbrev Generators.cMulXSubOneCotangent : (Generators.localizationAway S r).toExtension.Cotangent :=
  Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩

/--
lemma `Generators.cMulXSubOneCotangent_eq` / 引理 `Generators.cMulXSubOneCotangent_eq`

English:
lemma Generators.cMulXSubOneCotangent_eq
  proof: rfl

中文:
引理 生成元.cMulXSubOneCotangent_eq
  证明: rfl
-/
lemma Generators.cMulXSubOneCotangent_eq :
    cMulXSubOneCotangent S r = Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩ :=
  rfl

/--
lemma `SubmersivePresentation.basisCotangent_localizationAway_apply` / 引理 `SubmersivePresentation.basisCotangent_localizationAway_apply`

English:
lemma SubmersivePresentation.basisCotangent_localizationAway_apply
  given: (x : Unit)
  proof: basisCotangent_apply _ _

中文:
引理 浸没呈现.basisCotangent_localizationAway_apply
  条件: (x : 单元)
  证明: basisCotangent_apply _ _

Depends on / 依赖: basisCotangent_apply
-/
lemma SubmersivePresentation.basisCotangent_localizationAway_apply (x : Unit) :
    (SubmersivePresentation.localizationAway S r).basisCotangent x =
      Generators.cMulXSubOneCotangent S r :=
  basisCotangent_apply _ _

variable (S) in
/--
The basis of `(g * X - 1) / (g * X - 1)²` given by the image of `g * X - 1`.

This is def-eq to `(SubmersivePresentation.localizationAway T g).basisCotangent`, but
```
(SubmersivePresentation.localizationAway T g).toExtension =
  (Generators.localizationAway T g).toExtension
```
is not reducibly def-eq. Hence using the general `SubmersivePresentation.basisCotangent` leads
to `erw` hell.
-/
noncomputable
/--
Definition of `Generators.basisCotangentAway` / `Generators.basisCotangentAway` 的定义

English:
definition Generators.basisCotangentAway
  signature: (r : R) [IsLocalization.Away r S]
  body: (SubmersivePresentation.localizationAway S r).basisCotangent

中文:
定义 生成元.basisCotangentAway
  签名: (r : R) [是Localization.Away r S]
  定义体: (SubmersivePresentation.localizationAway S r).basisCotangent

Depends on / 依赖: SubmersivePresentation, SubmersivePresentation.localizationAway, basisCotangent, localizationAway
-/
def Generators.basisCotangentAway (r : R) [IsLocalization.Away r S] :
    Module.Basis Unit S (localizationAway S r).toExtension.Cotangent :=
  (SubmersivePresentation.localizationAway S r).basisCotangent

/--
lemma `Generators.basisCotangentAway_apply` / 引理 `Generators.basisCotangentAway_apply`

English:
lemma Generators.basisCotangentAway_apply
  given: (x : Unit)
  proof: SubmersivePresentation.basisCotangent_apply _ _

中文:
引理 生成元.basisCotangentAway_apply
  条件: (x : 单元)
  证明: SubmersivePresentation.basisCotangent_apply _ _

Depends on / 依赖: SubmersivePresentation, SubmersivePresentation.basisCotangent_apply, basisCotangent_apply
-/
lemma Generators.basisCotangentAway_apply (x : Unit) :
    basisCotangentAway S r x = cMulXSubOneCotangent S r :=
  SubmersivePresentation.basisCotangent_apply _ _

end LocalizationAway

/--
Instance `IsStandardSmooth.free_kaehlerDifferential` / 实例 `IsStandardSmooth.free_kaehlerDifferential`

English:
instance IsStandardSmooth.free_kaehlerDifferential
  signature: [IsStandardSmooth R S]
  body: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.free_kaehlerDifferential

中文:
实例 是StandardSmooth.free_kaehlerDifferential
  签名: [是StandardSmooth R S]
  定义体: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.free_kaehlerDifferential

Depends on / 依赖: IsStandardSmooth, P.free_kaehlerDifferential, free_kaehlerDifferential
-/
instance IsStandardSmooth.free_kaehlerDifferential [IsStandardSmooth R S] :
    Module.Free S Ω[S⁄R] := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.free_kaehlerDifferential

/--
Instance `IsStandardSmooth.subsingleton_h1Cotangent` / 实例 `IsStandardSmooth.subsingleton_h1Cotangent`

English:
instance IsStandardSmooth.subsingleton_h1Cotangent
  signature: [IsStandardSmooth R S]
  body: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.equivH1Cotangent.symm.toEquiv.subsingleton

中文:
实例 是StandardSmooth.subsingleton_h1Cotangent
  签名: [是StandardSmooth R S]
  定义体: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.equivH1Cotangent.symm.toEquiv.subsingleton

Depends on / 依赖: IsStandardSmooth, P.equivH1Cotangent.symm.toEquiv.subsingleton, equivH1Cotangent, subsingleton, toEquiv
-/
instance IsStandardSmooth.subsingleton_h1Cotangent [IsStandardSmooth R S] :
    Subsingleton (H1Cotangent R S) := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.equivH1Cotangent.symm.toEquiv.subsingleton

/--
theorem `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` / 定理 `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`

English:
theorem IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
  statement: [Nontrivial S] (n : Nat)
  proof: by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  rw [P.rank_kaehlerDifferential]; rw [hP]

中文:
定理 是StandardSmoothOfRelativeDimension.rank_kaehlerDifferential
  结论: [非平凡 S] (n : 自然数)
  证明: by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  rw [P.rank_kaehlerDifferential]; rw [hP]

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, P.rank_kaehlerDifferential, rank_kaehlerDifferential
-/
theorem IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential [Nontrivial S] (n : Nat)
    [IsStandardSmoothOfRelativeDimension n R S] :
    Module.rank S Ω[S⁄R] = n := by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  rw [P.rank_kaehlerDifferential]; rw [hP]

/--
lemma `IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth` / 引理 `IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`

English:
lemma IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
  statement: [Nontrivial S]
  proof: by
  refine ⟨fun h => IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _, fun h => ?_⟩
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  refine ⟨_, _, _, ‹_›, ⟨P, ?_⟩⟩
  apply Nat.cast_injective (R := Cardinal)
  rwa [← P.rank_kaehlerDifferential]

中文:
引理 是StandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
  结论: [非平凡 S]
  证明: by
  refine ⟨fun h => IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _, fun h => ?_⟩
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  refine ⟨_, _, _, ‹_›, ⟨P, ?_⟩⟩
  apply Nat.cast_injective (R := Cardinal)
  rwa [← P.rank_kaehlerDifferential]

Depends on / 依赖: Cardinal, IsStandardSmooth, IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential, Nat.cast_injective, P.rank_kaehlerDifferential, cast_injective, rank_kaehlerDifferential
-/
lemma IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth [Nontrivial S]
    [IsStandardSmooth R S] (n : Nat) :
    IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = n := by
  refine ⟨fun h => IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _, fun h => ?_⟩
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  refine ⟨_, _, _, ‹_›, ⟨P, ?_⟩⟩
  apply Nat.cast_injective (R := Cardinal)
  rwa [← P.rank_kaehlerDifferential]

/--
Instance `IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential` / 实例 `IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential`

English:
instance IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential
  body: by
  cases subsingleton_or_nontrivial S
  · exact Module.subsingleton S _
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  exact Module.subsingleton_of_rank_zero
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 0)

@[deprecated (since := "2026-05-22")]
alias IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential :=
  IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential

中文:
实例 是StandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential
  定义体: by
  cases subsingleton_or_nontrivial S
  · exact Module.subsingleton S _
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  exact Module.subsingleton_of_rank_zero
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 0)

@[deprecated (since := "2026-05-22")]
alias IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential :=
  IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential

Depends on / 依赖: IsStandardSmooth, IsStandardSmoothOfRelativeDimension, IsStandardSmoothOfRelativeDimension.isStandardSmooth, IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential, Module, Module.subsingleton, Module.subsingleton_of_rank_zero, isStandardSmooth, rank_kaehlerDifferential, subsingleton, subsingleton_of_rank_zero, subsingleton_or_nontrivial
-/
instance IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential
    [IsStandardSmoothOfRelativeDimension 0 R S] : Subsingleton Ω[S⁄R] := by
  cases subsingleton_or_nontrivial S
  · exact Module.subsingleton S _
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  exact Module.subsingleton_of_rank_zero
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 0)

@[deprecated (since := "2026-05-22")]
alias IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential :=
  IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential

end

instance (priority := 900) [IsStandardSmooth R S] : Smooth R S where
  formallySmooth := by
    rw [Algebra.formallySmooth_iff]
    exact ⟨inferInstance, inferInstance⟩

/-- If `S` is `R`-standard smooth of relative dimension zero, it is étale. -/
instance (priority := 900) [IsStandardSmoothOfRelativeDimension 0 R S] : Etale R S where
  finitePresentation := (IsStandardSmoothOfRelativeDimension.isStandardSmooth 0).finitePresentation
  formallyEtale :=
    have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
    have : FormallyUnramified R S := ⟨inferInstance⟩
    .of_formallyUnramified_and_formallySmooth

end Algebra
