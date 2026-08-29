/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Computation of Jacobian of presentations from basis of Cotangent

Let `P` be a presentation of an `R`-algebra `S` with kernel `I = (fᵢ)`.
In this file we provide lemmas to show that `P` is submersive when given suitable bases of
`I/I²` and `Ω[S⁄R]`.

We will later deduce from this a presentation-independent characterisation of standard
smooth algebras (TODO @chrisflav).

## Main results

- `PreSubmersivePresentation.isUnit_jacobian_of_cotangentRestrict_bijective`:
  If the `fᵢ` form a basis of `I/I²` and the restricted cotangent complex
  `I/I² → S ⊗[R] (Ω[R[Xᵢ]⁄R]) = ⊕ᵢ S → ⊕ⱼ S` is bijective, `P` is submersive.
-/

public section

universe t₂ t₁ u v

open KaehlerDifferential MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ κ : Type*}

namespace Algebra

namespace Generators

variable (P : Generators R S ι) {u : σ -> ι} (hu : Function.Injective u)
  {v : κ -> ι} (hv : Function.Injective v)

/--
lemma `cotangentRestrict_bijective_of_isCompl` / 引理 `cotangentRestrict_bijective_of_isCompl`

English:
lemma cotangentRestrict_bijective_of_isCompl
  proof: by
  rw [cotangentRestrict]; rw [Finsupp.lcomapDomain_eq_linearProjOfIsCompl _ huv.symm]
  set f : _ ->ₗ[S] (ι ->₀ S) := P.cotangentSpaceBasis.repr ∘ₗ P.toExtension.cotangentComplex
  let g : (ι ->₀ S) ->ₗ[S] (Ω[S⁄R]) := P.toExtension.toKaehler ∘ₗ P.cotangentSpaceBasis.repr.symm
  have hfg : Functio

中文:
引理 cotangentRestrict_bijective_of_isCompl
  证明: by
  rw [cotangentRestrict]; rw [Finsupp.lcomapDomain_eq_linearProjOfIsCompl _ huv.symm]
  set f : _ ->ₗ[S] (ι ->₀ S) := P.cotangentSpaceBasis.repr ∘ₗ P.toExtension.cotangentComplex
  let g : (ι ->₀ S) ->ₗ[S] (Ω[S⁄R]) := P.toExtension.toKaehler ∘ₗ P.cotangentSpaceBasis.repr.symm
  have hfg : Functio

Depends on / 依赖: Extension, Extension.exact_cotangentComplex_toKaehler, Finsupp, Finsupp.lcomapDomain_eq_linearProjOfIsCompl, Function, Function.Exact, LinearEquiv, LinearEquiv.conj_exact_iff_exact, LinearMap, LinearMap.linearProjOfIsCompl_comp_bijective_of_exact, P.cotangentSpaceBa, P.cotangentSpaceBasis.repr, P.cotangentSpaceBasis.repr.symm, P.toExtension.cotangentComplex, P.toExtension.toKaehler, conj_exact_iff_exact, cotangentComplex, cotangentRestrict, cotangentSpaceBa, cotangentSpaceBasis
-/
lemma cotangentRestrict_bijective_of_isCompl
    (huv : IsCompl (Set.range v) (Set.range u))
    (hm : Submodule.span S (.range fun i => D R S (P.val (v i))) = ⊤)
    (hk : Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S (.range fun x => P.cotangentSpaceBasis (v x))))
    [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  rw [cotangentRestrict]; rw [Finsupp.lcomapDomain_eq_linearProjOfIsCompl _ huv.symm]
  set f : _ ->ₗ[S] (ι ->₀ S) := P.cotangentSpaceBasis.repr ∘ₗ P.toExtension.cotangentComplex
  let g : (ι ->₀ S) ->ₗ[S] (Ω[S⁄R]) := P.toExtension.toKaehler ∘ₗ P.cotangentSpaceBasis.repr.symm
  have hfg : Function.Exact f g := by
    simp only [f, g, LinearEquiv.conj_exact_iff_exact]
    exact Extension.exact_cotangentComplex_toKaehler
  apply LinearMap.linearProjOfIsCompl_comp_bijective_of_exact hfg
· exact P.cotangentSpaceBasis.repr.injective.comp
      (Extension.subsingleton_h1Cotangent P.toExtension).mp P.equivH1Cotangent.subsingleton
  · simp only [disjoint_iff, g]
    apply Submodule.map_injective_of_injective (f := P.cotangentSpaceBasis.repr.symm.toLinearMap)
      P.cotangentSpaceBasis.repr.symm.injective
    rw [Submodule.map_inf P.cotangentSpaceBasis.repr.symm.toLinearMap
        P.cotangentSpaceBasis.repr.symm.injective]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [Function.comp_def]; rw [LinearMap.ker_comp]; rw [Submodule.map_comap_eq_of_surjective]
    · simpa [← disjoint_iff]
    · exact P.cotangentSpaceBasis.repr.symm.surjective
  · simpa [g, Submodule.map_comp, Submodule.map_span, ← Set.range_comp, Function.comp_def]

/--
lemma `disjoint_ker_toKaehler_of_linearIndependent` / 引理 `disjoint_ker_toKaehler_of_linearIndependent`

English:
lemma disjoint_ker_toKaehler_of_linearIndependent
  proof: by
  rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  intro x ⟨hx, hxs⟩
  rw [SetLike.mem_coe]; rw [Finsupp.mem_span_range_iff_exists_finsupp] at hxs
  obtain ⟨c, rfl⟩ := hxs
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_finsuppSum, map_smul,
    toKaehler_cotangentSpaceBasis] at hx
  obtain rf

中文:
引理 disjoint_ker_toKaehler_of_linearIndependent
  证明: by
  rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  intro x ⟨hx, hxs⟩
  rw [SetLike.mem_coe]; rw [Finsupp.mem_span_range_iff_exists_finsupp] at hxs
  obtain ⟨c, rfl⟩ := hxs
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_finsuppSum, map_smul,
    toKaehler_cotangentSpaceBasis] at hx
  obtain rf

Depends on / 依赖: Finsupp, Finsupp.mem_span_range_iff_exists_finsupp, LinearMap, LinearMap.mem_ker, SetLike, SetLike.mem_coe, Submodule, Submodule.eq_bot_iff, disjoint_iff, eq_bot_iff, linearIndependent_iff, linearIndependent_iff.mp, map_finsuppSum, map_smul, mem_coe, mem_ker, mem_span_range_iff_exists_finsupp, toKaehler_cotangentSpaceBasis
-/
lemma disjoint_ker_toKaehler_of_linearIndependent
    (h : LinearIndependent S (fun k => D R S (P.val (v k)))) :
    Disjoint (LinearMap.ker P.toExtension.toKaehler)
        (.span S <| .range fun x => P.cotangentSpaceBasis (v x)) := by
  rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
  intro x ⟨hx, hxs⟩
  rw [SetLike.mem_coe]; rw [Finsupp.mem_span_range_iff_exists_finsupp] at hxs
  obtain ⟨c, rfl⟩ := hxs
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_finsuppSum, map_smul,
    toKaehler_cotangentSpaceBasis] at hx
  obtain rfl := (linearIndependent_iff.mp h) c hx
  simp

/--
lemma `cotangentRestrict_bijective_of_basis_kaehlerDifferential` / 引理 `cotangentRestrict_bijective_of_basis_kaehlerDifferential`

English:
lemma cotangentRestrict_bijective_of_basis_kaehlerDifferential
  proof: by
  refine P.cotangentRestrict_bijective_of_isCompl _ huv ?_ ?_
  · simp_rw [← hb]
    exact b.span_eq
  · apply disjoint_ker_toKaehler_of_linearIndependent
    simp_rw [← hb]
    exact b.linearIndependent

中文:
引理 cotangentRestrict_bijective_of_basis_kaehlerDifferential
  证明: by
  refine P.cotangentRestrict_bijective_of_isCompl _ huv ?_ ?_
  · simp_rw [← hb]
    exact b.span_eq
  · apply disjoint_ker_toKaehler_of_linearIndependent
    simp_rw [← hb]
    exact b.linearIndependent

Depends on / 依赖: P.cotangentRestrict_bijective_of_isCompl, b.linearIndependent, b.span_eq, cotangentRestrict_bijective_of_isCompl, disjoint_ker_toKaehler_of_linearIndependent, linearIndependent, simp_rw, span_eq
-/
lemma cotangentRestrict_bijective_of_basis_kaehlerDifferential
    (huv : IsCompl (Set.range v) (Set.range u)) (b : Module.Basis κ S (Ω[S⁄R]))
    (hb : forall k, b k = (D R S) (P.val (v k))) [Subsingleton (H1Cotangent R S)] :
    Function.Bijective (cotangentRestrict P hu) := by
  refine P.cotangentRestrict_bijective_of_isCompl _ huv ?_ ?_
  · simp_rw [← hb]
    exact b.span_eq
  · apply disjoint_ker_toKaehler_of_linearIndependent
    simp_rw [← hb]
    exact b.linearIndependent

end Generators

namespace PreSubmersivePresentation

open Generators

variable (P : PreSubmersivePresentation R S ι σ) [Finite σ]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isUnit_jacobian_of_cotangentRestrict_bijective` / 引理 `isUnit_jacobian_of_cotangentRestrict_bijective`

English:
lemma isUnit_jacobian_of_cotangentRestrict_bijective
  proof: by
  have heq : (fun j i => (aeval P.val) (pderiv (P.map i) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘ P.cotangentRestrict P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply, cotangentRestrict_mk]
  apply P.isUnit_jacobi

中文:
引理 isUnit_jacobian_of_cotangentRestrict_bijective
  证明: by
  have heq : (fun j i => (aeval P.val) (pderiv (P.map i) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘ P.cotangentRestrict P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply, cotangentRestrict_mk]
  apply P.isUnit_jacobi

Depends on / 依赖: Finsupp, Finsupp.linearEquivFunOnFinite, Finsupp.linearEquivFunOnFinite_apply, Function, Function.comp_apply, LinearMap, LinearMap.ker_eq_bot_of_injective, P.cotangentRestrict, P.isUnit_jacobian_of_linearIndependent_of_span_eq_top, P.map, P.map_inj, P.relation, P.val, Set.rang, Set.range_comp, b.linearIndependent.map, comp_apply, cotangentRestrict, cotangentRestrict_mk, h.injective
-/
lemma isUnit_jacobian_of_cotangentRestrict_bijective
    (b : Module.Basis σ S P.toExtension.Cotangent)
    (hb : forall r, b r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩)
    (h : Function.Bijective (P.cotangentRestrict P.map_inj)) :
    IsUnit P.jacobian := by
  have heq : (fun j i => (aeval P.val) (pderiv (P.map i) (P.relation j))) =
      Finsupp.linearEquivFunOnFinite S S _ ∘ P.cotangentRestrict P.map_inj ∘ ⇑b := by
    ext i j
    simp only [Function.comp_apply, hb, Finsupp.linearEquivFunOnFinite_apply, cotangentRestrict_mk]
  apply P.isUnit_jacobian_of_linearIndependent_of_span_eq_top
  · rw [heq]
    exact (b.linearIndependent.map' _ (LinearMap.ker_eq_bot_of_injective h.injective)).map' _
      (Finsupp.linearEquivFunOnFinite S S σ).ker
  · rw [heq, Set.range_comp, Set.range_comp, Submodule.span_image_linearEquiv, ← Submodule.map_span,
      b.span_eq, Submodule.map_top, LinearMap.range_eq_top_of_surjective _ h.surjective,
      Submodule.map_top, LinearEquiv.range]

end PreSubmersivePresentation

end Algebra
