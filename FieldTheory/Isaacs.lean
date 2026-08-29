/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.GroupTheory.CosetCover

/-!
# Algebraic extensions are determined by their sets of minimal polynomials up to isomorphism

## Main results

`Field.nonempty_algHom_of_exists_root` says if `E/F` and `K/F` are field extensions
with `E/F` algebraic, and if the minimal polynomial of every element of `E` over `F` has a root
in `K`, then there exists an `F`-embedding of `E` into `K`. If `E/F` and `K/F` have the same
set of minimal polynomials, then `E` and `K` are isomorphic as `F`-algebras. As a corollary:

`IsAlgClosure.of_exists_root`: if `E/F` is algebraic and every monic irreducible polynomial
in `F[X]` has a root in `E`, then `E` is an algebraic closure of `F`.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

public section

namespace Field

open Polynomial IntermediateField

variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
variable [alg : Algebra.IsAlgebraic F E]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `nonempty_algHom_of_exists_root` / 定理 `nonempty_algHom_of_exists_root`

English:
theorem nonempty_algHom_of_exists_root
  given: (h : forall x : E, exists y : K, aeval y (minpoly F x) = 0)
  proof: by
  refine Lifts.nonempty_algHom_of_exist_lifts_finset fun S => ⟨⟨adjoin F S, ?_⟩, subset_adjoin _ _⟩
  let p := (S.prod <| fun x => (minpoly F x).map (algebraMap F K))
  let K' := SplittingField p
  have splits s (hs : s in S) : ((minpoly F s).map (algebraMap F K')).Splits := by
    apply (Splitti

中文:
定理 nonempty_algHom_of_存在_root
  条件: (h : 对任意 x : E, 存在 y : K, aeval y (minpoly F x) = 0)
  证明: by
  refine Lifts.nonempty_algHom_of_exist_lifts_finset fun S => ⟨⟨adjoin F S, ?_⟩, subset_adjoin _ _⟩
  let p := (S.prod <| fun x => (minpoly F x).map (algebraMap F K))
  let K' := SplittingField p
  have splits s (hs : s in S) : ((minpoly F s).map (algebraMap F K')).Splits := by
    apply (Splitti

Depends on / 依赖: Equiv.injective, Finset, Finset.prod_ne_zero_iff.mpr, IsScalarTower, IsScalarTower.algebraMap_eq, Lifts.nonempty_algHom_of_exist_lifts_finset, Polynomial, Polynomial.map_map, Polynomial.map_ne_zero, S.prod, Splits, SplittingField, SplittingField.splits, WithZero, WithZero.unitsWithZeroEquiv, adjoin, alg.isIntegral, algebraMap, algebraMap_eq, injective
-/
theorem nonempty_algHom_of_exists_root (h : forall x : E, exists y : K, aeval y (minpoly F x) = 0) :
    Nonempty (E ->ₐ[F] K) := by
  refine Lifts.nonempty_algHom_of_exist_lifts_finset fun S => ⟨⟨adjoin F S, ?_⟩, subset_adjoin _ _⟩
  let p := (S.prod <| fun x => (minpoly F x).map (algebraMap F K))
  let K' := SplittingField p
  have splits s (hs : s in S) : ((minpoly F s).map (algebraMap F K')).Splits := by
    apply (SplittingField.splits p).of_dvd (map_ne_zero (Finset.prod_ne_zero_iff.mpr
      fun _ _ => Polynomial.map_ne_zero (minpoly.ne_zero <| alg.isIntegral.1 _))) ?_
    rw [IsScalarTower.algebraMap_eq F K K']; rw [← Polynomial.map_map]; rw [map_dvd_map']
    exact Finset.dvd_prod_of_mem _ hs
  let K₀ := (⊥ : IntermediateField K K').restrictScalars F
  let FS := adjoin F (S : Set E)
  let Ω := FS ->ₐ[F] K'
  have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ => (alg.isIntegral).1 _
  let M (ω : Ω) := Subalgebra.toSubmodule (K₀.comap ω).toSubalgebra
  have : ⋃ ω : Ω, (M ω : Set FS) = Set.univ :=
Set.eq_univ_of_forall fun ⟨α, hα⟩ => Set.mem_iUnion.mpr by
      have ⟨β, hβ⟩ := h α
      let ϕ : F⟮α⟯ ->ₐ[F] K' := (IsScalarTower.toAlgHom _ _ _).comp
        ((AdjoinRoot.liftAlgHom _ _ _ hβ).comp
        (adjoinRootEquivAdjoin F <| (alg.isIntegral).1 _).symm.toAlgHom)
      have ⟨ω, hω⟩ := exists_algHom_adjoin_of_splits
        (fun s hs => ⟨(alg.isIntegral).1 _, splits s hs⟩) ϕ (adjoin_simple_le_iff.mpr hα)
      refine ⟨ω, β, ((DFunLike.congr_fun hω <| AdjoinSimple.gen F α).trans ?_).symm⟩
      rw [AlgHom.comp_apply]; rw [AlgHom.comp_apply]; rw [AlgEquiv.coe_toAlgHom]; rw [adjoinRootEquivAdjoin_symm_apply_gen]; rw [AdjoinRoot.liftAlgHom_root]
      rfl
  have ω : exists ω : Ω, ⊤ <= M ω := by
    cases finite_or_infinite F
    · have ⟨α, hα⟩ := exists_primitive_element_of_finite_bot F FS
      have ⟨ω, hω⟩ := Set.mem_iUnion.mp (this ▸ Set.mem_univ α)
      exact ⟨ω, show ⊤ <= K₀.comap ω by rwa [← hα, adjoin_simple_le_iff]⟩
    · simp_rw [top_le_iff, Subspace.exists_eq_top_of_iUnion_eq_univ this]
  exact ((botEquiv K K').toAlgHom.restrictScalars F).comp
    (ω.choose.codRestrict K₀.toSubalgebra fun x => ω.choose_spec trivial)

@[deprecated (since := "2026-01-31")]
alias nonempty_algHom_of_exist_roots := nonempty_algHom_of_exists_root

/--
theorem `nonempty_algHom_of_minpoly_eq` / 定理 `nonempty_algHom_of_minpoly_eq`

English:
theorem nonempty_algHom_of_minpoly_eq
  proof: nonempty_algHom_of_exists_root fun x => have ⟨y, hy⟩ := h x; ⟨y, by rw [hy, minpoly.aeval]⟩

中文:
定理 nonempty_algHom_of_minpoly_eq
  证明: nonempty_algHom_of_exists_root fun x => have ⟨y, hy⟩ := h x; ⟨y, by rw [hy, minpoly.aeval]⟩

Depends on / 依赖: minpoly, minpoly.aeval, nonempty_algHom_of_exists_root
-/
theorem nonempty_algHom_of_minpoly_eq
    (h : forall x : E, exists y : K, minpoly F x = minpoly F y) :
    Nonempty (E ->ₐ[F] K) :=
  nonempty_algHom_of_exists_root fun x => have ⟨y, hy⟩ := h x; ⟨y, by rw [hy, minpoly.aeval]⟩

/--
theorem `nonempty_algHom_of_range_minpoly_subset` / 定理 `nonempty_algHom_of_range_minpoly_subset`

English:
theorem nonempty_algHom_of_range_minpoly_subset
  proof: nonempty_algHom_of_minpoly_eq fun x => have ⟨y, hy⟩ := h ⟨x, rfl⟩; ⟨y, hy.symm⟩

中文:
定理 nonempty_algHom_of_range_minpoly_subset
  证明: nonempty_algHom_of_minpoly_eq fun x => have ⟨y, hy⟩ := h ⟨x, rfl⟩; ⟨y, hy.symm⟩

Depends on / 依赖: hy.symm, nonempty_algHom_of_minpoly_eq
-/
theorem nonempty_algHom_of_range_minpoly_subset
    (h : Set.range (@minpoly F E _ _ _) subseteq Set.range (@minpoly F K _ _ _)) :
    Nonempty (E ->ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x => have ⟨y, hy⟩ := h ⟨x, rfl⟩; ⟨y, hy.symm⟩

/--
theorem `nonempty_algEquiv_of_range_minpoly_eq` / 定理 `nonempty_algEquiv_of_range_minpoly_eq`

English:
theorem nonempty_algEquiv_of_range_minpoly_eq
  proof: have ⟨σ⟩ := nonempty_algHom_of_range_minpoly_subset h.le
have : Algebra.IsAlgebraic F K := ⟨fun y => IsIntegral.isAlgebraic by
    by_contra hy
    have ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    rw [minpoly.eq_zero hy] at hx
    exact minpoly.ne_zero ((alg.isIntegral).1 x) hx⟩
  have ⟨τ⟩ := nonempty_algHom_of_ra

中文:
定理 nonempty_algEquiv_of_range_minpoly_eq
  证明: have ⟨σ⟩ := nonempty_algHom_of_range_minpoly_subset h.le
have : Algebra.IsAlgebraic F K := ⟨fun y => IsIntegral.isAlgebraic by
    by_contra hy
    have ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    rw [minpoly.eq_zero hy] at hx
    exact minpoly.ne_zero ((alg.isIntegral).1 x) hx⟩
  have ⟨τ⟩ := nonempty_algHom_of_ra

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Algebra.IsAlgebraic.algHom_bijective, IsAlgebraic, IsIntegral, IsIntegral.isAlgebraic, alg.isIntegral, eq_zero, h.ge, h.le, isAlgebraic, isIntegral, minpoly, minpoly.eq_zero, minpoly.ne_zero, ne_zero, nonempty_algHom_of_range_minpoly_subset, ofBijective
-/
theorem nonempty_algEquiv_of_range_minpoly_eq
    (h : Set.range (@minpoly F E _ _ _) = Set.range (@minpoly F K _ _ _)) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_range_minpoly_subset h.le
have : Algebra.IsAlgebraic F K := ⟨fun y => IsIntegral.isAlgebraic by
    by_contra hy
    have ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    rw [minpoly.eq_zero hy] at hx
    exact minpoly.ne_zero ((alg.isIntegral).1 x) hx⟩
  have ⟨τ⟩ := nonempty_algHom_of_range_minpoly_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

/--
theorem `nonempty_algHom_of_aeval_eq_zero_subset` / 定理 `nonempty_algHom_of_aeval_eq_zero_subset`

English:
theorem nonempty_algHom_of_aeval_eq_zero_subset
  proof: nonempty_algHom_of_minpoly_eq fun x =>
    have ⟨y, hy⟩ := h ⟨_, minpoly.aeval F x⟩
    ⟨y, (minpoly.eq_iff_aeval_minpoly_eq_zero <| (alg.isIntegral).1 x).mpr hy⟩

中文:
定理 nonempty_algHom_of_aeval_eq_zero_subset
  证明: nonempty_algHom_of_minpoly_eq fun x =>
    have ⟨y, hy⟩ := h ⟨_, minpoly.aeval F x⟩
    ⟨y, (minpoly.eq_iff_aeval_minpoly_eq_zero <| (alg.isIntegral).1 x).mpr hy⟩

Depends on / 依赖: alg.isIntegral, eq_iff_aeval_minpoly_eq_zero, isIntegral, minpoly, minpoly.aeval, minpoly.eq_iff_aeval_minpoly_eq_zero, nonempty_algHom_of_minpoly_eq
-/
theorem nonempty_algHom_of_aeval_eq_zero_subset
    (h : {p : F[X] | exists x : E, aeval x p = 0} subseteq {p | exists y : K, aeval y p = 0}) :
    Nonempty (E ->ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x =>
    have ⟨y, hy⟩ := h ⟨_, minpoly.aeval F x⟩
    ⟨y, (minpoly.eq_iff_aeval_minpoly_eq_zero <| (alg.isIntegral).1 x).mpr hy⟩

/--
theorem `nonempty_algEquiv_of_aeval_eq_zero_eq` / 定理 `nonempty_algEquiv_of_aeval_eq_zero_eq`

English:
theorem nonempty_algEquiv_of_aeval_eq_zero_eq
  statement: [Algebra.IsAlgebraic F K]
  proof: have ⟨σ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.le
  have ⟨τ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

中文:
定理 nonempty_algEquiv_of_aeval_eq_zero_eq
  结论: [代数.是代数 F K]
  证明: have ⟨σ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.le
  have ⟨τ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.algHom_bijective, IsAlgebraic, h.ge, h.le, nonempty_algHom_of_aeval_eq_zero_subset, ofBijective
-/
theorem nonempty_algEquiv_of_aeval_eq_zero_eq [Algebra.IsAlgebraic F K]
    (h : {p : F[X] | exists x : E, aeval x p = 0} = {p | exists y : K, aeval y p = 0}) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.le
  have ⟨τ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩

/--
theorem `_root_.IsAlgClosure.of_exists_root` / 定理 `_root_.IsAlgClosure.of_exists_root`

English:
theorem _root_.IsAlgClosure.of_exists_root
  proof: .of_splits fun p _ _ =>
    have ⟨σ⟩ := nonempty_algHom_of_exists_root fun x : p.SplittingField =>
      have := Algebra.IsAlgebraic.isIntegral (K := F).1 x
      h _ (minpoly.monic this) (minpoly.irreducible this)
    Splits.of_algHom (SplittingField.splits _) σ

@[deprecated (since := "2026-01-31"

中文:
定理 _root_.是AlgClosure.of_存在_root
  证明: .of_splits fun p _ _ =>
    have ⟨σ⟩ := nonempty_algHom_of_exists_root fun x : p.SplittingField =>
      have := Algebra.IsAlgebraic.isIntegral (K := F).1 x
      h _ (minpoly.monic this) (minpoly.irreducible this)
    Splits.of_algHom (SplittingField.splits _) σ

@[deprecated (since := "2026-01-31"

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isIntegral, IsAlgebraic, Splits, Splits.of_algHom, SplittingField, SplittingField.splits, irreducible, isIntegral, minpoly, minpoly.irreducible, minpoly.monic, nonempty_algHom_of_exists_root, of_algHom, of_splits, p.SplittingField, splits
-/
theorem _root_.IsAlgClosure.of_exists_root
    (h : forall p : F[X], p.Monic -> Irreducible p -> exists x : E, aeval x p = 0) :
    IsAlgClosure F E :=
  .of_splits fun p _ _ =>
    have ⟨σ⟩ := nonempty_algHom_of_exists_root fun x : p.SplittingField =>
      have := Algebra.IsAlgebraic.isIntegral (K := F).1 x
      h _ (minpoly.monic this) (minpoly.irreducible this)
    Splits.of_algHom (SplittingField.splits _) σ

@[deprecated (since := "2026-01-31")]
alias _root_.IsAlgClosure.of_exist_roots := IsAlgClosure.of_exists_root

end Field
