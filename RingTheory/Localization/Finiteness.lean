/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!

# Finiteness properties under localization

In this file we establish behaviour of `Module.Finite` under localizations.

## Main results

- `Module.Finite.of_isLocalizedModule`: If `M` is a finite `R`-module,
  `S` is a submonoid of `R`, `Rₚ` is the localization of `R` at `S`
  and `Mₚ` is the localization of `M` at `S`, then `Mₚ` is a finite
  `Rₚ`-module.
- `Module.Finite.of_localizationSpan_finite`: If `M` is an `R`-module
  and `{ r }` is a finite set generating the unit ideal such that
  `Mᵣ` is a finite `Rᵣ`-module for each `r`, then `M` is a finite `R`-module.

## TODO

* Move the results that `Module.Finite` over a semilocal ring is a local property from
  `Mathlib/RingTheory/LocalProperties/Semilocal.lean` to this file.

-/

@[expose] public section

universe u v w t

section

open scoped Pointwise

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (M : Submonoid R) (f : R ->+* S)
variable (R' S' : Type*) [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S']

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
theorem `IsLocalization.smul_mem_finsetIntegerMultiple_span` / 定理 `IsLocalization.smul_mem_finsetIntegerMultiple_span`

English:
theorem IsLocalization.smul_mem_finsetIntegerMultiple_span
  statement: [Algebra R S] [Algebra R S']
  proof: by
  let g : S ->ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  have g_apply : forall x, g x = algebraMap S S' x := fun _ => rfl
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalizatio

中文:
定理 IsLocalization.smul_mem_finsetIntegerMultiple_span
  结论: [Algebra R S] [Algebra R S']
  证明: by
  let g : S ->ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  have g_apply : forall x, g x = algebraMap S S' x := fun _ => rfl
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalizatio

Depends on / 依赖: AlgHom, AlgHom.mk, Algebra, Algebra.algebraMap_eq_smul_one, algebraMap, algebraMap_eq_smul_one, g_apply
-/
theorem IsLocalization.smul_mem_finsetIntegerMultiple_span [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x in Submodule.span R (s : Set S')) :
    exists m : M, m • x in
      Submodule.span R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  let g : S ->ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  have g_apply : forall x, g x = algebraMap S S' x := fun _ => rfl
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalization.commonDenomOfFinset (M.map (algebraMap R S)) s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨y', hy', e : algebraMap R S y' = y⟩ := y.prop
  have : algebraMap R S y' • (s : Set S') = y' • (s : Set S') := by
    simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  rw [← e]; rw [this] at hx₁
  replace hx₁ := congr_arg (Submodule.span R) hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ in y' • Submodule.span R (s : Set S') := Set.smul_mem_smul_set hx
  rw [hx₁]; rw [← g_apply]; rw [← map_smul g]; rw [g_apply]; rw [← Algebra.linearMap_apply]; rw [← AlgHom.coe_toLinearMap]; rw [← Submodule.map_span] at hx
  -- Since `x` falls in the span of `s` in `S'`, `y' • x : S` falls in the span of `s'` in `S'`.
  -- That is, there exists some `x' : S` in the span of `s'` in `S` and `x' = y' • x` in `S'`.
  -- Thus `a • (y' • x) = a • x' ∈ span s'` in `S` for some `a ∈ M`.
  obtain ⟨x', hx', hx'' : algebraMap _ _ _ = _⟩ := hx
  obtain ⟨⟨_, a, ha₁, rfl⟩, ha₂⟩ :=
    (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hx''
  use (⟨a, ha₁⟩ : M) * (⟨y', hy'⟩ : M)
  convert!
    (Submodule.span R
          (IsLocalization.finsetIntegerMultiple (Submonoid.map (algebraMap R S) M) s :
            Set S)).smul_mem
      a hx' using 1
  convert! ha₂.symm using 1
  · rw [Subtype.coe_mk, Submonoid.smul_def, Submonoid.coe_mul, ← smul_smul]
    exact Algebra.smul_def _ _
  · exact Algebra.smul_def _ _

/--
theorem `multiple_mem_span_of_mem_localization_span` / 定理 `multiple_mem_span_of_mem_localization_span`

English:
theorem multiple_mem_span_of_mem_localization_span
  proof: by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : exists t : M, t • x in Submodule.span R (s' : Set N)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x with
  | empty => use 1;

中文:
定理 multiple_mem_span_of_mem_localization_span
  证明: by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : exists t : M, t • x in Submodule.span R (s' : Set N)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x with
  | empty => use 1;

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction_on, IsLocalization, IsLocalization.surj, Submodule, Submodule.mem_span_finite_of_mem_span, Submodule.mem_span_insert, Submodule.span, Submodule.span_mono, classical, coe_insert, generalizing, induction_on, insert, mem_span_finite_of_mem_span, mem_span_insert, rsuffices, span_mono
-/
theorem multiple_mem_span_of_mem_localization_span
    {N : Type*} [AddCommMonoid N] [Module R N] [Module R' N]
    [IsScalarTower R R' N] [IsLocalization M R'] (s : Set N) (x : N)
    (hx : x in Submodule.span R' s) : exists (t : M), t • x in Submodule.span R s := by
  classical
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : exists t : M, t • x in Submodule.span R (s' : Set N)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x with
  | empty => use 1; simpa using hs'
  | insert a s _ hs =>
  simp only [Finset.coe_insert,
    Submodule.mem_span_insert] at hs' ⊢
  rcases hs' with ⟨y, z, hz, rfl⟩
  rcases IsLocalization.surj M y with ⟨⟨y', s'⟩, e⟩
  apply congrArg (fun x => x • a) at e
  simp only [algebraMap_smul] at e
  rcases hs _ hz with ⟨t, ht⟩
  refine ⟨t * s', t * y', _, (Submodule.span R (s : Set N)).smul_mem s' ht, ?_⟩
  rw [smul_add]; rw [← smul_smul]; rw [mul_comm]; rw [← smul_smul]; rw [← smul_smul]; rw [← e]; rw [mul_comm]; rw [← Algebra.smul_def]
  simp [Submonoid.smul_def]

/--
theorem `multiple_mem_adjoin_of_mem_localization_adjoin` / 定理 `multiple_mem_adjoin_of_mem_localization_adjoin`

English:
theorem multiple_mem_adjoin_of_mem_localization_adjoin
  statement: [Algebra R' S] [Algebra R S]
  proof: by
  change exists t : M, t • x in Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x in Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx

中文:
定理 multiple_mem_adjoin_of_mem_localization_adjoin
  结论: [Algebra R' S] [Algebra R S]
  证明: by
  change exists t : M, t • x in Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x in Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_eq_span, Subalgebra, Subalgebra.toSubmodule, adjoin, adjoin_eq_span, multiple_mem_span_of_mem_localization_span, simp_rw, toSubmodule
-/
theorem multiple_mem_adjoin_of_mem_localization_adjoin [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S)
    (hx : x in Algebra.adjoin R' s) : exists t : M, t • x in Algebra.adjoin R s := by
  change exists t : M, t • x in Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x in Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx

end

namespace Module.Finite

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {Rₚ : Type v} [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization S Rₚ]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {Mₚ : Type t} [AddCommMonoid Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
variable (f : M ->ₗ[R] Mₚ) [IsLocalizedModule S f]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_isLocalization` / 引理 `of_isLocalization`

English:
lemma of_isLocalization
  statement: (R S) {Rₚ Sₚ : Type*} [CommSemiring R] [CommSemiring S]
  proof: by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is g

中文:
引理 of_isLocalization
  结论: (R S) {Rₚ Sₚ : 类型} [CommSemiring R] [CommSemiring S]
  证明: by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is g

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, IsLocalization, IsLocalization.map, IsLocalization.map_comp, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.algebraMap_eq, Submonoid, Submonoid.le_comap_map, algebraMap, algebraMapSubmonoid, algebraMap_eq, classical, le_comap_map, map_comp, ringHom_ext
-/
lemma of_isLocalization (R S) {Rₚ Sₚ : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring Rₚ] [CommSemiring Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [hRS : Module.Finite R S] :
    Module.Finite Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  obtain ⟨T, hT⟩ := hRS
  use T.image (algebraMap S Sₚ)
  simpa using span_eq_top_localization_localization Rₚ M Sₚ hT

instance {R S : Type*} [CommSemiring R] {P : Ideal R} [CommSemiring S] [Algebra R S]
    [Module.Finite R S] [P.IsPrime] :
    Module.Finite (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
  .of_isLocalization R S P.primeCompl

open Algebra nonZeroDivisors in
instance {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [Module.Finite A C] :
    Module.Finite (FractionRing A) (Localization (algebraMapSubmonoid C A⁰)) :=
  .of_isLocalization A C A⁰

include S f in
/--
lemma `of_isLocalizedModule` / 引理 `of_isLocalizedModule`

English:
lemma of_isLocalizedModule
  given: [Module.Finite R M]
  statement: Module.Finite Rₚ Mₚ
  proof: by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  simpa using span_eq_top_of_isLocalizedModule Rₚ S f hT

中文:
引理 of_isLocalizedModule
  条件: [Module.Finite R M]
  结论: Module.Finite Rₚ Mₚ
  证明: by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  simpa using span_eq_top_of_isLocalizedModule Rₚ S f hT

Depends on / 依赖: Finite, Module, Module.Finite, T.image, classical, span_eq_top_of_isLocalizedModule
-/
lemma of_isLocalizedModule [Module.Finite R M] : Module.Finite Rₚ Mₚ := by
  classical
  obtain ⟨T, hT⟩ := ‹Module.Finite R M›
  use T.image f
  simpa using span_eq_top_of_isLocalizedModule Rₚ S f hT

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R M] : Module.Finite (Localization S) (LocalizedModule S M)
  body: of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

中文:
实例 [Module.Finite
  签名: R M] : Module.Finite (Localization S) (LocalizedModule S M)
  定义体: of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, mkLinearMap, of_isLocalizedModule
-/
instance [Module.Finite R M] : Module.Finite (Localization S) (LocalizedModule S M) :=
  of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

end

variable {R : Type u} [CommSemiring R] {M : Type w} [AddCommMonoid M] [Module R M]

/--
theorem `of_localizationSpan_finite'` / 定理 `of_localizationSpan_finite'`

English:
theorem of_localizationSpan_finite'
  statement: (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
  proof: by
  classical
  constructor
  choose s₁ s₂ using (fun g => (H g).1)
  let sf := fun x : t =>
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion]; rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_

中文:
定理 of_localizationSpan_finite'
  结论: (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
  证明: by
  classical
  constructor
  choose s₁ s₂ using (fun g => (H g).1)
  let sf := fun x : t =>
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion]; rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_

Depends on / 依赖: IsLocalizedModu, IsLocalizedModule, IsLocalizedModule.finsetIntegerMultiple, Submodule, Submodule.mem_of_span_eq_top_of_smul_pow_mem, Submodule.span_attach_biUnion, Submonoid, Submonoid.powers, attach, biUnion, classical, eq_top_iff, finsetIntegerMultiple, mem_of_span_eq_top_of_smul_pow_mem, multiple_mem_span_of_mem_localization_span, powers, r.val, span_attach_biUnion, t.attach.biUnion, x.val
-/
theorem of_localizationSpan_finite' (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid (Mₚ g)] [forall (g : t), Module R (Mₚ g)]
    {Rₚ : forall (_ : t), Type*} [forall (g : t), CommSemiring (Rₚ g)] [forall (g : t), Algebra R (Rₚ g)]
    [forall (g : t), IsLocalization.Away g.val (Rₚ g)]
    [forall (g : t), Module (Rₚ g) (Mₚ g)] [forall (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : forall (g : t), M ->ₗ[R] Mₚ g) [forall (g : t), IsLocalizedModule.Away g.val (f g)]
    (H : forall (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  classical
  constructor
  choose s₁ s₂ using (fun g => (H g).1)
  let sf := fun x : t =>
    IsLocalizedModule.finsetIntegerMultiple (Submonoid.powers x.val) (f x) (s₁ x)
  use t.attach.biUnion sf
  rw [Submodule.span_attach_biUnion]; rw [eq_top_iff]
  rintro x -
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (t : Set R) ht _ (fun r => ?_)
  set S : Submonoid R := Submonoid.powers r.val
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ := multiple_mem_span_of_mem_localization_span S (Rₚ r)
    (s₁ r : Set (Mₚ r)) (IsLocalizedModule.mk' (f r) x (1 : S)) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def]; rw [← IsLocalizedModule.mk'_smul]; rw [IsLocalizedModule.mk'_one] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalizedModule.smul_mem_finsetIntegerMultiple_span
    S (f r) _ (s₁ r) hn₁
  rw [Submonoid.smul_def] at hn₂
  use n₂ + n₁
  apply le_iSup (fun x : t => Submodule.span R (sf x : Set M)) r
  rw [pow_add]; rw [mul_smul]
  exact hn₂

/--
theorem `of_localizationSpan'` / 定理 `of_localizationSpan'`

English:
theorem of_localizationSpan'
  statement: (t : Set R) (ht : Ideal.span t = ⊤)
  proof: by
  rw [Ideal.span_eq_top_iff_finite] at ht
  obtain ⟨t', hc, ht'⟩ := ht
  have (g : t') : IsLocalization.Away g.val (Rₚ ⟨g.val, hc g.property⟩) :=
    h₁ ⟨g.val, hc g.property⟩
  have (g : t') : IsLocalizedModule.Away g.val
    ((fun g => f ⟨g.val, hc g.property⟩) g) := h₂ ⟨g.val, hc g.property⟩
 

中文:
定理 of_localizationSpan'
  结论: (t : Set R) (ht : Ideal.span t = ⊤)
  证明: by
  rw [Ideal.span_eq_top_iff_finite] at ht
  obtain ⟨t', hc, ht'⟩ := ht
  have (g : t') : IsLocalization.Away g.val (Rₚ ⟨g.val, hc g.property⟩) :=
    h₁ ⟨g.val, hc g.property⟩
  have (g : t') : IsLocalizedModule.Away g.val
    ((fun g => f ⟨g.val, hc g.property⟩) g) := h₂ ⟨g.val, hc g.property⟩
 

Depends on / 依赖: Ideal.span_eq_top_iff_finite, IsLocalization, IsLocalization.Away, IsLocalizedModule, IsLocalizedModule.Away, g.property, g.val, of_localizationSpan_finite, property, span_eq_top_iff_finite
-/
theorem of_localizationSpan' (t : Set R) (ht : Ideal.span t = ⊤)
    {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid (Mₚ g)] [forall (g : t), Module R (Mₚ g)]
    {Rₚ : forall (_ : t), Type*} [forall (g : t), CommSemiring (Rₚ g)] [forall (g : t), Algebra R (Rₚ g)]
    [h₁ : forall (g : t), IsLocalization.Away g.val (Rₚ g)]
    [forall (g : t), Module (Rₚ g) (Mₚ g)] [forall (g : t), IsScalarTower R (Rₚ g) (Mₚ g)]
    (f : forall (g : t), M ->ₗ[R] Mₚ g) [h₂ : forall (g : t), IsLocalizedModule.Away g.val (f g)]
    (H : forall (g : t), Module.Finite (Rₚ g) (Mₚ g)) :
    Module.Finite R M := by
  rw [Ideal.span_eq_top_iff_finite] at ht
  obtain ⟨t', hc, ht'⟩ := ht
  have (g : t') : IsLocalization.Away g.val (Rₚ ⟨g.val, hc g.property⟩) :=
    h₁ ⟨g.val, hc g.property⟩
  have (g : t') : IsLocalizedModule.Away g.val
    ((fun g => f ⟨g.val, hc g.property⟩) g) := h₂ ⟨g.val, hc g.property⟩
  apply of_localizationSpan_finite' t' ht' (fun g => f ⟨g.val, hc g.property⟩)
    (fun g => H ⟨g.val, hc g.property⟩)

/--
theorem `of_localizationSpan_finite` / 定理 `of_localizationSpan_finite`

English:
theorem of_localizationSpan_finite
  statement: (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
  proof: let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan_finite' t ht f H

中文:
定理 of_localizationSpan_finite
  结论: (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
  证明: let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan_finite' t ht f H

Depends on / 依赖: LocalizedModule, LocalizedModule.Away, LocalizedModule.mkLinearMap, Submonoid, Submonoid.powers, g.val, mkLinearMap, of_localizationSpan_finite, powers
-/
theorem of_localizationSpan_finite (t : Finset R) (ht : Ideal.span (t : Set R) = ⊤)
    (H : forall (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.Finite R M :=
  let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan_finite' t ht f H

/--
theorem `of_localizationSpan` / 定理 `of_localizationSpan`

English:
theorem of_localizationSpan
  statement: (t : Set R) (ht : Ideal.span t = ⊤)
  proof: let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan' t ht f H

中文:
定理 of_localizationSpan
  结论: (t : Set R) (ht : Ideal.span t = ⊤)
  证明: let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan' t ht f H

Depends on / 依赖: LocalizedModule, LocalizedModule.Away, LocalizedModule.mkLinearMap, Submonoid, Submonoid.powers, g.val, mkLinearMap, of_localizationSpan, powers
-/
theorem of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : forall (g : t), Module.Finite (Localization.Away g.val)
      (LocalizedModule.Away g.val M)) :
    Module.Finite R M :=
  let f (g : t) : M ->ₗ[R] LocalizedModule.Away g.val M :=
    LocalizedModule.mkLinearMap (Submonoid.powers g.val) M
  of_localizationSpan' t ht f H

end Finite

end Module

namespace Submodule

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Submodule R M}

/--
lemma `of_localizationSpan'` / 引理 `of_localizationSpan'`

English:
lemma of_localizationSpan'
  statement: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  proof: by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan' s hs
    (fun g => N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g => Module.Finite.iff_fg.mpr (H g))]

中文:
引理 of_localizationSpan'
  结论: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  证明: by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan' s hs
    (fun g => N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g => Module.Finite.iff_fg.mpr (H g))]

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, Module.Finite.iff_fg.mpr, Module.Finite.of_localizationSpan, N.toLocalized, Submonoid, Submonoid.powers, iff_fg, of_localizationSpan, powers, toLocalized
-/
lemma of_localizationSpan' (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    {Mₚ : forall (_ : s), Type*} [forall (g : s), AddCommMonoid (Mₚ g)] [forall (g : s), Module R (Mₚ g)]
    {Rₚ : forall (_ : s), Type*} [forall (g : s), CommSemiring (Rₚ g)] [forall (g : s), Algebra R (Rₚ g)]
    [forall (g : s), IsLocalization.Away g.val (Rₚ g)]
    [forall (g : s), Module (Rₚ g) (Mₚ g)] [forall (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : forall (g : s), M ->ₗ[R] Mₚ g) [forall (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (H : forall (g : s), (N.localized' (Rₚ g) (Submonoid.powers g.1) (ϕ g)).FG) :
    N.FG := by
  simp [← Module.Finite.iff_fg, Module.Finite.of_localizationSpan' s hs
    (fun g => N.toLocalized' (Rₚ g) (Submonoid.powers g.1) (ϕ g))
    (fun g => Module.Finite.iff_fg.mpr (H g))]

/--
lemma `of_localizationSpan` / 引理 `of_localizationSpan`

English:
lemma of_localizationSpan
  statement: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  proof: N.of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) H

中文:
引理 of_localizationSpan
  结论: (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
  证明: N.of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) H

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, N.of_localizationSpan, Submonoid, Submonoid.powers, mkLinearMap, of_localizationSpan, powers
-/
lemma of_localizationSpan (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    (H : forall (g : s), (localized (Submonoid.powers g.1) N).FG) : N.FG :=
  N.of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) H

variable (R' : Type*) [CommSemiring R'] [Algebra R R']
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
  (S : Submonoid R) [IsLocalization S R'] (f : M ->ₗ[R] M') [IsLocalizedModule S f]

/--
lemma `localized'_fg` / 引理 `localized'_fg`

English:
lemma localized'_fg
  given: (h : N.FG)
  statement: (N.localized' R' S f).FG
  proof: by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  exact ⟨f '' s, hfin.image f, by rw [← hspan, localized'_span]⟩

中文:
引理 localized'_fg
  条件: (h : N.FG)
  结论: (N.localized' R' S f).FG
  证明: by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  exact ⟨f '' s, hfin.image f, by rw [← hspan, localized'_span]⟩

Depends on / 依赖: _span, fg_def, hfin.image, localized
-/
lemma localized'_fg (h : N.FG) : (N.localized' R' S f).FG := by
  rw [fg_def] at h ⊢
  rcases h with ⟨s, hfin, hspan⟩
  exact ⟨f '' s, hfin.image f, by rw [← hspan, localized'_span]⟩

/--
lemma `localized_fg` / 引理 `localized_fg`

English:
lemma localized_fg
  given: (h : N.FG)
  statement: (N.localized S).FG
  proof: localized'_fg _ S _ h

中文:
引理 localized_fg
  条件: (h : N.FG)
  结论: (N.localized S).FG
  证明: localized'_fg _ S _ h

Depends on / 依赖: localized
-/
lemma localized_fg (h : N.FG) : (N.localized S).FG := localized'_fg _ S _ h

end Submodule

namespace Ideal

variable {R : Type u} [CommSemiring R]

/--
lemma `fg_of_localizationSpan` / 引理 `fg_of_localizationSpan`

English:
lemma fg_of_localizationSpan
  statement: {I : Ideal R} (t : Set R) (ht : Ideal.span t = ⊤)
  proof: by
  apply Module.Finite.iff_fg.mp
  let k (g : t) : I ->ₗ[R] (I.map (algebraMap R (Localization.Away g.val))) :=
    Algebra.idealMap I (S := Localization.Away g.val)
  exact Module.Finite.of_localizationSpan' t ht k (fun g => .of_fg (H g))

中文:
引理 fg_of_localizationSpan
  结论: {I : Ideal R} (t : Set R) (ht : Ideal.span t = ⊤)
  证明: by
  apply Module.Finite.iff_fg.mp
  let k (g : t) : I ->ₗ[R] (I.map (algebraMap R (Localization.Away g.val))) :=
    Algebra.idealMap I (S := Localization.Away g.val)
  exact Module.Finite.of_localizationSpan' t ht k (fun g => .of_fg (H g))

Depends on / 依赖: Algebra, Algebra.idealMap, Finite, I.map, Localization, Localization.Away, Module, Module.Finite.iff_fg.mp, Module.Finite.of_localizationSpan, algebraMap, g.val, idealMap, iff_fg, of_fg, of_localizationSpan
-/
lemma fg_of_localizationSpan {I : Ideal R} (t : Set R) (ht : Ideal.span t = ⊤)
    (H : forall (g : t), (I.map (algebraMap R (Localization.Away g.val))).FG) : I.FG := by
  apply Module.Finite.iff_fg.mp
  let k (g : t) : I ->ₗ[R] (I.map (algebraMap R (Localization.Away g.val))) :=
    Algebra.idealMap I (S := Localization.Away g.val)
  exact Module.Finite.of_localizationSpan' t ht k (fun g => .of_fg (H g))

end Ideal

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S] {f : R ->+* S}

/--
lemma `RingHom.ker_fg_of_localizationSpan` / 引理 `RingHom.ker_fg_of_localizationSpan`

English:
lemma RingHom.ker_fg_of_localizationSpan
  statement: (t : Set R) (ht : Ideal.span t = ⊤)
  proof: by
  apply Ideal.fg_of_localizationSpan t ht
  intro g
  rw [← IsLocalization.ker_map (Localization.Away (f g.val)) f (Submonoid.map_powers f g.val)]
  exact H g

中文:
引理 RingHom.ker_fg_of_localizationSpan
  结论: (t : Set R) (ht : Ideal.span t = ⊤)
  证明: by
  apply Ideal.fg_of_localizationSpan t ht
  intro g
  rw [← IsLocalization.ker_map (Localization.Away (f g.val)) f (Submonoid.map_powers f g.val)]
  exact H g

Depends on / 依赖: Ideal.fg_of_localizationSpan, IsLocalization, IsLocalization.ker_map, Localization, Localization.Away, Submonoid, Submonoid.map_powers, fg_of_localizationSpan, g.val, ker_map, map_powers
-/
lemma RingHom.ker_fg_of_localizationSpan (t : Set R) (ht : Ideal.span t = ⊤)
    (H : forall g : t, (RingHom.ker (Localization.awayMap f g.val)).FG) :
    (RingHom.ker f).FG := by
  apply Ideal.fg_of_localizationSpan t ht
  intro g
  rw [← IsLocalization.ker_map (Localization.Away (f g.val)) f (Submonoid.map_powers f g.val)]
  exact H g
