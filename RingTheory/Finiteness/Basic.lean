/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Order.Nonneg.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Basic results on finitely generated (sub)modules

This file contains the basic results on `Submodule.FG` and `Module.Finite` that do not need heavy
further imports.
-/

public section

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/--
theorem `fg_bot` / 定理 `fg_bot`

English:
theorem fg_bot
  statement: (⊥ : Submodule R M).FG
  proof: ⟨∅, by rw [Finset.coe_empty, span_empty]⟩

中文:
定理 fg_bot
  结论: (⊥ : Submodule R M).FG
  证明: ⟨∅, by rw [Finset.coe_empty, span_empty]⟩

Depends on / 依赖: Finset, Finset.coe_empty, coe_empty, span_empty
-/
theorem fg_bot : (⊥ : Submodule R M).FG :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩

/--
theorem `fg_span` / 定理 `fg_span`

English:
theorem fg_span
  given: {s : Set M} (hs : s.Finite)
  statement: FG (span R s)
  proof: ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

中文:
定理 fg_span
  条件: {s : Set M} (hs : s.Finite)
  结论: FG (span R s)
  证明: ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

Depends on / 依赖: coe_toFinset, hs.coe_toFinset, hs.toFinset, toFinset
-/
theorem fg_span {s : Set M} (hs : s.Finite) : FG (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

/--
theorem `fg_span_singleton` / 定理 `fg_span_singleton`

English:
theorem fg_span_singleton
  given: (x : M)
  statement: FG (R ∙ x)
  proof: fg_span (finite_singleton x)

中文:
定理 fg_span_singleton
  条件: (x : M)
  结论: FG (R ∙ x)
  证明: fg_span (finite_singleton x)

Depends on / 依赖: fg_span, finite_singleton
-/
theorem fg_span_singleton (x : M) : FG (R ∙ x) :=
  fg_span (finite_singleton x)

/--
theorem `FG.sup` / 定理 `FG.sup`

English:
theorem FG.sup
  given: {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG)
  statement: (N₁ ⊔ N₂).FG
  proof: let ⟨t₁, ht₁, span_t₁⟩ := fg_def.mp hN₁
  let ⟨t₂, ht₂, span_t₂⟩ := fg_def.mp hN₂
  fg_def.mpr ⟨t₁ union t₂, ht₁.union ht₂, by rw [span_union, span_t₁, span_t₂]⟩

中文:
定理 FG.sup
  条件: {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG)
  结论: (N₁ ⊔ N₂).FG
  证明: let ⟨t₁, ht₁, span_t₁⟩ := fg_def.mp hN₁
  let ⟨t₂, ht₂, span_t₂⟩ := fg_def.mp hN₂
  fg_def.mpr ⟨t₁ union t₂, ht₁.union ht₂, by rw [span_union, span_t₁, span_t₂]⟩
-/
theorem FG.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁, span_t₁⟩ := fg_def.mp hN₁
  let ⟨t₂, ht₂, span_t₂⟩ := fg_def.mp hN₂
  fg_def.mpr ⟨t₁ union t₂, ht₁.union ht₂, by rw [span_union, span_t₁, span_t₂]⟩

/--
theorem `fg_finset_sup` / 定理 `fg_finset_sup`

English:
theorem fg_finset_sup
  given: {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : forall i in s, (N i).FG)
  proof: Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h

中文:
定理 fg_finset_sup
  条件: {ι : 类型} (s : Finset ι) (N : ι -> Submodule R M) (h : 对任意 i in s, (N i).FG)
  证明: Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h

Depends on / 依赖: Finset, Finset.sup_induction, fg_bot, ha.sup, sup_induction
-/
theorem fg_finset_sup {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : forall i in s, (N i).FG) :
    (s.sup N).FG :=
  Finset.sup_induction fg_bot (fun _ ha _ hb => ha.sup hb) h

/--
theorem `fg_biSup` / 定理 `fg_biSup`

English:
theorem fg_biSup
  given: {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : forall i in s, (N i).FG)
  proof: by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h

中文:
定理 fg_biSup
  条件: {ι : 类型} (s : Finset ι) (N : ι -> Submodule R M) (h : 对任意 i in s, (N i).FG)
  证明: by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h

Depends on / 依赖: Finset, Finset.sup_eq_iSup, fg_finset_sup, sup_eq_iSup
-/
theorem fg_biSup {ι : Type*} (s : Finset ι) (N : ι -> Submodule R M) (h : forall i in s, (N i).FG) :
    (⨆ i in s, N i).FG := by simpa only [Finset.sup_eq_iSup] using fg_finset_sup s N h

/--
theorem `fg_iSup` / 定理 `fg_iSup`

English:
theorem fg_iSup
  given: {ι : Sort*} [Finite ι] (N : ι -> Submodule R M) (h : forall i, (N i).FG)
  proof: by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down

中文:
定理 fg_iSup
  条件: {ι : Sort*} [Finite ι] (N : ι -> Submodule R M) (h : 对任意 i, (N i).FG)
  证明: by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down

Depends on / 依赖: Finset, Finset.univ, PLift.down, fg_biSup, i.down, iSup_plift_down, nonempty_fintype
-/
theorem fg_iSup {ι : Sort*} [Finite ι] (N : ι -> Submodule R M) (h : forall i, (N i).FG) :
    (iSup N).FG := by
  cases nonempty_fintype (PLift ι)
  simpa [iSup_plift_down] using fg_biSup Finset.univ (N ∘ PLift.down) fun i _ => h i.down

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup {P : Submodule R M // P.FG}
  body: fun P Q => ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢


中文:
实例 :
  签名: SemilatticeSup {P : Submodule R M // P.FG}
  定义体: fun P Q => ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢


Depends on / 依赖: P.property, P.val, Q.property, Q.val, Submodule, Submodule.FG.sup, property
-/
instance : SemilatticeSup {P : Submodule R M // P.FG} where
  sup := fun P Q => ⟨P.val ⊔ Q.val, Submodule.FG.sup P.property Q.property⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun P Q R hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited {P : Submodule R M // P.FG}
  body: ⟨⊥, fg_bot⟩

中文:
实例 :
  签名: Inhabited {P : Submodule R M // P.FG}
  定义体: ⟨⊥, fg_bot⟩

Depends on / 依赖: fg_bot
-/
instance : Inhabited {P : Submodule R M // P.FG} where
  default := ⟨⊥, fg_bot⟩

section

variable {S P : Type*} [Semiring S] [AddCommMonoid P] [Module S P]
variable {σ : R ->+* S} [RingHomSurjective σ] (f : M ->ₛₗ[σ] P)

/--
theorem `fg_pi` / 定理 `fg_pi`

English:
theorem fg_pi
  statement: {ι : Type*} {M : ι -> Type*} [Finite ι] [forall i, AddCommMonoid (M i)]
  proof: by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    sim

中文:
定理 fg_pi
  结论: {ι : 类型} {M : ι -> 类型} [Finite ι] [对任意 i, AddCommMonoid (M i)]
  证明: by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    sim

Depends on / 依赖: LinearMap, LinearMap.single, Set.finite_iUnion, classical, fg_def, finite_iUnion, simp_rw, single
-/
theorem fg_pi {ι : Type*} {M : ι -> Type*} [Finite ι] [forall i, AddCommMonoid (M i)]
    [forall i, Module R (M i)] {p : forall i, Submodule R (M i)} (hsb : forall i, (p i).FG) :
    (pi Set.univ p).FG := by
  classical
    simp_rw [fg_def] at hsb ⊢
    choose t htf hts using hsb
    refine
      ⟨⋃ i, (LinearMap.single R _ i) '' t i, Set.finite_iUnion fun i => (htf i).image _, ?_⟩
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `span_image` into `span_image _`
    simp_rw [span_iUnion, span_image _, hts, iSup_map_single]

/--
theorem `FG.map` / 定理 `FG.map`

English:
theorem FG.map
  given: {N : Submodule R M} (hs : N.FG)
  statement: (N.map f).FG
  proof: let ⟨t, ht, span_t⟩ := fg_def.mp hs
  fg_def.mpr ⟨f '' t, ht.image _, by rw [span_image, span_t]⟩

中文:
定理 FG.map
  条件: {N : Submodule R M} (hs : N.FG)
  结论: (N.map f).FG
  证明: let ⟨t, ht, span_t⟩ := fg_def.mp hs
  fg_def.mpr ⟨f '' t, ht.image _, by rw [span_image, span_t]⟩
-/
theorem FG.map {N : Submodule R M} (hs : N.FG) : (N.map f).FG :=
  let ⟨t, ht, span_t⟩ := fg_def.mp hs
  fg_def.mpr ⟨f '' t, ht.image _, by rw [span_image, span_t]⟩

/--
lemma `fg_range` / 引理 `fg_range`

English:
lemma fg_range
  given: [Module.Finite R M] (f : M ->ₛₗ[σ] P)
  statement: f.range.FG
  proof: by
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

中文:
引理 fg_range
  条件: [Module.Finite R M] (f : M ->ₛₗ[σ] P)
  结论: f.range.FG
  证明: by
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f
-/
@[simp] lemma fg_range [Module.Finite R M] (f : M ->ₛₗ[σ] P) : f.range.FG := by
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fg_of_fg_map_injective` / 定理 `fg_of_fg_map_injective`

English:
theorem fg_of_fg_map_injective
  statement: (hf : Function.Injective f) {N : Submodule R M}
  proof: let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun _ _ _ _ h => hf h,
map_injective_of_injective hf by
      rw [map_span]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_self_of_subset_left]; rw [ht]
      rw [← LinearMap.coe_range]; rw [← span_le]; rw [ht]; rw [← map_top]
 

中文:
定理 fg_of_fg_map_injective
  结论: (hf : Function.Injective f) {N : Submodule R M}
  证明: let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun _ _ _ _ h => hf h,
map_injective_of_injective hf by
      rw [map_span]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_self_of_subset_left]; rw [ht]
      rw [← LinearMap.coe_range]; rw [← span_le]; rw [ht]; rw [← map_top]
 

Depends on / 依赖: Finset, Finset.coe_preimage, LinearMap, LinearMap.coe_range, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, coe_preimage, coe_range, image_preimage_eq_inter_range, inter_eq_self_of_subset_left, le_top, map_injective_of_injective, map_mono, map_span, map_top, preimage, span_le, t.preimage
-/
theorem fg_of_fg_map_injective (hf : Function.Injective f) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f fun _ _ _ _ h => hf h,
map_injective_of_injective hf by
      rw [map_span]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_inter_range]; rw [Set.inter_eq_self_of_subset_left]; rw [ht]
      rw [← LinearMap.coe_range]; rw [← span_le]; rw [ht]; rw [← map_top]
      exact map_mono le_top⟩

/--
theorem `fg_map_iff` / 定理 `fg_map_iff`

English:
theorem fg_map_iff
  given: (hf : Function.Injective f) {N : Submodule R M}
  proof: ⟨(fg_of_fg_map_injective _ hf ·), (.map _)⟩

中文:
定理 fg_map_iff
  条件: (hf : Function.Injective f) {N : Submodule R M}
  证明: ⟨(fg_of_fg_map_injective _ hf ·), (.map _)⟩

Depends on / 依赖: fg_of_fg_map_injective
-/
theorem fg_map_iff (hf : Function.Injective f) {N : Submodule R M} :
    (N.map f).FG ↔ N.FG :=
  ⟨(fg_of_fg_map_injective _ hf ·), (.map _)⟩

end

variable {P : Type*} [AddCommMonoid P] [Module R P]
variable {f : M ->ₗ[R] P}

/--
theorem `fg_of_fg_map` / 定理 `fg_of_fg_map`

English:
theorem fg_of_fg_map
  statement: {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
  proof: fg_of_fg_map_injective f (LinearMap.ker_eq_bot.mp hf) hfn

中文:
定理 fg_of_fg_map
  结论: {R M P : 类型} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
  证明: fg_of_fg_map_injective f (LinearMap.ker_eq_bot.mp hf) hfn

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mp, fg_of_fg_map_injective, ker_eq_bot
-/
theorem fg_of_fg_map {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M ->ₗ[R] P) (hf : LinearMap.ker f = ⊥) {N : Submodule R M}
    (hfn : (N.map f).FG) : N.FG :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.mp hf) hfn

/--
theorem `fg_top` / 定理 `fg_top`

English:
theorem fg_top
  given: (N : Submodule R M)
  statement: (⊤ : Submodule R N).FG ↔ N.FG
  proof: by
  rw [← fg_map_iff N.subtype Subtype.val_injective]; rw [map_top]; rw [range_subtype]

中文:
定理 fg_top
  条件: (N : Submodule R M)
  结论: (⊤ : Submodule R N).FG ↔ N.FG
  证明: by
  rw [← fg_map_iff N.subtype Subtype.val_injective]; rw [map_top]; rw [range_subtype]
-/
protected theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).FG ↔ N.FG := by
  rw [← fg_map_iff N.subtype Subtype.val_injective]; rw [map_top]; rw [range_subtype]

/--
theorem `fg_of_linearEquiv` / 定理 `fg_of_linearEquiv`

English:
theorem fg_of_linearEquiv
  given: (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG)
  statement: (⊤ : Submodule R M).FG
  proof: e.symm.range ▸ map_top (e.symm : P ->ₗ[R] M) ▸ h.map _

中文:
定理 fg_of_linearEquiv
  条件: (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG)
  结论: (⊤ : Submodule R M).FG
  证明: e.symm.range ▸ map_top (e.symm : P ->ₗ[R] M) ▸ h.map _

Depends on / 依赖: e.symm, e.symm.range, h.map, map_top
-/
theorem fg_of_linearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).FG) : (⊤ : Submodule R M).FG :=
  e.symm.range ▸ map_top (e.symm : P ->ₗ[R] M) ▸ h.map _

/--
theorem `fg_induction` / 定理 `fg_induction`

English:
theorem fg_induction
  statement: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simpa using singleton 0
  | insert x s hxs ih =>
    simpa [span_insert, sup_comm] using
      sup (span R s) (R ∙ x) _ (fg_span_singleton _) ih (singleton x)

中文:
定理 fg_induction
  结论: {R M : 类型} [Semiring R] [AddCommMonoid M] [Module R M]
  证明: by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simpa using singleton 0
  | insert x s hxs ih =>
    simpa [span_insert, sup_comm] using
      sup (span R s) (R ∙ x) _ (fg_span_singleton _) ih (singleton x)

Depends on / 依赖: Finset, Finset.induction, classical, fg_span_singleton, insert, singleton, span_insert, sup_comm
-/
theorem fg_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {motive : forall N : Submodule R M, N.FG -> Prop}
    (singleton : forall x : M, motive (R ∙ x) (fg_span_singleton _))
    (sup : forall (N₁ N₂ : Submodule R M) (hN₁ : N₁.FG) (hN₂ : N₂.FG),
      motive N₁ hN₁ -> motive N₂ hN₂ -> motive (N₁ ⊔ N₂) (hN₁.sup hN₂))
    (N : Submodule R M) (hN : N.FG) : motive N hN := by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simpa using singleton 0
  | insert x s hxs ih =>
    simpa [span_insert, sup_comm] using
      sup (span R s) (R ∙ x) _ (fg_span_singleton _) ih (singleton x)

/--
theorem `fg_sup_span_induction` / 定理 `fg_sup_span_induction`

English:
theorem fg_sup_span_induction
  statement: {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simp [bot]
  | insert x s hxs ih => simpa [span_insert, sup_comm] using sup (span R s) x (by use s) ih

中文:
定理 fg_sup_span_induction
  结论: {R M : 类型} [Semiring R] [AddCommMonoid M] [Module R M]
  证明: by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simp [bot]
  | insert x s hxs ih => simpa [span_insert, sup_comm] using sup (span R s) x (by use s) ih

Depends on / 依赖: Finset, Finset.induction, classical, insert, span_insert, sup_comm
-/
theorem fg_sup_span_induction {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {motive : forall N : Submodule R M, N.FG -> Prop}
    (bot : motive ⊥ fg_bot)
    (sup : forall (N : Submodule R M) (x : M) (hN : N.FG),
      motive N hN -> motive (N ⊔ (R ∙ x)) (hN.sup <| fg_span_singleton x))
    (N : Submodule R M) (hN : N.FG) : motive N hN := by classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction with
  | empty => simp [bot]
  | insert x s hxs ih => simpa [span_insert, sup_comm] using sup (span R s) x (by use s) ih

section RestrictScalars

variable {R A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
variable {S : Submodule A M}

/--
theorem `FG.restrictScalars_of_surjective` / 定理 `FG.restrictScalars_of_surjective`

English:
theorem FG.restrictScalars_of_surjective
  statement: [CommSemiring R] [Algebra R A] [Module R M]
  proof: by
  obtain ⟨s, rfl⟩ := hS
exact ⟨s, .symm restrictScalars_span R A h _⟩

@[deprecated (since := "2026-01-24")]
alias fg_restrictScalars := FG.restrictScalars_of_surjective

中文:
定理 FG.restrictScalars_of_surjective
  结论: [CommSemiring R] [Algebra R A] [Module R M]
  证明: by
  obtain ⟨s, rfl⟩ := hS
exact ⟨s, .symm restrictScalars_span R A h _⟩

@[deprecated (since := "2026-01-24")]
alias fg_restrictScalars := FG.restrictScalars_of_surjective

Depends on / 依赖: restrictScalars_span
-/
theorem FG.restrictScalars_of_surjective [CommSemiring R] [Algebra R A] [Module R M]
    [IsScalarTower R A M] (hS : S.FG) (h : Function.Surjective (algebraMap R A)) :
    (restrictScalars R S).FG := by
  obtain ⟨s, rfl⟩ := hS
exact ⟨s, .symm restrictScalars_span R A h _⟩

@[deprecated (since := "2026-01-24")]
alias fg_restrictScalars := FG.restrictScalars_of_surjective

/--
theorem `FG.of_restrictScalars` / 定理 `FG.of_restrictScalars`

English:
theorem FG.of_restrictScalars
  statement: (R) [Semiring R] [Module R M] [SMul R A] [IsScalarTower R A M]
  proof: by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · have := span_le.mp e.le
    rwa [restrictScalars_le, span_le]
  · rw [← e]
    exact span_le_restrictScalars ..

中文:
定理 FG.of_restrictScalars
  结论: (R) [Semiring R] [Module R M] [SMul R A] [IsScalarTower R A M]
  证明: by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · have := span_le.mp e.le
    rwa [restrictScalars_le, span_le]
  · rw [← e]
    exact span_le_restrictScalars ..
-/
theorem FG.of_restrictScalars (R) [Semiring R] [Module R M] [SMul R A] [IsScalarTower R A M]
    (hS : (S.restrictScalars R).FG) : S.FG := by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · have := span_le.mp e.le
    rwa [restrictScalars_le, span_le]
  · rw [← e]
    exact span_le_restrictScalars ..

end RestrictScalars

/--
theorem `FG.stabilizes_of_iSup_eq` / 定理 `FG.stabilizes_of_iSup_eq`

English:
theorem FG.stabilizes_of_iSup_eq
  statement: {M' : Submodule R M} (hM' : M'.FG) (N : Nat ->o Submodule R M)
  proof: by
  obtain ⟨S, hS⟩ := hM'
  have (s : S) : exists n, (s : M) in N n :=
    (mem_iSup_of_chain N s).mp (by simpa [H, ← hS] using subset_span s.prop)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · rw [← hS, span_le]
    intro s hs
    exact N.monotone' (Finset.le_sup <| S.mem_a

中文:
定理 FG.stabilizes_of_iSup_eq
  结论: {M' : Submodule R M} (hM' : M'.FG) (N : 自然数 ->o Submodule R M)
  证明: by
  obtain ⟨S, hS⟩ := hM'
  have (s : S) : exists n, (s : M) in N n :=
    (mem_iSup_of_chain N s).mp (by simpa [H, ← hS] using subset_span s.prop)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · rw [← hS, span_le]
    intro s hs
    exact N.monotone' (Finset.le_sup <| S.mem_a

Depends on / 依赖: Finset, Finset.le_sup, N.monotone, S.attach.sup, S.mem_attach, attach, le_antisymm, le_iSup, le_sup, mem_attach, mem_iSup_of_chain, monotone, s.prop, span_le, subset_span
-/
theorem FG.stabilizes_of_iSup_eq {M' : Submodule R M} (hM' : M'.FG) (N : Nat ->o Submodule R M)
    (H : iSup N = M') : exists n, M' = N n := by
  obtain ⟨S, hS⟩ := hM'
  have (s : S) : exists n, (s : M) in N n :=
    (mem_iSup_of_chain N s).mp (by simpa [H, ← hS] using subset_span s.prop)
  choose f hf using this
  use S.attach.sup f
  apply le_antisymm
  · rw [← hS, span_le]
    intro s hs
    exact N.monotone' (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
  · rw [← H]
    exact le_iSup ..

/--
theorem `fg_iff_compact` / 定理 `fg_iff_compact`

English:
theorem fg_iff_compact
  given: (s : Submodule R M)
  statement: s.FG ↔ IsCompactElement s
  proof: by
  -- Introduce shorthand for span of an element
  let sp : M -> Submodule R M := fun a => span R {a}
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : forall t : Finset M, ⨆ x in t, sp x = ⨆ x in (↑t : Set M), sp x := fun t => by rfl


中文:
定理 fg_iff_compact
  条件: (s : Submodule R M)
  结论: s.FG ↔ IsCompactElement s
  证明: by
  -- Introduce shorthand for span of an element
  let sp : M -> Submodule R M := fun a => span R {a}
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : forall t : Finset M, ⨆ x in t, sp x = ⨆ x in (↑t : Set M), sp x := fun t => by rfl

-/
theorem fg_iff_compact (s : Submodule R M) : s.FG ↔ IsCompactElement s := by
  -- Introduce shorthand for span of an element
  let sp : M -> Submodule R M := fun a => span R {a}
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : forall t : Finset M, ⨆ x in t, sp x = ⨆ x in (↑t : Set M), sp x := fun t => by rfl
  constructor
  · rintro ⟨t, rfl⟩
    rw [span_eq_iSup_of_singleton_spans]; rw [← supr_rw]; rw [← t.sup_eq_iSup sp]
    apply CompleteLattice.isCompactElement_finsetSup
    exact fun n _ => singleton_span_isCompactElement n
  · intro h
    rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at h
    -- s is the Sup of the spans of its elements.
    have sSup' : s = sSup (sp '' ↑s) := by
      rw [sSup_eq_iSup]; rw [iSup_image]; rw [← span_eq_iSup_of_singleton_spans]; rw [eq_comm]; rw [span_eq]
    -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
    obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup')
    have ssup : s = u.sup id := by
      suffices u.sup id <= s from le_antisymm husup this
      rw [sSup']; rw [Finset.sup_id_eq_sSup]
      exact sSup_le_sSup huspan
    obtain ⟨t, -, rfl⟩ := Finset.subset_set_image_iff.mp huspan
    rw [Finset.sup_image]; rw [Function.id_comp]; rw [Finset.sup_eq_iSup]; rw [supr_rw]; rw [← span_eq_iSup_of_singleton_spans]; rw [eq_comm] at ssup
    exact ⟨t, ssup⟩

end Submodule

section ModuleAndAlgebra

variable (R A B M N : Type*)

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R M N}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R M] : IsCoatomic (Submodule R M)
  body: CompleteLattice.coatomic_of_top_compact by rwa [← fg_iff_compact, ← finite_def]

中文:
实例 [Module.Finite
  签名: R M] : IsCoatomic (Submodule R M)
  定义体: CompleteLattice.coatomic_of_top_compact by rwa [← fg_iff_compact, ← finite_def]

Depends on / 依赖: CompleteLattice, CompleteLattice.coatomic_of_top_compact, coatomic_of_top_compact, fg_iff_compact, finite_def
-/
instance [Module.Finite R M] : IsCoatomic (Submodule R M) :=
CompleteLattice.coatomic_of_top_compact by rwa [← fg_iff_compact, ← finite_def]

-- See note [lower instance priority]
instance (priority := 100) of_finite [Finite M] : Module.Finite R M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ, span_univ]⟩⟩

section

variable {S} {P : Type*} [Semiring S] [AddCommMonoid P] [Module S P] {σ : R ->+* S}

@[stacks 0519 "(3)"]
/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: [hM : Module.Finite R M] (f : M ->ₛₗ[σ] P) (hf : Surjective f)
  proof: by
  rw [Module.finite_def]; rw [Submodule.fg_def] at hM ⊢
  obtain ⟨s, hsfin, hs⟩ := hM
  refine ⟨f '' s, hsfin.image f, eq_top_iff.mpr fun p _ => ?_⟩
  exact image_span_subset_span f s (by simpa [hs] using hf p)

中文:
定理 of_surjective
  条件: [hM : Module.Finite R M] (f : M ->ₛₗ[σ] P) (hf : Surjective f)
  证明: by
  rw [Module.finite_def]; rw [Submodule.fg_def] at hM ⊢
  obtain ⟨s, hsfin, hs⟩ := hM
  refine ⟨f '' s, hsfin.image f, eq_top_iff.mpr fun p _ => ?_⟩
  exact image_span_subset_span f s (by simpa [hs] using hf p)

Depends on / 依赖: Module, Module.finite_def, Submodule, Submodule.fg_def, eq_top_iff, eq_top_iff.mpr, fg_def, finite_def, hsfin.image, image_span_subset_span
-/
theorem of_surjective [hM : Module.Finite R M] (f : M ->ₛₗ[σ] P) (hf : Surjective f) :
    Module.Finite S P := by
  rw [Module.finite_def]; rw [Submodule.fg_def] at hM ⊢
  obtain ⟨s, hsfin, hs⟩ := hM
  refine ⟨f '' s, hsfin.image f, eq_top_iff.mpr fun p _ => ?_⟩
  exact image_span_subset_span f s (by simpa [hs] using hf p)

/--
theorem `_root_.LinearMap.finite_iff_of_bijective` / 定理 `_root_.LinearMap.finite_iff_of_bijective`

English:
theorem _root_.LinearMap.finite_iff_of_bijective
  statement: [RingHomSurjective σ]
  proof: ⟨fun _ => of_surjective f hf.surjective, fun _ => ⟨fg_of_fg_map_injective f hf.injective by
    rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hf.surjective, ← Module.finite_def]⟩⟩

中文:
定理 _root_.LinearMap.finite_iff_of_bijective
  结论: [RingHomSurjective σ]
  证明: ⟨fun _ => of_surjective f hf.surjective, fun _ => ⟨fg_of_fg_map_injective f hf.injective by
    rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hf.surjective, ← Module.finite_def]⟩⟩

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, Module, Module.finite_def, Submodule, Submodule.map_top, fg_of_fg_map_injective, finite_def, hf.injective, hf.surjective, injective, map_top, of_surjective, range_eq_top, surjective
-/
theorem _root_.LinearMap.finite_iff_of_bijective [RingHomSurjective σ]
    (f : M ->ₛₗ[σ] P) (hf : Function.Bijective f) : Module.Finite R M ↔ Module.Finite S P :=
⟨fun _ => of_surjective f hf.surjective, fun _ => ⟨fg_of_fg_map_injective f hf.injective by
    rwa [Submodule.map_top, LinearMap.range_eq_top.mpr hf.surjective, ← Module.finite_def]⟩⟩

end

/--
Instance `quotient` / 实例 `quotient`

English:
instance quotient
  signature: (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
  body: Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

中文:
实例 quotient
  签名: (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
  定义体: Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

Depends on / 依赖: Finite, Module, Module.Finite.of_surjective, N.mkQ.restrictScalars, N.mkQ_surjective, mkQ_surjective, of_surjective, restrictScalars
-/
instance quotient (R) {A M} [Semiring R] [AddCommGroup M] [Ring A] [Module A M] [Module R M]
    [SMul R A] [IsScalarTower R A M] [Module.Finite R M] (N : Submodule A M) :
    Module.Finite R (M ⧸ N) :=
  Module.Finite.of_surjective (N.mkQ.restrictScalars R) N.mkQ_surjective

/--
Instance `range` / 实例 `range`

English:
instance range
  signature: [Module.Finite R M] (f : M ->ₗ[R] N)
  body: of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩

中文:
实例 range
  签名: [Module.Finite R M] (f : M ->ₗ[R] N)
  定义体: of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩

Depends on / 依赖: SemilinearMapClass, SemilinearMapClass.semilinearMap, Subtype, Subtype.ext, of_surjective, rangeRestrict, semilinearMap
-/
instance range [Module.Finite R M] (f : M ->ₗ[R] N) : Module.Finite R f.range :=
  of_surjective (SemilinearMapClass.semilinearMap f).rangeRestrict
    fun ⟨_, y, hy⟩ => ⟨y, Subtype.ext hy⟩

/--
Instance `map` / 实例 `map`

English:
instance map
  signature: (p : Submodule R M) [Module.Finite R p] (f : M ->ₗ[R] N)
  body: of_surjective (f.restrict fun _ => mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ => ⟨⟨_, hy⟩, Subtype.ext hy'⟩

中文:
实例 map
  签名: (p : Submodule R M) [Module.Finite R p] (f : M ->ₗ[R] N)
  定义体: of_surjective (f.restrict fun _ => mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ => ⟨⟨_, hy⟩, Subtype.ext hy'⟩

Depends on / 依赖: Subtype, Subtype.ext, f.restrict, mem_map_of_mem, of_surjective, restrict
-/
instance map (p : Submodule R M) [Module.Finite R p] (f : M ->ₗ[R] N) : Module.Finite R (p.map f) :=
  of_surjective (f.restrict fun _ => mem_map_of_mem) fun ⟨_, _, hy, hy'⟩ => ⟨⟨_, hy⟩, Subtype.ext hy'⟩

/--
Instance `pi` / 实例 `pi`

English:
instance pi
  signature: {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMonoid (M i)]
  body: ⟨by
    rw [← pi_top]
    exact fg_pi fun i => (h i).fg_top⟩

中文:
实例 pi
  签名: {ι : 类型} {M : ι -> 类型} [_root_.Finite ι] [对任意 i, AddCommMonoid (M i)]
  定义体: ⟨by
    rw [← pi_top]
    exact fg_pi fun i => (h i).fg_top⟩

Depends on / 依赖: fg_pi, fg_top, pi_top
-/
instance pi {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMonoid (M i)]
    [forall i, Module R (M i)] [h : forall i, Module.Finite R (M i)] : Module.Finite R (forall i, M i) :=
  ⟨by
    rw [← pi_top]
    exact fg_pi fun i => (h i).fg_top⟩

/--
theorem `of_pi` / 定理 `of_pi`

English:
theorem of_pi
  statement: {ι : Type*} (M : ι -> Type*) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
  proof: of_surjective _ LinearMap.proj_surjective i

中文:
定理 of_pi
  结论: {ι : 类型} (M : ι -> 类型) [对任意 i, AddCommMonoid (M i)] [对任意 i, Module R (M i)]
  证明: of_surjective _ LinearMap.proj_surjective i

Depends on / 依赖: LinearMap, LinearMap.proj_surjective, of_surjective, proj_surjective
-/
theorem of_pi {ι : Type*} (M : ι -> Type*) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]
    [Module.Finite R (forall i, M i)] (i : ι) : Module.Finite R (M i) :=
of_surjective _ LinearMap.proj_surjective i

/--
theorem `pi_iff` / 定理 `pi_iff`

English:
theorem pi_iff
  statement: {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMonoid (M i)]
  proof: ⟨fun _ i => of_pi M i, fun _ => inferInstance⟩

中文:
定理 pi_iff
  结论: {ι : 类型} {M : ι -> 类型} [_root_.Finite ι] [对任意 i, AddCommMonoid (M i)]
  证明: ⟨fun _ i => of_pi M i, fun _ => inferInstance⟩

Depends on / 依赖: of_pi
-/
theorem pi_iff {ι : Type*} {M : ι -> Type*} [_root_.Finite ι] [forall i, AddCommMonoid (M i)]
    [forall i, Module R (M i)] : Module.Finite R (forall i, M i) ↔ forall i, Module.Finite R (M i) :=
  ⟨fun _ i => of_pi M i, fun _ => inferInstance⟩

variable (R)

/--
theorem `_root_.Ideal.fg_top` / 定理 `_root_.Ideal.fg_top`

English:
theorem _root_.Ideal.fg_top
  statement: (⊤ : Ideal R).FG
  proof: ⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩

中文:
定理 _root_.Ideal.fg_top
  结论: (⊤ : Ideal R).FG
  证明: ⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩

Depends on / 依赖: Finset, Finset.coe_singleton, Ideal.span_singleton_one, coe_singleton, span_singleton_one
-/
theorem _root_.Ideal.fg_top : (⊤ : Ideal R).FG :=
  ⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : Module.Finite R R
  body: ⟨Ideal.fg_top R⟩

中文:
实例 self
  签名: : Module.Finite R R
  定义体: ⟨Ideal.fg_top R⟩

Depends on / 依赖: Ideal.fg_top, fg_top
-/
instance self : Module.Finite R R := ⟨Ideal.fg_top R⟩

variable (M)

/--
theorem `of_restrictScalars_finite` / 定理 `of_restrictScalars_finite`

English:
theorem of_restrictScalars_finite
  statement: (R A M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M]
  proof: by
  rw [finite_def]; rw [fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.mpr ?_⟩
  have := span_le_restrictScalars R A S
  rwa [hSgen] at this

中文:
定理 of_restrictScalars_finite
  结论: (R A M : 类型) [Semiring R] [Semiring A] [AddCommMonoid M]
  证明: by
  rw [finite_def]; rw [fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.mpr ?_⟩
  have := span_le_restrictScalars R A S
  rwa [hSgen] at this

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, fg_def, finite_def, span_le_restrictScalars
-/
theorem of_restrictScalars_finite (R A M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [SMul R A] [IsScalarTower R A M] [hM : Module.Finite R M] :
    Module.Finite A M := by
  rw [finite_def]; rw [fg_def] at hM ⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine ⟨S, hSfin, eq_top_iff.mpr ?_⟩
  have := span_le_restrictScalars R A S
  rwa [hSgen] at this

variable {R M}

/--
theorem `equiv` / 定理 `equiv`

English:
theorem equiv
  given: [Module.Finite R M] (e : M ≃ₗ[R] N)
  statement: Module.Finite R N
  proof: of_surjective (e : M ->ₗ[R] N) e.surjective

中文:
定理 equiv
  条件: [Module.Finite R M] (e : M ≃ₗ[R] N)
  结论: Module.Finite R N
  证明: of_surjective (e : M ->ₗ[R] N) e.surjective

Depends on / 依赖: e.surjective, of_surjective, surjective
-/
theorem equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.Finite R N :=
  of_surjective (e : M ->ₗ[R] N) e.surjective

/--
theorem `equiv_iff` / 定理 `equiv_iff`

English:
theorem equiv_iff
  given: (e : M ≃ₗ[R] N)
  statement: Module.Finite R M ↔ Module.Finite R N
  proof: ⟨fun _ => equiv e, fun _ => equiv e.symm⟩

中文:
定理 equiv_iff
  条件: (e : M ≃ₗ[R] N)
  结论: Module.Finite R M ↔ Module.Finite R N
  证明: ⟨fun _ => equiv e, fun _ => equiv e.symm⟩

Depends on / 依赖: e.symm
-/
theorem equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔ Module.Finite R N :=
  ⟨fun _ => equiv e, fun _ => equiv e.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Finite
  signature: R M] : Module.Finite R Mᵐᵒᵖ
  body: equiv (MulOpposite.opLinearEquiv R)

中文:
实例 [Module.Finite
  签名: R M] : Module.Finite R Mᵐᵒᵖ
  定义体: equiv (MulOpposite.opLinearEquiv R)

Depends on / 依赖: MulOpposite, MulOpposite.opLinearEquiv, opLinearEquiv
-/
instance [Module.Finite R M] : Module.Finite R Mᵐᵒᵖ := equiv (MulOpposite.opLinearEquiv R)

/--
Instance `ulift` / 实例 `ulift`

English:
instance ulift
  signature: [Module.Finite R M]
  body: equiv ULift.moduleEquiv.symm

universe u in

中文:
实例 ulift
  签名: [Module.Finite R M]
  定义体: equiv ULift.moduleEquiv.symm

universe u in

Depends on / 依赖: ULift.moduleEquiv.symm, moduleEquiv
-/
instance ulift [Module.Finite R M] : Module.Finite R (ULift M) := equiv ULift.moduleEquiv.symm

universe u in
/--
Instance `shrink` / 实例 `shrink`

English:
instance shrink
  signature: [Module.Finite R M] [Small.{u} M]
  body: Module.Finite.equiv (Shrink.linearEquiv R M).symm

中文:
实例 shrink
  签名: [Module.Finite R M] [Small.{u} M]
  定义体: Module.Finite.equiv (Shrink.linearEquiv R M).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, Shrink, Shrink.linearEquiv, linearEquiv
-/
instance shrink [Module.Finite R M] [Small.{u} M] : Module.Finite R (Shrink.{u} M) :=
  Module.Finite.equiv (Shrink.linearEquiv R M).symm

set_option linter.dupNamespace false in
@[deprecated (since := "2026-04-18")] alias Module.finite_shrink := shrink

/--
theorem `iff_fg` / 定理 `iff_fg`

English:
theorem iff_fg
  given: {N : Submodule R M}
  statement: Module.Finite R N ↔ N.FG
  proof: finite_def.trans N.fg_top

中文:
定理 iff_fg
  条件: {N : Submodule R M}
  结论: Module.Finite R N ↔ N.FG
  证明: finite_def.trans N.fg_top

Depends on / 依赖: N.fg_top, fg_top, finite_def, finite_def.trans
-/
theorem iff_fg {N : Submodule R M} : Module.Finite R N ↔ N.FG := finite_def.trans N.fg_top

/-- A finitely-generated submodule is finite as a module. -/
alias ⟨_, of_fg⟩ := iff_fg

/--
theorem `_root_.Submodule.FG.of_finite` / 定理 `_root_.Submodule.FG.of_finite`

English:
theorem _root_.Submodule.FG.of_finite
  given: {N : Submodule R M} [Module.Finite R N]
  statement: N.FG
  proof: iff_fg.mp ‹_›

中文:
定理 _root_.Submodule.FG.of_finite
  条件: {N : Submodule R M} [Module.Finite R N]
  结论: N.FG
  证明: iff_fg.mp ‹_›

Depends on / 依赖: iff_fg, iff_fg.mp
-/
theorem _root_.Submodule.FG.of_finite {N : Submodule R M} [Module.Finite R N] : N.FG :=
  iff_fg.mp ‹_›

variable (R M)

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : Module.Finite R (⊥ : Submodule R M)
  body: .of_fg fg_bot

中文:
实例 bot
  签名: : Module.Finite R (⊥ : Submodule R M)
  定义体: .of_fg fg_bot

Depends on / 依赖: fg_bot, of_fg
-/
instance bot : Module.Finite R (⊥ : Submodule R M) := .of_fg fg_bot

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: [Module.Finite R M]
  body: .of_fg fg_top

中文:
实例 top
  签名: [Module.Finite R M]
  定义体: .of_fg fg_top

Depends on / 依赖: fg_top, of_fg
-/
instance top [Module.Finite R M] : Module.Finite R (⊤ : Submodule R M) := .of_fg fg_top

/--
Instance `top_left` / 实例 `top_left`

English:
instance top_left
  signature: [Module.Finite R M]
  body: have : RingHomSurjective (Subsemiring.topEquiv (R := R)).symm.toRingHom :=
    RingHomSurjective.instToRingHomRingEquiv Subsemiring.topEquiv.symm
  of_surjective (σ := (Subsemiring.topEquiv (R := R)).symm.toRingHom)
      ⟨⟨id, fun _ _ => rfl⟩, fun _ _ => rfl⟩ Function.surjective_id

中文:
实例 top_left
  签名: [Module.Finite R M]
  定义体: have : RingHomSurjective (Subsemiring.topEquiv (R := R)).symm.toRingHom :=
    RingHomSurjective.instToRingHomRingEquiv Subsemiring.topEquiv.symm
  of_surjective (σ := (Subsemiring.topEquiv (R := R)).symm.toRingHom)
      ⟨⟨id, fun _ _ => rfl⟩, fun _ _ => rfl⟩ Function.surjective_id

Depends on / 依赖: Function, Function.surjective_id, RingHomSurjective, RingHomSurjective.instToRingHomRingEquiv, Subsemiring, Subsemiring.topEquiv, Subsemiring.topEquiv.symm, instToRingHomRingEquiv, of_surjective, surjective_id, symm.toRingHom, toRingHom, topEquiv
-/
instance top_left [Module.Finite R M] : Module.Finite (⊤ : Subsemiring R) M :=
  have : RingHomSurjective (Subsemiring.topEquiv (R := R)).symm.toRingHom :=
    RingHomSurjective.instToRingHomRingEquiv Subsemiring.topEquiv.symm
  of_surjective (σ := (Subsemiring.topEquiv (R := R)).symm.toRingHom)
      ⟨⟨id, fun _ _ => rfl⟩, fun _ _ => rfl⟩ Function.surjective_id

variable {M}

/--
theorem `span_of_finite` / 定理 `span_of_finite`

English:
theorem span_of_finite
  given: {A : Set M} (hA : Set.Finite A)
  statement: Module.Finite R (span R A)
  proof: of_fg ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩

中文:
定理 span_of_finite
  条件: {A : Set M} (hA : Set.Finite A)
  结论: Module.Finite R (span R A)
  证明: of_fg ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩

Depends on / 依赖: coe_toFinset, hA.coe_toFinset.symm, hA.toFinset, of_fg, toFinset
-/
theorem span_of_finite {A : Set M} (hA : Set.Finite A) : Module.Finite R (span R A) :=
  of_fg ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩

/--
Instance `span_singleton` / 实例 `span_singleton`

English:
instance span_singleton
  signature: (x : M)
  body: span_of_finite R Set.finite_singleton _

中文:
实例 span_singleton
  签名: (x : M)
  定义体: span_of_finite R Set.finite_singleton _

Depends on / 依赖: Set.finite_singleton, finite_singleton, span_of_finite
-/
instance span_singleton (x : M) : Module.Finite R (R ∙ x) :=
span_of_finite R Set.finite_singleton _

/--
Instance `span_finset` / 实例 `span_finset`

English:
instance span_finset
  signature: (s : Finset M)
  body: of_fg ⟨s, rfl⟩

中文:
实例 span_finset
  签名: (s : Finset M)
  定义体: of_fg ⟨s, rfl⟩

Depends on / 依赖: of_fg
-/
instance span_finset (s : Finset M) : Module.Finite R (span R (s : Set M)) :=
  of_fg ⟨s, rfl⟩

variable {R}

section Algebra

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]

中文:
定理 trans
  结论: {R : 类型} (A M : 类型) [Semiring R] [Semiring A] [Module R A]
-/
theorem trans {R : Type*} (A M : Type*) [Semiring R] [Semiring A] [Module R A]
    [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] :
    forall [Module.Finite R A] [Module.Finite A M], Module.Finite R M
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨fg_def.mpr
      ⟨image2 (· • ·) (↑s : Set A) (↑t : Set M),
        Finite.image2 _ s.finite_toSet t.finite_toSet,
        by rw [image2_smul, span_smul_of_span_eq_top hs (↑t : Set M), ht, restrictScalars_top]⟩⟩

/--
lemma `of_equiv_equiv` / 引理 `of_equiv_equiv`

English:
lemma of_equiv_equiv
  statement: {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁]
  proof: by
  let := e₁.toRingHom.toAlgebra
  let := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  have : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x => by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r => by
        sim

中文:
引理 of_equiv_equiv
  结论: {A₁ B₁ A₂ B₂ : 类型} [CommSemiring A₁] [CommSemiring B₁]
  证明: by
  let := e₁.toRingHom.toAlgebra
  let := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  have : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x => by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r => by
        sim

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, algebraMap, algebraMap_toAlgebra, commutes, congr_fun, e.toLinearEquiv, he.symm, of_algebraMap_eq, of_restrictScalars_finite, symm.toRingHom, toAlgebra, toLinearEquiv, toRingHom, toRingHom.toAlgebra
-/
lemma of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommSemiring A₁] [CommSemiring B₁]
    [CommSemiring A₂] [Semiring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂)
    (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁))
    [Module.Finite A₁ B₁] : Module.Finite A₂ B₂ := by
  let := e₁.toRingHom.toAlgebra
  let := ((algebraMap A₁ B₁).comp e₁.symm.toRingHom).toAlgebra
  have : IsScalarTower A₁ A₂ B₁ := IsScalarTower.of_algebraMap_eq
    (fun x => by simp [RingHom.algebraMap_toAlgebra])
  let e : B₁ ≃ₐ[A₂] B₂ :=
    { e₂ with
      commutes' := fun r => by
        simpa [RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun he.symm (e₁.symm r) }
  have := of_restrictScalars_finite A₁ A₂ B₁
  exact equiv e.toLinearEquiv

end Algebra

end Finite

end Module

end ModuleAndAlgebra

namespace Submodule

open Module

variable {R V} [Ring R] [AddCommGroup V] [Module R V]

/--
Instance `finite_sup` / 实例 `finite_sup`

English:
instance finite_sup
  signature: (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
  body: by
  rw [Finite.iff_fg] at *
  exact .sup h₁ h₂

中文:
实例 finite_sup
  签名: (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
  定义体: by
  rw [Finite.iff_fg] at *
  exact .sup h₁ h₂

Depends on / 依赖: Finite, Finite.iff_fg, iff_fg
-/
instance finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
    [h₂ : Module.Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V) := by
  rw [Finite.iff_fg] at *
  exact .sup h₁ h₂

/--
Instance `finite_finset_sup` / 实例 `finite_finset_sup`

English:
instance finite_finset_sup
  signature: {ι : Type*} (s : Finset ι) (S : ι -> Submodule R V)
  body: by
  refine s.sup_induction (f := S) (p := fun i => Module.Finite R ↑i) (Module.Finite.bot R V) ?_
    inferInstance
  intro S₁ hS₁ S₂ hS₂
  exact finite_sup S₁ S₂

中文:
实例 finite_finset_sup
  签名: {ι : 类型} (s : Finset ι) (S : ι -> Submodule R V)
  定义体: by
  refine s.sup_induction (f := S) (p := fun i => Module.Finite R ↑i) (Module.Finite.bot R V) ?_
    inferInstance
  intro S₁ hS₁ S₂ hS₂
  exact finite_sup S₁ S₂

Depends on / 依赖: Finite, Module, Module.Finite, Module.Finite.bot, finite_sup, s.sup_induction, sup_induction
-/
instance finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι -> Submodule R V)
    [forall i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V) := by
  refine s.sup_induction (f := S) (p := fun i => Module.Finite R ↑i) (Module.Finite.bot R V) ?_
    inferInstance
  intro S₁ hS₁ S₂ hS₂
  exact finite_sup S₁ S₂

section RestrictScalars

variable {R : Type*} [Semiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {A : Type*} [Semiring A] [Module R A] [Module A M] [IsScalarTower R A M]
variable {S : Submodule A M}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FG.restrictScalars` / 定理 `FG.restrictScalars`

English:
theorem FG.restrictScalars
  given: [Module.Finite R A] (hS : S.FG)
  statement: (S.restrictScalars R).FG
  proof: by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans A S

@[simp]

中文:
定理 FG.restrictScalars
  条件: [Module.Finite R A] (hS : S.FG)
  结论: (S.restrictScalars R).FG
  证明: by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans A S

@[simp]

Depends on / 依赖: Finite, Module, Module.Finite.iff_fg, Module.Finite.trans, MonoidalCategory, MonoidalCategory.tensorHom_def, iff_fg, tensorHom_def
-/
theorem FG.restrictScalars [Module.Finite R A] (hS : S.FG) : (S.restrictScalars R).FG := by
  rw [← Module.Finite.iff_fg] at *
  exact Module.Finite.trans A S

@[simp]
/--
theorem `FG.restrictScalars_iff` / 定理 `FG.restrictScalars_iff`

English:
theorem FG.restrictScalars_iff
  given: [Module.Finite R A]
  statement: (S.restrictScalars R).FG ↔ S.FG
  proof: ⟨of_restrictScalars R, restrictScalars⟩

中文:
定理 FG.restrictScalars_iff
  条件: [Module.Finite R A]
  结论: (S.restrictScalars R).FG ↔ S.FG
  证明: ⟨of_restrictScalars R, restrictScalars⟩

Depends on / 依赖: of_restrictScalars, restrictScalars
-/
theorem FG.restrictScalars_iff [Module.Finite R A] : (S.restrictScalars R).FG ↔ S.FG :=
  ⟨of_restrictScalars R, restrictScalars⟩

/--
theorem `FG.span` / 定理 `FG.span`

English:
theorem FG.span
  given: {S : Submodule R M} (hS : S.FG)
  statement: (span A (S : Set M)).FG
  proof: by
  obtain ⟨t, ht⟩ := hS
  use t
  rw [← ht]; rw [Submodule.span_span_of_tower]

中文:
定理 FG.span
  条件: {S : Submodule R M} (hS : S.FG)
  结论: (span A (S : Set M)).FG
  证明: by
  obtain ⟨t, ht⟩ := hS
  use t
  rw [← ht]; rw [Submodule.span_span_of_tower]
-/
protected theorem FG.span {S : Submodule R M} (hS : S.FG) : (span A (S : Set M)).FG := by
  obtain ⟨t, ht⟩ := hS
  use t
  rw [← ht]; rw [Submodule.span_span_of_tower]

end RestrictScalars

end Submodule

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

namespace Finite

variable (A) in
/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: Finite (RingHom.id A)
  proof: Module.Finite.self A

中文:
定理 id
  结论: Finite (RingHom.id A)
  证明: Module.Finite.self A

Depends on / 依赖: Finite, Module, Module.Finite.self
-/
theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->+* B) (hf : Surjective f)
  statement: f.Finite
  proof: letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf

中文:
定理 of_surjective
  条件: (f : A ->+* B) (hf : Surjective f)
  结论: f.Finite
  证明: letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf

Depends on / 依赖: Algebra, Algebra.linearMap, Finite, Module, Module.Finite.of_surjective, f.toAlgebra, linearMap, of_surjective, toAlgebra
-/
theorem of_surjective (f : A ->+* B) (hf : Surjective f) : f.Finite :=
  letI := f.toAlgebra
  Module.Finite.of_surjective (Algebra.linearMap A B) hf

/--
lemma `_root_.RingEquiv.finite` / 引理 `_root_.RingEquiv.finite`

English:
lemma _root_.RingEquiv.finite
  given: (e : A ≃+* B)
  statement: e.toRingHom.Finite
  proof: .of_surjective _ e.surjective

中文:
引理 _root_.RingEquiv.finite
  条件: (e : A ≃+* B)
  结论: e.toRingHom.Finite
  证明: .of_surjective _ e.surjective

Depends on / 依赖: e.surjective, of_surjective, surjective
-/
lemma _root_.RingEquiv.finite (e : A ≃+* B) : e.toRingHom.Finite :=
  .of_surjective _ e.surjective

instance (h : A ≃+* B) : letI := h.toRingHom.toAlgebra; Module.Finite A B :=
  h.finite

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) (hf : f.Finite)
  statement: (g.comp f).Finite
  proof: by
  algebraize [f, g, g.comp f]
  exact .trans B C

中文:
定理 comp
  条件: {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) (hf : f.Finite)
  结论: (g.comp f).Finite
  证明: by
  algebraize [f, g, g.comp f]
  exact .trans B C

Depends on / 依赖: algebraize, g.comp
-/
theorem comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
  algebraize [f, g, g.comp f]
  exact .trans B C

/--
theorem `of_comp_finite` / 定理 `of_comp_finite`

English:
theorem of_comp_finite
  given: {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).Finite)
  statement: g.Finite
  proof: by
  algebraize [f, g, g.comp f]
  exact .of_restrictScalars_finite A B C

中文:
定理 of_comp_finite
  条件: {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).Finite)
  结论: g.Finite
  证明: by
  algebraize [f, g, g.comp f]
  exact .of_restrictScalars_finite A B C

Depends on / 依赖: algebraize, g.comp, of_restrictScalars_finite
-/
theorem of_comp_finite {f : A ->+* B} {g : B ->+* C} (h : (g.comp f).Finite) : g.Finite := by
  algebraize [f, g, g.comp f]
  exact .of_restrictScalars_finite A B C

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

namespace Finite

variable (R A)

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: Finite (AlgHom.id R A)
  proof: RingHom.Finite.id A

中文:
定理 id
  结论: Finite (AlgHom.id R A)
  证明: RingHom.Finite.id A

Depends on / 依赖: Finite, RingHom, RingHom.Finite.id
-/
theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A

variable {R A}

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.Finite) (hf : f.Finite)
  statement: (g.comp f).Finite
  proof: RingHom.Finite.comp hg hf

中文:
定理 comp
  条件: {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.Finite) (hf : f.Finite)
  结论: (g.comp f).Finite
  证明: RingHom.Finite.comp hg hf

Depends on / 依赖: Finite, RingHom, RingHom.Finite.comp
-/
theorem comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf

/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: (f : A ->ₐ[R] B) (hf : Surjective f)
  statement: f.Finite
  proof: RingHom.Finite.of_surjective f.toRingHom hf

中文:
定理 of_surjective
  条件: (f : A ->ₐ[R] B) (hf : Surjective f)
  结论: f.Finite
  证明: RingHom.Finite.of_surjective f.toRingHom hf

Depends on / 依赖: Finite, RingHom, RingHom.Finite.of_surjective, f.toRingHom, of_surjective, toRingHom
-/
theorem of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.of_surjective f.toRingHom hf

/--
theorem `of_comp_finite` / 定理 `of_comp_finite`

English:
theorem of_comp_finite
  given: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).Finite)
  statement: g.Finite
  proof: RingHom.Finite.of_comp_finite h

中文:
定理 of_comp_finite
  条件: {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).Finite)
  结论: g.Finite
  证明: RingHom.Finite.of_comp_finite h

Depends on / 依赖: Finite, RingHom, RingHom.Finite.of_comp_finite, of_comp_finite
-/
theorem of_comp_finite {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.of_comp_finite h

end Finite

end AlgHom

section Ring
variable {R E : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]

local notation3 "R>=0" => {c : R // 0 <= c}

/--
Instance `instModuleFiniteAux` / 实例 `instModuleFiniteAux`

English:
instance instModuleFiniteAux
  signature: : Module.Finite R>=0 R
  body: by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x => ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := R) (.span R>=0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smu

中文:
实例 instModuleFiniteAux
  签名: : Module.Finite R>=0 R
  定义体: by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x => ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := R) (.span R>=0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smu
-/
private instance instModuleFiniteAux : Module.Finite R>=0 R := by
  simp_rw [Module.finite_def, Submodule.fg_def, Submodule.eq_top_iff']
  refine ⟨{1, -1}, by simp, fun x => ?_⟩
  obtain hx | hx := le_total 0 x
  · simpa using Submodule.smul_mem (M := R) (.span R>=0 {1, -1}) ⟨x, hx⟩ (x := 1)
      (Submodule.subset_span <| by simp)
  · simpa using Submodule.smul_mem (M := R) (.span R>=0 {1, -1}) ⟨-x, neg_nonneg.mpr hx⟩ (x := -1)
      (Submodule.subset_span <| by simp)

/--
Instance `instModuleFinite` / 实例 `instModuleFinite`

English:
instance instModuleFinite
  signature: [Module.Finite R E]
  body: .trans R E

中文:
实例 instModuleFinite
  签名: [Module.Finite R E]
  定义体: .trans R E
-/
instance instModuleFinite [Module.Finite R E] : Module.Finite R>=0 E := .trans R E

end Ring
