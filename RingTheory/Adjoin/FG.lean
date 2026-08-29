/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `FG (S : Subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
  as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

@[expose] public section


universe u v w

open Subsemiring Ring Submodule

open scoped Pointwise

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [Algebra R A]
  {s t : Set A}

/--
theorem `fg_trans` / 定理 `fg_trans`

English:
theorem fg_trans
  given: (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).toSubmodule.FG)
  proof: by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm ?_ ?_⟩
  · rw [span_le, Set.mul_subset_iff]
    intro x hx y hy
    change x * y in adjoin R (s union t)
    refine Subalgebra.mul_mem _ ?_ ?_
    · have : x in Subalgebr

中文:
定理 fg_trans
  条件: (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).toSubmodule.FG)
  证明: by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm ?_ ?_⟩
  · rw [span_le, Set.mul_subset_iff]
    intro x hx y hy
    change x * y in adjoin R (s union t)
    refine Subalgebra.mul_mem _ ?_ ?_
    · have : x in Subalgebr

Depends on / 依赖: Set.mul_subset_iff, Set.subset_union_left, Subalgebra, Subalgebra.mul_mem, Subalgebra.toSubmodule, adjoin, adjoin_mono, fg_def, hp.mul, le_antisymm, mul_mem, mul_subset_iff, span_le, subset_span, subset_union_left, toSubmodule
-/
theorem fg_trans (h1 : (adjoin R s).toSubmodule.FG) (h2 : (adjoin (adjoin R s) t).toSubmodule.FG) :
    (adjoin R (s union t)).toSubmodule.FG := by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm ?_ ?_⟩
  · rw [span_le, Set.mul_subset_iff]
    intro x hx y hy
    change x * y in adjoin R (s union t)
    refine Subalgebra.mul_mem _ ?_ ?_
    · have : x in Subalgebra.toSubmodule (adjoin R s) := by
        rw [← hp']
        exact subset_span hx
      exact adjoin_mono Set.subset_union_left this
    have : y in Subalgebra.toSubmodule (adjoin (adjoin R s) t) := by
      rw [← hq']
      exact subset_span hy
    change y in adjoin R (s union t)
    rwa [adjoin_union_eq_adjoin_adjoin]
  · intro r hr
    change r in adjoin R (s union t) at hr
    rw [adjoin_union_eq_adjoin_adjoin] at hr
    change r in Subalgebra.toSubmodule (adjoin (adjoin R s) t) at hr
    rw [← hq']; rw [← Set.image_id q]; rw [Finsupp.mem_span_image_iff_linearCombination (adjoin R s)] at hr
    rcases hr with ⟨l, hlq, rfl⟩
    have := @Finsupp.linearCombination_apply A A (adjoin R s)
    rw [this]; rw [Finsupp.sum]
    refine sum_mem ?_
    intro z hz
    change (l z).1 * _ in _
    have : (l z).1 in Subalgebra.toSubmodule (adjoin R s) := (l z).2
    rw [← hp']; rw [← Set.image_id p]; rw [Finsupp.mem_span_image_iff_linearCombination R] at this
    rcases this with ⟨l2, hlp, hl⟩
    have := @Finsupp.linearCombination_apply A A R
    rw [this] at hl
    rw [← hl]; rw [Finsupp.sum_mul]
    refine sum_mem ?_
    intro t ht
    change _ * _ in _
    rw [smul_mul_assoc]
    refine smul_mem _ _ ?_
    exact subset_span ⟨t, hlp ht, z, hlq hz, rfl⟩

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
Definition of `FG` / `FG` 的定义

English:
definition FG
  signature: (S : Subalgebra R A)
  body: exists t : Finset A, Algebra.adjoin R ↑t = S

中文:
定义 FG
  签名: (S : 子代数 R A)
  定义体: exists t : Finset A, Algebra.adjoin R ↑t = S

Depends on / 依赖: Algebra, Algebra.adjoin, Finset, adjoin
-/
def FG (S : Subalgebra R A) : Prop :=
  exists t : Finset A, Algebra.adjoin R ↑t = S

/--
theorem `fg_adjoin_finset` / 定理 `fg_adjoin_finset`

English:
theorem fg_adjoin_finset
  given: (s : Finset A)
  statement: (Algebra.adjoin R (↑s : Set A)).FG
  proof: ⟨s, rfl⟩

中文:
定理 fg_adjoin_finset
  条件: (s : 有限集 A)
  结论: (代数.adjoin R (↑s : 集合 A)).FG
  证明: ⟨s, rfl⟩
-/
theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).FG :=
  ⟨s, rfl⟩

/--
theorem `fg_def` / 定理 `fg_def`

English:
theorem fg_def
  given: {S : Subalgebra R A}
  statement: S.FG ↔ exists t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S
  proof: Iff.symm Set.exists_finite_iff_finset

中文:
定理 fg_def
  条件: {S : 子代数 R A}
  结论: S.FG ↔ 存在 t : 集合 A, 集合.有限 t ∧ 代数.adjoin R t = S
  证明: Iff.symm Set.exists_finite_iff_finset

Depends on / 依赖: Iff.symm, Set.exists_finite_iff_finset, exists_finite_iff_finset
-/
theorem fg_def {S : Subalgebra R A} : S.FG ↔ exists t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset

/--
theorem `fg_bot` / 定理 `fg_bot`

English:
theorem fg_bot
  statement: (⊥ : Subalgebra R A).FG
  proof: ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩

中文:
定理 fg_bot
  结论: (⊥ : 子代数 R A).FG
  证明: ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩

Depends on / 依赖: Algebra, Algebra.adjoin_empty, Finset, Finset.coe_empty, adjoin_empty, coe_empty
-/
theorem fg_bot : (⊥ : Subalgebra R A).FG :=
  ⟨∅, Finset.coe_empty ▸ Algebra.adjoin_empty R A⟩

/--
theorem `fg_of_fg_toSubmodule` / 定理 `fg_of_fg_toSubmodule`

English:
theorem fg_of_fg_toSubmodule
  given: {S : Subalgebra R A}
  statement: S.toSubmodule.FG -> S.FG
  proof: fun ⟨t, ht⟩ => ⟨t, le_antisymm
(Algebra.adjoin_le fun x hx => show x in Subalgebra.toSubmodule S from ht ▸ subset_span hx)
    show Subalgebra.toSubmodule S <= Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx =>
      span_le.mpr (fun _ hx => Algebra.subset_adjoin hx)
        (show x in sp

中文:
定理 fg_of_fg_toSubmodule
  条件: {S : 子代数 R A}
  结论: S.toSubmodule.FG -> S.FG
  证明: fun ⟨t, ht⟩ => ⟨t, le_antisymm
(Algebra.adjoin_le fun x hx => show x in Subalgebra.toSubmodule S from ht ▸ subset_span hx)
    show Subalgebra.toSubmodule S <= Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx =>
      span_le.mpr (fun _ hx => Algebra.subset_adjoin hx)
        (show x in sp

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.adjoin_le, Algebra.subset_adjoin, Subalgebra, Subalgebra.toSubmodule, adjoin, adjoin_le, le_antisymm, span_le, span_le.mpr, subset_adjoin, subset_span, toSubmodule
-/
theorem fg_of_fg_toSubmodule {S : Subalgebra R A} : S.toSubmodule.FG -> S.FG :=
  fun ⟨t, ht⟩ => ⟨t, le_antisymm
(Algebra.adjoin_le fun x hx => show x in Subalgebra.toSubmodule S from ht ▸ subset_span hx)
    show Subalgebra.toSubmodule S <= Subalgebra.toSubmodule (Algebra.adjoin R ↑t) from fun x hx =>
      span_le.mpr (fun _ hx => Algebra.subset_adjoin hx)
        (show x in span R ↑t by
          rw [ht]
          exact hx)⟩

/--
theorem `fg_of_noetherian` / 定理 `fg_of_noetherian`

English:
theorem fg_of_noetherian
  given: [IsNoetherian R A] (S : Subalgebra R A)
  statement: S.FG
  proof: fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))

中文:
定理 fg_of_noetherian
  条件: [是Noether R A] (S : 子代数 R A)
  结论: S.FG
  证明: fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, Subalgebra, Subalgebra.toSubmodule, fg_of_fg_toSubmodule, noetherian, toSubmodule
-/
theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.FG :=
  fg_of_fg_toSubmodule (IsNoetherian.noetherian (Subalgebra.toSubmodule S))

/--
theorem `fg_of_submodule_fg` / 定理 `fg_of_submodule_fg`

English:
theorem fg_of_submodule_fg
  given: (h : (⊤ : Submodule R A).FG)
  statement: (⊤ : Subalgebra R A).FG
  proof: let ⟨s, hs⟩ := h
⟨s, toSubmodule.injective by
    rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← hs]; rw [span_le]
    exact Algebra.subset_adjoin⟩

中文:
定理 fg_of_submodule_fg
  条件: (h : (⊤ : 子模 R A).FG)
  结论: (⊤ : 子代数 R A).FG
  证明: let ⟨s, hs⟩ := h
⟨s, toSubmodule.injective by
    rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← hs]; rw [span_le]
    exact Algebra.subset_adjoin⟩

Depends on / 依赖: Algebra, Algebra.subset_adjoin, Algebra.top_toSubmodule, eq_top_iff, injective, span_le, subset_adjoin, toSubmodule, toSubmodule.injective, top_toSubmodule
-/
theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := h
⟨s, toSubmodule.injective by
    rw [Algebra.top_toSubmodule]; rw [eq_top_iff]; rw [← hs]; rw [span_le]
    exact Algebra.subset_adjoin⟩

/--
theorem `FG.prod` / 定理 `FG.prod`

English:
theorem FG.prod
  given: {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.FG) (hT : T.FG)
  proof: by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2]; rw [← ht.2]
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finit

中文:
定理 FG.乘积
  条件: {S : 子代数 R A} {T : 子代数 R B} (hS : S.FG) (hT : T.FG)
  证明: by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2]; rw [← ht.2]
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finit

Depends on / 依赖: Algebra, Algebra.adjoin_inl_union_inr_eq_prod, Finite, LinearMap, LinearMap.inl, LinearMap.inr, Set.Finite.image, Set.Finite.union, Set.finite_singleton, adjoin_inl_union_inr_eq_prod, fg_def, finite_singleton
-/
theorem FG.prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.FG) (hT : T.FG) :
    (S.prod T).FG := by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2]; rw [← ht.2]
  exact fg_def.2 ⟨LinearMap.inl R A B '' (s union {1}) union LinearMap.inr R A B '' (t union {1}),
    Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
      (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
    Algebra.adjoin_inl_union_inr_eq_prod R s t⟩

section

/--
theorem `FG.map` / 定理 `FG.map`

English:
theorem FG.map
  given: {S : Subalgebra R A} (f : A ->ₐ[R] B) (hs : S.FG)
  statement: (S.map f).FG
  proof: by
  let ⟨s, hs⟩ := hs
  classical
  exact ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

中文:
定理 FG.map
  条件: {S : 子代数 R A} (f : A ->ₐ[R] B) (hs : S.FG)
  结论: (S.map f).FG
  证明: by
  let ⟨s, hs⟩ := hs
  classical
  exact ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩
-/
theorem FG.map {S : Subalgebra R A} (f : A ->ₐ[R] B) (hs : S.FG) : (S.map f).FG := by
  let ⟨s, hs⟩ := hs
  classical
  exact ⟨s.image f, by rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fg_of_fg_map` / 定理 `fg_of_fg_map`

English:
theorem fg_of_fg_map
  statement: (S : Subalgebra R A) (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h => hf h,
map_injective hf by
      rw [← Algebra.adjoin_image]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_of_subset]; rw [hs]
      rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_le_iff]; rw [hs]; rw [← Algebra.map_top]
      exact map_mono le

中文:
定理 fg_of_fg_map
  结论: (S : 子代数 R A) (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h => hf h,
map_injective hf by
      rw [← Algebra.adjoin_image]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_of_subset]; rw [hs]
      rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_le_iff]; rw [hs]; rw [← Algebra.map_top]
      exact map_mono le

Depends on / 依赖: AlgHom, AlgHom.coe_range, Algebra, Algebra.adjoin_image, Algebra.adjoin_le_iff, Algebra.map_top, Finset, Finset.coe_preimage, Set.image_preimage_eq_of_subset, adjoin_image, adjoin_le_iff, coe_preimage, coe_range, image_preimage_eq_of_subset, le_top, map_injective, map_mono, map_top, preimage, s.preimage
-/
theorem fg_of_fg_map (S : Subalgebra R A) (f : A ->ₐ[R] B) (hf : Function.Injective f)
    (hs : (S.map f).FG) : S.FG :=
  let ⟨s, hs⟩ := hs
  ⟨s.preimage f fun _ _ _ _ h => hf h,
map_injective hf by
      rw [← Algebra.adjoin_image]; rw [Finset.coe_preimage]; rw [Set.image_preimage_eq_of_subset]; rw [hs]
      rw [← AlgHom.coe_range]; rw [← Algebra.adjoin_le_iff]; rw [hs]; rw [← Algebra.map_top]
      exact map_mono le_top⟩

/--
theorem `fg_top` / 定理 `fg_top`

English:
theorem fg_top
  given: (S : Subalgebra R A)
  statement: (⊤ : Subalgebra R S).FG ↔ S.FG
  proof: ⟨fun h => by
    rw [← S.range_val]; rw [← Algebra.map_top]
    exact FG.map _ h, fun h =>
fg_of_fg_map _ S.val Subtype.val_injective by
      rw [Algebra.map_top]; rw [range_val]
      exact h⟩

中文:
定理 fg_top
  条件: (S : 子代数 R A)
  结论: (⊤ : 子代数 R S).FG ↔ S.FG
  证明: ⟨fun h => by
    rw [← S.range_val]; rw [← Algebra.map_top]
    exact FG.map _ h, fun h =>
fg_of_fg_map _ S.val Subtype.val_injective by
      rw [Algebra.map_top]; rw [range_val]
      exact h⟩

Depends on / 依赖: Algebra, Algebra.map_top, FG.map, S.range_val, S.val, Subtype, Subtype.val_injective, fg_of_fg_map, map_top, range_val, val_injective
-/
theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).FG ↔ S.FG :=
  ⟨fun h => by
    rw [← S.range_val]; rw [← Algebra.map_top]
    exact FG.map _ h, fun h =>
fg_of_fg_map _ S.val Subtype.val_injective by
      rw [Algebra.map_top]; rw [range_val]
      exact h⟩

/--
theorem `induction_on_adjoin` / 定理 `induction_on_adjoin`

English:
theorem induction_on_adjoin
  statement: [IsNoetherian R A] (P : Subalgebra R A -> Prop) (base : P ⊥)
  proof: by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine Finset.induction_on t ?_ ?_
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h

中文:
定理 induction_on_adjoin
  结论: [是Noether R A] (P : 子代数 R A -> 命题) (base : P ⊥)
  证明: by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine Finset.induction_on t ?_ ?_
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h

Depends on / 依赖: Algebra, Algebra.adjoin_insert_adjoin, Finset, Finset.coe_insert, Finset.induction_on, S.fg_of_noetherian, adjoin_insert_adjoin, classical, coe_insert, fg_of_noetherian, induction_on
-/
theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A -> Prop) (base : P ⊥)
    (ih : forall (S : Subalgebra R A) (x : A), P S -> P (Algebra.adjoin R (insert x S)))
    (S : Subalgebra R A) : P S := by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine Finset.induction_on t ?_ ?_
  · simpa using base
  intro x t _ h
  rw [Finset.coe_insert]
  simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h

/--
theorem `FG.sup` / 定理 `FG.sup`

English:
theorem FG.sup
  given: {S S' : Subalgebra R A} (hS : Subalgebra.FG S) (hS' : Subalgebra.FG S')
  proof: let ⟨s, hs⟩ := Subalgebra.fg_def.1 hS
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hS'
  fg_def.mpr ⟨s union s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩

中文:
定理 FG.上确界
  条件: {S S' : 子代数 R A} (hS : 子代数.FG S) (hS' : 子代数.FG S')
  证明: let ⟨s, hs⟩ := Subalgebra.fg_def.1 hS
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hS'
  fg_def.mpr ⟨s union s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩
-/
theorem FG.sup {S S' : Subalgebra R A} (hS : Subalgebra.FG S) (hS' : Subalgebra.FG S') :
    Subalgebra.FG (S ⊔ S') :=
  let ⟨s, hs⟩ := Subalgebra.fg_def.1 hS
  let ⟨s', hs'⟩ := Subalgebra.fg_def.1 hS'
  fg_def.mpr ⟨s union s', Set.Finite.union hs.1 hs'.1,
    (by rw [Algebra.adjoin_union, hs.2, hs'.2])⟩

end Subalgebra

section Semiring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/--
Instance `AlgHom.isNoetherianRing_range` / 实例 `AlgHom.isNoetherianRing_range`

English:
instance AlgHom.isNoetherianRing_range
  signature: (f : A ->ₐ[R] B) [IsNoetherianRing A]
  body: _root_.isNoetherianRing_range f.toRingHom

中文:
实例 代数态射.isNoetherianRing_range
  签名: (f : A ->ₐ[R] B) [是Noether环 A]
  定义体: _root_.isNoetherianRing_range f.toRingHom

Depends on / 依赖: _root_, _root_.isNoetherianRing_range, f.toRingHom, isNoetherianRing_range, toRingHom
-/
instance AlgHom.isNoetherianRing_range (f : A ->ₐ[R] B) [IsNoetherianRing A] :
    IsNoetherianRing f.range :=
  _root_.isNoetherianRing_range f.toRingHom

end Semiring

section Ring

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/--
theorem `isNoetherianRing_of_fg` / 定理 `isNoetherianRing_of_fg`

English:
theorem isNoetherianRing_of_fg
  given: {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing R]
  proof: let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _

中文:
定理 isNoetherianRing_of_fg
  条件: {S : 子代数 R A} (HS : S.FG) [是Noether环 R]
  证明: let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _

Depends on / 依赖: AlgHom, AlgHom.isNoetherianRing_range, Algebra, Algebra.adjoin_eq_range, adjoin_eq_range, isNoetherianRing_range
-/
theorem isNoetherianRing_of_fg {S : Subalgebra R A} (HS : S.FG) [IsNoetherianRing R] :
    IsNoetherianRing S :=
  let ⟨t, ht⟩ := HS
  ht ▸ (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ AlgHom.isNoetherianRing_range _

/--
theorem `is_noetherian_subring_closure` / 定理 `is_noetherian_subring_closure`

English:
theorem is_noetherian_subring_closure
  given: (s : Set R) (hs : s.Finite)
  proof: show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

中文:
定理 is_noetherian_subring_closure
  条件: (s : 集合 R) (hs : s.有限)
  证明: show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

Depends on / 依赖: Algebra, Algebra.adjoin_int, IsNoetherianRing, Subalgebra, Subalgebra.fg_def, Subring, Subring.closure, adjoin_int, closure, fg_def, isNoetherianRing_of_fg, subalgebraOfSubring
-/
theorem is_noetherian_subring_closure (s : Set R) (hs : s.Finite) :
    IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end Ring
