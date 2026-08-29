/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!

# The rank nullity theorem

In this file we provide the rank nullity theorem as a typeclass, and prove various corollaries
of the theorem. The main definition is `HasRankNullity.{u} R`, which states that
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

The following instances are provided in mathlib:
1. `DivisionRing.hasRankNullity` for division rings in
   `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`.
2. `IsDomain.hasRankNullity` for commutative domains in
   `Mathlib/LinearAlgebra/Dimension/Localization.lean`.

TODO: prove the rank-nullity theorem for `[Ring R] [IsDomain R] [StrongRankCondition R]`.
See `nonempty_oreSet_of_strongRankCondition` for a start.
-/

public section
universe u v

open Function Set Cardinal Module Submodule LinearMap

variable {R} {M M₁ M₂ M₃ : Type u} {M' : Type v} [Ring R]
variable [AddCommGroup M] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M']
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M']

/--
`HasRankNullity.{u}` is a class of rings satisfying
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

Usually such a ring satisfies `HasRankNullity.{w}` for all universes `w`, and the universe
argument is there because of technical limitations to universe polymorphism.

See `DivisionRing.hasRankNullity` and `IsDomain.hasRankNullity`.
-/
@[pp_with_univ]
/--
Definition of `HasRankNullity` / `HasRankNullity` 的定义

English:
class HasRankNullity
  parameters: (R : Type v) [inst : Ring R]
  axioms and operations (2):
    - exists_set_linearIndependent : forall (M : Type u) [AddCommGroup M] [Module R M], exists s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s
    - rank_quotient_add_rank : forall {M : Type u} [AddCommGroup M] [Module R M] (N : Submodule R M), Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M

中文:
类 有RankNullity
  参数: (R : 类型v) [inst : 环 R]
  公理与运算 (2 个):
    - exists_set_linearIndependent : 对任意 (M : 类型u) [加法交换群 M] [模 R M], 存在 s : 集合 M, #s = 模.rank R M ∧ LinearIndepOn R id s
    - rank_quotient_add_rank : 对任意 {M : 类型u} [加法交换群 M] [模 R M] (N : 子模 R M), 模.rank R (M ⧸ N) + 模.rank R N = 模.rank R M
-/
class HasRankNullity (R : Type v) [inst : Ring R] : Prop where
  exists_set_linearIndependent : forall (M : Type u) [AddCommGroup M] [Module R M],
    exists s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s
  rank_quotient_add_rank : forall {M : Type u} [AddCommGroup M] [Module R M] (N : Submodule R M),
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M

variable [HasRankNullity.{u} R]

/--
lemma `Submodule.rank_quotient_add_rank` / 引理 `Submodule.rank_quotient_add_rank`

English:
lemma Submodule.rank_quotient_add_rank
  given: (N : Submodule R M)
  proof: HasRankNullity.rank_quotient_add_rank N

中文:
引理 子模.rank_quotient_add_rank
  条件: (N : 子模 R M)
  证明: HasRankNullity.rank_quotient_add_rank N

Depends on / 依赖: HasRankNullity, HasRankNullity.rank_quotient_add_rank, rank_quotient_add_rank
-/
lemma Submodule.rank_quotient_add_rank (N : Submodule R M) :
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M :=
  HasRankNullity.rank_quotient_add_rank N

variable (R M) in
/--
lemma `exists_set_linearIndependent` / 引理 `exists_set_linearIndependent`

English:
lemma exists_set_linearIndependent
  proof: HasRankNullity.exists_set_linearIndependent M

中文:
引理 存在_set_linearIndependent
  证明: HasRankNullity.exists_set_linearIndependent M

Depends on / 依赖: Subtype, Subtype.val
-/
lemma exists_set_linearIndependent :
    exists s : Set M, #s = Module.rank R M ∧ LinearIndependent (ι := s) R Subtype.val :=
  HasRankNullity.exists_set_linearIndependent M

variable (R) in
/--
theorem `nontrivial_of_hasRankNullity` / 定理 `nontrivial_of_hasRankNullity`

English:
theorem nontrivial_of_hasRankNullity
  statement: Nontrivial R
  proof: by
  refine (subsingleton_or_nontrivial R).resolve_left fun H => ?_
  have := rank_quotient_add_rank (R := R) (M := PUnit) ⊥
  simp [one_add_one_eq_two] at this

中文:
定理 nontrivial_of_hasRankNullity
  结论: 非平凡 R
  证明: by
  refine (subsingleton_or_nontrivial R).resolve_left fun H => ?_
  have := rank_quotient_add_rank (R := R) (M := PUnit) ⊥
  simp [one_add_one_eq_two] at this

Depends on / 依赖: one_add_one_eq_two, rank_quotient_add_rank, resolve_left, subsingleton_or_nontrivial
-/
theorem nontrivial_of_hasRankNullity : Nontrivial R := by
  refine (subsingleton_or_nontrivial R).resolve_left fun H => ?_
  have := rank_quotient_add_rank (R := R) (M := PUnit) ⊥
  simp [one_add_one_eq_two] at this

attribute [local instance] nontrivial_of_hasRankNullity

/--
theorem `LinearMap.lift_rank_range_add_rank_ker` / 定理 `LinearMap.lift_rank_range_add_rank_ker`

English:
theorem LinearMap.lift_rank_range_add_rank_ker
  given: (f : M ->ₗ[R] M')
  proof: by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.lift_rank_eq]; rw [← lift_add]; rw [rank_quotient_add_rank]

中文:
定理 线性映射.lift_rank_range_add_rank_ker
  条件: (f : M ->ₗ[R] M')
  证明: by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.lift_rank_eq]; rw [← lift_add]; rw [rank_quotient_add_rank]

Depends on / 依赖: Classical, Classical.decEq, Submodule, f.quotKerEquivRange.lift_rank_eq, lift_add, lift_rank_eq, quotKerEquivRange, rank_quotient_add_rank
-/
theorem LinearMap.lift_rank_range_add_rank_ker (f : M ->ₗ[R] M') :
    lift.{u} (Module.rank R (LinearMap.range f)) + lift.{v} (Module.rank R (LinearMap.ker f)) =
      lift.{v} (Module.rank R M) := by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.lift_rank_eq]; rw [← lift_add]; rw [rank_quotient_add_rank]

/--
theorem `LinearMap.rank_range_add_rank_ker` / 定理 `LinearMap.rank_range_add_rank_ker`

English:
theorem LinearMap.rank_range_add_rank_ker
  given: (f : M ->ₗ[R] M₁)
  proof: by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq]; rw [rank_quotient_add_rank]

中文:
定理 线性映射.rank_range_add_rank_ker
  条件: (f : M ->ₗ[R] M₁)
  证明: by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq]; rw [rank_quotient_add_rank]

Depends on / 依赖: Classical, Classical.decEq, Submodule, f.quotKerEquivRange.rank_eq, quotKerEquivRange, rank_eq, rank_quotient_add_rank
-/
theorem LinearMap.rank_range_add_rank_ker (f : M ->ₗ[R] M₁) :
    Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M := by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq]; rw [rank_quotient_add_rank]

/--
theorem `LinearMap.lift_rank_eq_of_surjective` / 定理 `LinearMap.lift_rank_eq_of_surjective`

English:
theorem LinearMap.lift_rank_eq_of_surjective
  given: {f : M ->ₗ[R] M'} (h : Surjective f)
  proof: by
  rw [← lift_rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

中文:
定理 线性映射.lift_rank_eq_of_surjective
  条件: {f : M ->ₗ[R] M'} (h : 满射 f)
  证明: by
  rw [← lift_rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

Depends on / 依赖: lift_rank_range_add_rank_ker, rank_range_of_surjective
-/
theorem LinearMap.lift_rank_eq_of_surjective {f : M ->ₗ[R] M'} (h : Surjective f) :
    lift.{v} (Module.rank R M) =
      lift.{u} (Module.rank R M') + lift.{v} (Module.rank R (LinearMap.ker f)) := by
  rw [← lift_rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

/--
theorem `LinearMap.rank_eq_of_surjective` / 定理 `LinearMap.rank_eq_of_surjective`

English:
theorem LinearMap.rank_eq_of_surjective
  given: {f : M ->ₗ[R] M₁} (h : Surjective f)
  proof: by
  rw [← rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

中文:
定理 线性映射.rank_eq_of_surjective
  条件: {f : M ->ₗ[R] M₁} (h : 满射 f)
  证明: by
  rw [← rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

Depends on / 依赖: rank_range_add_rank_ker, rank_range_of_surjective
-/
theorem LinearMap.rank_eq_of_surjective {f : M ->ₗ[R] M₁} (h : Surjective f) :
    Module.rank R M = Module.rank R M₁ + Module.rank R (LinearMap.ker f) := by
  rw [← rank_range_add_rank_ker f]; rw [← rank_range_of_surjective f h]

/--
theorem `LinearMap.lift_rank_comap_le` / 定理 `LinearMap.lift_rank_comap_le`

English:
theorem LinearMap.lift_rank_comap_le
  given: {f : M ->ₗ[R] M'} (p : Submodule R M')
  proof: by
  let f' : comap f p ->ₗ[R] p := f.restrict (by aesop)
  have hk : Module.rank R f'.ker <= Module.rank R f.ker := by
    rw [← rank_map_eq (injective_subtype (comap f p))]
    exact rank_mono fun x hx => by aesop (add simp Subtype.ext_iff)
  have hr : Module.rank R f'.range <= Module.rank R p := 

中文:
定理 线性映射.lift_rank_comap_le
  条件: {f : M ->ₗ[R] M'} (p : 子模 R M')
  证明: by
  let f' : comap f p ->ₗ[R] p := f.restrict (by aesop)
  have hk : Module.rank R f'.ker <= Module.rank R f.ker := by
    rw [← rank_map_eq (injective_subtype (comap f p))]
    exact rank_mono fun x hx => by aesop (add simp Subtype.ext_iff)
  have hr : Module.rank R f'.range <= Module.rank R p := 

Depends on / 依赖: Module, Module.rank, Submodule, Submodule.rank_le, Subtype, Subtype.ext_iff, ext_iff, f.ker, f.restrict, injective_subtype, lift_le, lift_rank_range_add_rank_ker, rank_le, rank_map_eq, rank_mono, restrict
-/
theorem LinearMap.lift_rank_comap_le {f : M ->ₗ[R] M'} (p : Submodule R M') :
    lift.{v} (Module.rank R (comap f p)) <=
      lift.{u} (Module.rank R p) + lift.{v} (Module.rank R f.ker) := by
  let f' : comap f p ->ₗ[R] p := f.restrict (by aesop)
  have hk : Module.rank R f'.ker <= Module.rank R f.ker := by
    rw [← rank_map_eq (injective_subtype (comap f p))]
    exact rank_mono fun x hx => by aesop (add simp Subtype.ext_iff)
  have hr : Module.rank R f'.range <= Module.rank R p := by grw [Submodule.rank_le f'.range]
  rw [← f'.lift_rank_range_add_rank_ker]
  gcongr <;> rwa [lift_le]

omit [HasRankNullity.{u} R] in
/--
lemma `LinearMap.rank_quot_submodule_map_eq` / 引理 `LinearMap.rank_quot_submodule_map_eq`

English:
lemma LinearMap.rank_quot_submodule_map_eq
  statement: [HasRankNullity.{v} R]
  proof: by
  let f' : M' ⧸ map f p ->ₗ[R] M' ⧸ f.range := factor map_le_range
  let +nondep e : (f.range ⧸ map f.rangeRestrict p) ≃ₗ[R] f'.ker := by
    let g : f.range ->ₗ[R] f'.ker :=
      (LinearEquiv.ofEq (map (map f p).mkQ f.range) f'.ker) (by rw [ker_mapQ]; rfl) ∘ₗ
        (map f p).mkQ.submoduleMap 

中文:
引理 线性映射.rank_quot_submodule_map_eq
  结论: [有RankNullity.{v} R]
  证明: by
  let f' : M' ⧸ map f p ->ₗ[R] M' ⧸ f.range := factor map_le_range
  let +nondep e : (f.range ⧸ map f.rangeRestrict p) ≃ₗ[R] f'.ker := by
    let g : f.range ->ₗ[R] f'.ker :=
      (LinearEquiv.ofEq (map (map f p).mkQ f.range) f'.ker) (by rw [ker_mapQ]; rfl) ∘ₗ
        (map f p).mkQ.submoduleMap 

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, Surjective, f.range, f.rangeRestrict, factor, fun_prop, g.ker, g.quotK, g_ker, g_surj, ker_mapQ, ker_restrict, map_codRestrict, map_le_range, mkQ.submoduleMap, nondep, rangeRestrict, submoduleMap, submoduleMap_surjective
-/
lemma LinearMap.rank_quot_submodule_map_eq [HasRankNullity.{v} R]
    {f : M ->ₗ[R] M'} (p : Submodule R M) :
    Module.rank R (M' ⧸ map f p) =
      Module.rank R (M' ⧸ f.range) + Module.rank R (f.range ⧸ map f.rangeRestrict p) := by
  let f' : M' ⧸ map f p ->ₗ[R] M' ⧸ f.range := factor map_le_range
  let +nondep e : (f.range ⧸ map f.rangeRestrict p) ≃ₗ[R] f'.ker := by
    let g : f.range ->ₗ[R] f'.ker :=
      (LinearEquiv.ofEq (map (map f p).mkQ f.range) f'.ker) (by rw [ker_mapQ]; rfl) ∘ₗ
        (map f p).mkQ.submoduleMap f.range
    have g_surj : Surjective g := by simpa [g] using submoduleMap_surjective (map f p).mkQ f.range
    have g_ker : g.ker = map f.rangeRestrict p := by
      simp [g, submoduleMap, ker_restrict, map_codRestrict]
    let e := g.quotKerEquivOfSurjective g_surj
    rwa [g_ker] at e
have := f'.rank_eq_of_surjective factor_surjective map_le_range
  rwa [← e.rank_eq] at this

omit [HasRankNullity.{u} R] in
/--
theorem `LinearMap.lift_rank_quot_map_le` / 定理 `LinearMap.lift_rank_quot_map_le`

English:
theorem LinearMap.lift_rank_quot_map_le
  statement: [HasRankNullity.{v} R]
  proof: by
  rw [rank_quot_submodule_map_eq]; rw [lift_add]; gcongr
  let f' : M ⧸ p ->ₗ[R] f.range ⧸ map f.rangeRestrict p :=
mapQ p (map f.rangeRestrict p) f.rangeRestrict by rw [comap_map_eq]; exact le_sup_left
exact lift_rank_le_of_surjective f' by rw [← range_eq_top, range_mapQ]; simp

中文:
定理 线性映射.lift_rank_quot_map_le
  结论: [有RankNullity.{v} R]
  证明: by
  rw [rank_quot_submodule_map_eq]; rw [lift_add]; gcongr
  let f' : M ⧸ p ->ₗ[R] f.range ⧸ map f.rangeRestrict p :=
mapQ p (map f.rangeRestrict p) f.rangeRestrict by rw [comap_map_eq]; exact le_sup_left
exact lift_rank_le_of_surjective f' by rw [← range_eq_top, range_mapQ]; simp

Depends on / 依赖: comap_map_eq, f.range, f.rangeRestrict, le_sup_left, lift_add, lift_rank_le_of_surjective, rangeRestrict, range_eq_top, range_mapQ, rank_quot_submodule_map_eq
-/
theorem LinearMap.lift_rank_quot_map_le [HasRankNullity.{v} R]
    {f : M ->ₗ[R] M'} (p : Submodule R M) :
    lift.{u} (Module.rank R (M' ⧸ map f p)) <=
      lift.{u} (Module.rank R (M' ⧸ f.range)) + lift.{v} (Module.rank R (M ⧸ p)) := by
  rw [rank_quot_submodule_map_eq]; rw [lift_add]; gcongr
  let f' : M ⧸ p ->ₗ[R] f.range ⧸ map f.rangeRestrict p :=
mapQ p (map f.rangeRestrict p) f.rangeRestrict by rw [comap_map_eq]; exact le_sup_left
exact lift_rank_le_of_surjective f' by rw [← range_eq_top, range_mapQ]; simp

/--
theorem `exists_linearIndepOn_of_lt_rank` / 定理 `exists_linearIndepOn_of_lt_rank`

English:
theorem exists_linearIndepOn_of_lt_rank
  statement: [StrongRankCondition R]
  proof: by
  obtain ⟨t, ht, ht'⟩ := exists_set_linearIndependent R (M ⧸ Submodule.span R s)
  choose sec hsec using Submodule.mkQ_surjective (Submodule.span R s)
  have hsec' : (Submodule.mkQ _) ∘ sec = _root_.id := funext hsec
  have hst : Disjoint s (sec '' t) := by
    rw [Set.disjoint_iff]
    rintro _ 

中文:
定理 存在_linearIndepOn_of_lt_rank
  结论: [StrongRankCondition R]
  证明: by
  obtain ⟨t, ht, ht'⟩ := exists_set_linearIndependent R (M ⧸ Submodule.span R s)
  choose sec hsec using Submodule.mkQ_surjective (Submodule.span R s)
  have hsec' : (Submodule.mkQ _) ∘ sec = _root_.id := funext hsec
  have hst : Disjoint s (sec '' t) := by
    rw [Set.disjoint_iff]
    rintro _ 

Depends on / 依赖: Disjoint, Quotient, Quotient.mk_eq_zero, Set.disjoint_iff, Submodule, Submodule.mkQ, Submodule.mkQ_surjective, Submodule.span, Submodule.subset_span, Subtype, Subtype.coe_mk, _root_, _root_.id, coe_mk, disjoint_iff, exists_set_linearIndependent, mkQ_apply, mkQ_surjective, mk_eq_zero, ne_zero
-/
theorem exists_linearIndepOn_of_lt_rank [StrongRankCondition R]
    {s : Set M} (hs : LinearIndepOn R id s) :
    exists t, s subseteq t ∧ #t = Module.rank R M ∧ LinearIndepOn R id t := by
  obtain ⟨t, ht, ht'⟩ := exists_set_linearIndependent R (M ⧸ Submodule.span R s)
  choose sec hsec using Submodule.mkQ_surjective (Submodule.span R s)
  have hsec' : (Submodule.mkQ _) ∘ sec = _root_.id := funext hsec
  have hst : Disjoint s (sec '' t) := by
    rw [Set.disjoint_iff]
    rintro _ ⟨hxs, ⟨x, hxt, rfl⟩⟩
    apply ht'.ne_zero ⟨x, hxt⟩
    rw [Subtype.coe_mk]; rw [← hsec x]; rw [mkQ_apply]; rw [Quotient.mk_eq_zero]
    exact Submodule.subset_span hxs
  refine ⟨s union sec '' t, subset_union_left, ?_, ?_⟩
  · rw [Cardinal.mk_union_of_disjoint hst, Cardinal.mk_image_eq, ht,
      ← rank_quotient_add_rank (Submodule.span R s), add_comm, rank_span_set hs]
    exact HasLeftInverse.injective ⟨Submodule.Quotient.mk, hsec⟩
  · apply LinearIndepOn.union_id_of_quotient Submodule.subset_span hs
    rwa [linearIndepOn_iff_image (hsec'.symm ▸ injective_id).injOn.image_of_comp,
      ← image_comp, hsec', image_id]

/--
theorem `exists_linearIndependent_cons_of_lt_rank` / 定理 `exists_linearIndependent_cons_of_lt_rank`

English:
theorem exists_linearIndependent_cons_of_lt_rank
  statement: [StrongRankCondition R] {n : Nat} {v : Fin n -> M}
  proof: by
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_linearIndepOn_of_lt_rank hv.linearIndepOn_id
  have : range v != t := by
    refine fun e => h.ne ?_
    rw [← e]; rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective hv.injective] at h₂
    simpa only [mk_fintype, Fintype.card_fin, lift_natCast, lift_id'

中文:
定理 存在_linearIndependent_cons_of_lt_rank
  结论: [StrongRankCondition R] {n : 自然数} {v : 有限集 n -> M}
  证明: by
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_linearIndepOn_of_lt_rank hv.linearIndepOn_id
  have : range v != t := by
    refine fun e => h.ne ?_
    rw [← e]; rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective hv.injective] at h₂
    simpa only [mk_fintype, Fintype.card_fin, lift_natCast, lift_id'

Depends on / 依赖: Fin.cons_injective_iff.mpr, Fin.range_cons, Fintype, Fintype.card_fin, card_fin, cons_injective_iff, eq_iff, exists_linearIndepOn_of_lt_rank, h.ne, hv.injective, hv.linearIndepOn_id, injective, insert_subset, lift_id, lift_injective, lift_injective.eq_iff, lift_natCast, linearIndepOn_id, linearIndepOn_id_range_iff, mk_fintype
-/
theorem exists_linearIndependent_cons_of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    exists (x : M), LinearIndependent R (Fin.cons x v) := by
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_linearIndepOn_of_lt_rank hv.linearIndepOn_id
  have : range v != t := by
    refine fun e => h.ne ?_
    rw [← e]; rw [← lift_injective.eq_iff]; rw [mk_range_eq_of_injective hv.injective] at h₂
    simpa only [mk_fintype, Fintype.card_fin, lift_natCast, lift_id'] using h₂
  obtain ⟨x, hx, hx'⟩ := nonempty_of_ssubset (h₁.ssubset_of_ne this)
  exact ⟨x, (linearIndepOn_id_range_iff (Fin.cons_injective_iff.mpr ⟨hx', hv.injective⟩)).mp
    (h₃.mono (Fin.range_cons x v ▸ insert_subset hx h₁))⟩

/--
theorem `exists_linearIndependent_snoc_of_lt_rank` / 定理 `exists_linearIndependent_snoc_of_lt_rank`

English:
theorem exists_linearIndependent_snoc_of_lt_rank
  statement: [StrongRankCondition R] {n : Nat} {v : Fin n -> M}
  proof: by
  simp only [Fin.snoc_eq_cons_rotate]
  have ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_rank hv h
  exact ⟨x, hx.comp _ (finRotate _).injective⟩

中文:
定理 存在_linearIndependent_snoc_of_lt_rank
  结论: [StrongRankCondition R] {n : 自然数} {v : 有限集 n -> M}
  证明: by
  simp only [Fin.snoc_eq_cons_rotate]
  have ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_rank hv h
  exact ⟨x, hx.comp _ (finRotate _).injective⟩

Depends on / 依赖: Fin.snoc_eq_cons_rotate, exists_linearIndependent_cons_of_lt_rank, finRotate, hx.comp, injective, snoc_eq_cons_rotate
-/
theorem exists_linearIndependent_snoc_of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    exists (x : M), LinearIndependent R (Fin.snoc v x) := by
  simp only [Fin.snoc_eq_cons_rotate]
  have ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_rank hv h
  exact ⟨x, hx.comp _ (finRotate _).injective⟩

/--
theorem `exists_linearIndependent_pair_of_one_lt_rank` / 定理 `exists_linearIndependent_pair_of_one_lt_rank`

English:
theorem exists_linearIndependent_pair_of_one_lt_rank
  statement: [IsDomain R] [StrongRankCondition R]
  proof: by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (.of_subsingleton (v := ![x]) 0 hx) h
  have : Fin.snoc ![x] y = ![x, y] := by simp
  rw [this] at hy
  exact ⟨y, hy⟩

中文:
定理 存在_linearIndependent_pair_of_one_lt_rank
  结论: [是整环 R] [StrongRankCondition R]
  证明: by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (.of_subsingleton (v := ![x]) 0 hx) h
  have : Fin.snoc ![x] y = ![x, y] := by simp
  rw [this] at hy
  exact ⟨y, hy⟩

Depends on / 依赖: Fin.snoc, exists_linearIndependent_snoc_of_lt_rank, of_subsingleton
-/
theorem exists_linearIndependent_pair_of_one_lt_rank [IsDomain R] [StrongRankCondition R]
    [IsTorsionFree R M] (h : 1 < Module.rank R M) {x : M} (hx : x != 0) :
    exists y, LinearIndependent R ![x, y] := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (.of_subsingleton (v := ![x]) 0 hx) h
  have : Fin.snoc ![x] y = ![x, y] := by simp
  rw [this] at hy
  exact ⟨y, hy⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Submodule.exists_smul_notMem_of_rank_lt` / 定理 `Submodule.exists_smul_notMem_of_rank_lt`

English:
theorem Submodule.exists_smul_notMem_of_rank_lt
  statement: {N : Submodule R M}
  proof: by
  have : Module.rank R (M ⧸ N) != 0 := by
    intro e
    rw [← rank_quotient_add_rank N]; rw [e]; rw [zero_add] at h
    exact h.ne rfl
  rw [ne_eq]; rw [rank_eq_zero_iff]; rw [(Submodule.Quotient.mk_surjective N).forall] at this
  push Not at this
  simp_rw [← N.mkQ_apply, ← map_smul, N.mkQ_app

中文:
定理 子模.存在_smul_notMem_of_rank_lt
  结论: {N : 子模 R M}
  证明: by
  have : Module.rank R (M ⧸ N) != 0 := by
    intro e
    rw [← rank_quotient_add_rank N]; rw [e]; rw [zero_add] at h
    exact h.ne rfl
  rw [ne_eq]; rw [rank_eq_zero_iff]; rw [(Submodule.Quotient.mk_surjective N).forall] at this
  push Not at this
  simp_rw [← N.mkQ_apply, ← map_smul, N.mkQ_app

Depends on / 依赖: Module, Module.rank, N.mkQ_apply, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_surjective, h.ne, map_smul, mkQ_apply, mk_eq_zero, mk_surjective, ne_eq, rank_eq_zero_iff, rank_quotient_add_rank, simp_rw, zero_add
-/
theorem Submodule.exists_smul_notMem_of_rank_lt {N : Submodule R M}
    (h : Module.rank R N < Module.rank R M) : exists m : M, forall r : R, r != 0 -> r • m ∉ N := by
  have : Module.rank R (M ⧸ N) != 0 := by
    intro e
    rw [← rank_quotient_add_rank N]; rw [e]; rw [zero_add] at h
    exact h.ne rfl
  rw [ne_eq]; rw [rank_eq_zero_iff]; rw [(Submodule.Quotient.mk_surjective N).forall] at this
  push Not at this
  simp_rw [← N.mkQ_apply, ← map_smul, N.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero] at this
  exact this

open Cardinal Basis Submodule Function Set LinearMap

/--
theorem `Submodule.rank_sup_add_rank_inf_eq` / 定理 `Submodule.rank_sup_add_rank_inf_eq`

English:
theorem Submodule.rank_sup_add_rank_inf_eq
  given: (s t : Submodule R M)
  proof: by
  conv_rhs => enter [2]; rw [show t = (s ⊔ t) ⊓ t by simp]
  rw [← rank_quotient_add_rank ((s ⊓ t).comap s.subtype)]; rw [← rank_quotient_add_rank (t.comap (s ⊔ t).subtype)]; rw [comap_inf]; rw [(quotientInfEquivSupQuotient s t).rank_eq]; rw [← comap_inf]; rw [(equivSubtypeMap s (comap _ (s ⊓ t))

中文:
定理 子模.rank_sup_add_rank_inf_eq
  条件: (s t : 子模 R M)
  证明: by
  conv_rhs => enter [2]; rw [show t = (s ⊔ t) ⊓ t by simp]
  rw [← rank_quotient_add_rank ((s ⊓ t).comap s.subtype)]; rw [← rank_quotient_add_rank (t.comap (s ⊔ t).subtype)]; rw [comap_inf]; rw [(quotientInfEquivSupQuotient s t).rank_eq]; rw [← comap_inf]; rw [(equivSubtypeMap s (comap _ (s ⊓ t))

Depends on / 依赖: Submodule, Submodule.map_comap_subtype, add_right_comm, comap_inf, conv_rhs, equivSubtypeMap, inf_assoc, inf_idem, map_comap_subtype, quotientInfEquivSupQuotient, rank_eq, rank_quotient_add_rank, s.subtype, subtype, t.comap
-/
theorem Submodule.rank_sup_add_rank_inf_eq (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s ⊓ t : Submodule R M) =
    Module.rank R s + Module.rank R t := by
  conv_rhs => enter [2]; rw [show t = (s ⊔ t) ⊓ t by simp]
  rw [← rank_quotient_add_rank ((s ⊓ t).comap s.subtype)]; rw [← rank_quotient_add_rank (t.comap (s ⊔ t).subtype)]; rw [comap_inf]; rw [(quotientInfEquivSupQuotient s t).rank_eq]; rw [← comap_inf]; rw [(equivSubtypeMap s (comap _ (s ⊓ t))).rank_eq]; rw [Submodule.map_comap_subtype]; rw [(equivSubtypeMap (s ⊔ t) (comap _ t)).rank_eq]; rw [Submodule.map_comap_subtype]; rw [← inf_assoc]; rw [inf_idem]; rw [add_right_comm]

/--
theorem `Submodule.rank_add_le_rank_add_rank` / 定理 `Submodule.rank_add_le_rank_add_rank`

English:
theorem Submodule.rank_add_le_rank_add_rank
  given: (s t : Submodule R M)
  proof: by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _

中文:
定理 子模.rank_add_le_rank_add_rank
  条件: (s t : 子模 R M)
  证明: by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _

Depends on / 依赖: Submodule, Submodule.rank_sup_add_rank_inf_eq, rank_sup_add_rank_inf_eq, self_le_add_right
-/
theorem Submodule.rank_add_le_rank_add_rank (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) <= Module.rank R s + Module.rank R t := by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _

section Finrank

open Submodule Module

variable [StrongRankCondition R]

/--
theorem `exists_linearIndependent_snoc_of_lt_finrank` / 定理 `exists_linearIndependent_snoc_of_lt_finrank`

English:
theorem exists_linearIndependent_snoc_of_lt_finrank
  statement: {n : Nat} {v : Fin n -> M}
  proof: exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

中文:
定理 存在_linearIndependent_snoc_of_lt_finrank
  结论: {n : 自然数} {v : 有限集 n -> M}
  证明: exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

Depends on / 依赖: exists_linearIndependent_snoc_of_lt_rank, lt_rank_of_lt_finrank
-/
theorem exists_linearIndependent_snoc_of_lt_finrank {n : Nat} {v : Fin n -> M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    exists (x : M), LinearIndependent R (Fin.snoc v x) :=
  exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

/--
theorem `exists_linearIndependent_cons_of_lt_finrank` / 定理 `exists_linearIndependent_cons_of_lt_finrank`

English:
theorem exists_linearIndependent_cons_of_lt_finrank
  statement: {n : Nat} {v : Fin n -> M}
  proof: exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

中文:
定理 存在_linearIndependent_cons_of_lt_finrank
  结论: {n : 自然数} {v : 有限集 n -> M}
  证明: exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

Depends on / 依赖: exists_linearIndependent_cons_of_lt_rank, lt_rank_of_lt_finrank
-/
theorem exists_linearIndependent_cons_of_lt_finrank {n : Nat} {v : Fin n -> M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    exists (x : M), LinearIndependent R (Fin.cons x v) :=
  exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

/--
theorem `exists_linearIndependent_pair_of_one_lt_finrank` / 定理 `exists_linearIndependent_pair_of_one_lt_finrank`

English:
theorem exists_linearIndependent_pair_of_one_lt_finrank
  statement: [IsDomain R] [Module.IsTorsionFree R M]
  proof: exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

中文:
定理 存在_linearIndependent_pair_of_one_lt_finrank
  结论: [是整环 R] [模.是无挠 R M]
  证明: exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

Depends on / 依赖: exists_linearIndependent_pair_of_one_lt_rank, one_lt_rank_of_one_lt_finrank
-/
theorem exists_linearIndependent_pair_of_one_lt_finrank [IsDomain R] [Module.IsTorsionFree R M]
    (h : 1 < finrank R M) {x : M} (hx : x != 0) :
    exists y, LinearIndependent R ![x, y] :=
  exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

/--
lemma `Submodule.finrank_quotient_add_finrank` / 引理 `Submodule.finrank_quotient_add_finrank`

English:
lemma Submodule.finrank_quotient_add_finrank
  given: [Module.Finite R M] (N : Submodule R M)
  proof: by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [Module.finrank_eq_rank]; rw [Nat.cast_add]; rw [Module.finrank_eq_rank]; rw [Submodule.finrank_eq_rank]
  exact HasRankNullity.rank_quotient_add_rank _

中文:
引理 子模.finrank_quotient_add_finrank
  条件: [模.有限 R M] (N : 子模 R M)
  证明: by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [Module.finrank_eq_rank]; rw [Nat.cast_add]; rw [Module.finrank_eq_rank]; rw [Submodule.finrank_eq_rank]
  exact HasRankNullity.rank_quotient_add_rank _

Depends on / 依赖: Cardinal, HasRankNullity, HasRankNullity.rank_quotient_add_rank, Module, Module.finrank_eq_rank, Nat.cast_add, Nat.cast_inj, Submodule, Submodule.finrank_eq_rank, cast_add, cast_inj, finrank_eq_rank, rank_quotient_add_rank
-/
lemma Submodule.finrank_quotient_add_finrank [Module.Finite R M] (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N = finrank R M := by
  rw [← Nat.cast_inj (R := Cardinal)]; rw [Module.finrank_eq_rank]; rw [Nat.cast_add]; rw [Module.finrank_eq_rank]; rw [Submodule.finrank_eq_rank]
  exact HasRankNullity.rank_quotient_add_rank _

/--
lemma `Submodule.finrank_quotient` / 引理 `Submodule.finrank_quotient`

English:
lemma Submodule.finrank_quotient
  statement: [Module.Finite R M] {S : Type*} [Ring S] [SMul R S] [Module S M]
  proof: by
  rw [← (N.restrictScalars R).finrank_quotient_add_finrank]
  exact Nat.eq_sub_of_add_eq rfl

中文:
引理 子模.finrank_quotient
  结论: [模.有限 R M] {S : 类型} [环 S] [标量乘法 R S] [模 S M]
  证明: by
  rw [← (N.restrictScalars R).finrank_quotient_add_finrank]
  exact Nat.eq_sub_of_add_eq rfl

Depends on / 依赖: N.restrictScalars, Nat.eq_sub_of_add_eq, eq_sub_of_add_eq, finrank_quotient_add_finrank, restrictScalars
-/
lemma Submodule.finrank_quotient [Module.Finite R M] {S : Type*} [Ring S] [SMul R S] [Module S M]
    [IsScalarTower R S M] (N : Submodule S M) : finrank R (M ⧸ N) = finrank R M - finrank R N := by
  rw [← (N.restrictScalars R).finrank_quotient_add_finrank]
  exact Nat.eq_sub_of_add_eq rfl

/--
lemma `Submodule.disjoint_ker_of_finrank_le` / 引理 `Submodule.disjoint_ker_of_finrank_le`

English:
lemma Submodule.disjoint_ker_of_finrank_le
  statement: [IsDomain R] [IsTorsionFree R M] {N : Type*}
  proof: by
refine LinearMap.injective_domRestrict_iff.mp LinearMap.ker_eq_bot.mp
    Submodule.rank_eq_zero.mp ?_
  rw [← Submodule.finrank_eq_rank]; rw [Nat.cast_eq_zero]
  rw [← LinearMap.range_domRestrict] at h
  have := (LinearMap.ker (f.domRestrict L)).finrank_quotient_add_finrank
  rw [LinearEquiv.fin

中文:
引理 子模.disjoint_ker_of_finrank_le
  结论: [是整环 R] [是无挠 R M] {N : 类型}
  证明: by
refine LinearMap.injective_domRestrict_iff.mp LinearMap.ker_eq_bot.mp
    Submodule.rank_eq_zero.mp ?_
  rw [← Submodule.finrank_eq_rank]; rw [Nat.cast_eq_zero]
  rw [← LinearMap.range_domRestrict] at h
  have := (LinearMap.ker (f.domRestrict L)).finrank_quotient_add_finrank
  rw [LinearEquiv.fin

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, LinearMap, LinearMap.injective_domRestrict_iff.mp, LinearMap.ker, LinearMap.ker_eq_bot.mp, LinearMap.range_domRestrict, Nat.cast_eq_zero, Submodule, Submodule.finrank_eq_rank, Submodule.rank_eq_zero.mp, cast_eq_zero, domRestrict, f.domRestrict, finrank_eq, finrank_eq_rank, finrank_quotient_add_finrank, injective_domRestrict_iff, ker_eq_bot, quotKerEquivRange
-/
lemma Submodule.disjoint_ker_of_finrank_le [IsDomain R] [IsTorsionFree R M] {N : Type*}
    [AddCommGroup N] [Module R N] {L : Submodule R M} [Module.Finite R L] (f : M ->ₗ[R] N)
    (h : finrank R L <= finrank R (L.map f)) :
    Disjoint L (LinearMap.ker f) := by
refine LinearMap.injective_domRestrict_iff.mp LinearMap.ker_eq_bot.mp
    Submodule.rank_eq_zero.mp ?_
  rw [← Submodule.finrank_eq_rank]; rw [Nat.cast_eq_zero]
  rw [← LinearMap.range_domRestrict] at h
  have := (LinearMap.ker (f.domRestrict L)).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq (f.domRestrict L).quotKerEquivRange] at this
  lia

end Finrank

section

open Submodule Module

variable [StrongRankCondition R] [Module.Finite R M]

/--
lemma `Submodule.exists_of_finrank_lt` / 引理 `Submodule.exists_of_finrank_lt`

English:
lemma Submodule.exists_of_finrank_lt
  given: (N : Submodule R M) (h : finrank R N < finrank R M)
  proof: by
  obtain ⟨s, hs, hs'⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := R) (M := M ⧸ N) le_rfl
  obtain ⟨v, hv⟩ : s.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero,
    hs, finrank_quotient, tsub_eq_zero_iff_le, not_le]
  obtain ⟨v, rfl⟩ := N.mkQ_surjective

中文:
引理 子模.存在_of_finrank_lt
  条件: (N : 子模 R M) (h : finrank R N < finrank R M)
  证明: by
  obtain ⟨s, hs, hs'⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := R) (M := M ⧸ N) le_rfl
  obtain ⟨v, hv⟩ : s.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero,
    hs, finrank_quotient, tsub_eq_zero_iff_le, not_le]
  obtain ⟨v, rfl⟩ := N.mkQ_surjective

Depends on / 依赖: Finset, Finset.card_eq_zero, Finset.nonempty_iff_ne_empty, Finsupp, Finsupp.linearCombination_single, Finsupp.single, Finsupp.single_eq_zero, N.mkQ_surjective, Nonempty, Quotient, Submodule, Submodule.Quotient, Submodule.mkQ_apply, card_eq_zero, exists_finset_linearIndependent_of_le_finrank, finrank_quotient, le_rfl, linearCombination_single, linearIndependent_iff, linearIndependent_iff.mp
-/
lemma Submodule.exists_of_finrank_lt (N : Submodule R M) (h : finrank R N < finrank R M) :
    exists m : M, forall r : R, r != 0 -> r • m ∉ N := by
  obtain ⟨s, hs, hs'⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := R) (M := M ⧸ N) le_rfl
  obtain ⟨v, hv⟩ : s.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero,
    hs, finrank_quotient, tsub_eq_zero_iff_le, not_le]
  obtain ⟨v, rfl⟩ := N.mkQ_surjective v
  refine ⟨v, fun r hr => mt ?_ hr⟩
  have := linearIndependent_iff.mp hs' (Finsupp.single ⟨_, hv⟩ r)
  rwa [Finsupp.linearCombination_single, Finsupp.single_eq_zero, ← map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end
