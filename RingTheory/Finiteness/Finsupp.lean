/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of (sub)modules and finitely supported functions

-/

public section

open Function (Surjective)
open Finsupp

namespace LinearMap

variable {R M N ι : Type*} (S : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N] [Semiring S] [Module S N] [SMulCommClass R S N]

/--
Definition of `finsuppLinearMap` / `finsuppLinearMap` 的定义

English:
definition finsuppLinearMap
  signature: : (ι ->₀ M ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] ι ->₀ N
  body: have := SMulCommClass.symm
  LinearMap.flip
  { toFun := (Finsupp.mapRange.linearMap <| flip id ·)
    map_add' := fun _ _ => by ext; simp
    map_smul' := fun _ _ => by ext; simp }

中文:
定义 finsuppLinearMap
  签名: : (ι ->₀ M ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] ι ->₀ N
  定义体: have := SMulCommClass.symm
  LinearMap.flip
  { toFun := (Finsupp.mapRange.linearMap <| flip id ·)
    map_add' := fun _ _ => by ext; simp
    map_smul' := fun _ _ => by ext; simp }
-/
@[expose, simps!] noncomputable def finsuppLinearMap : (ι ->₀ M ->ₗ[R] N) ->ₗ[S] M ->ₗ[R] ι ->₀ N :=
  have := SMulCommClass.symm
  LinearMap.flip
  { toFun := (Finsupp.mapRange.linearMap <| flip id ·)
    map_add' := fun _ _ => by ext; simp
    map_smul' := fun _ _ => by ext; simp }

variable (R M N ι)

/--
theorem `finsuppLinearMap_injective` / 定理 `finsuppLinearMap_injective`

English:
theorem finsuppLinearMap_injective
  proof: fun _ _ eq => by ext i m; exact congr($eq m i)

中文:
定理 finsuppLinearMap_injective
  证明: fun _ _ eq => by ext i m; exact congr($eq m i)
-/
theorem finsuppLinearMap_injective :
    Function.Injective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N) :=
  fun _ _ eq => by ext i m; exact congr($eq m i)

/--
theorem `finsuppLinearMap_bijective_of_moduleFinite` / 定理 `finsuppLinearMap_bijective_of_moduleFinite`

English:
theorem finsuppLinearMap_bijective_of_moduleFinite
  given: [Module.Finite R M]
  proof: by
  have ⟨s, span_s⟩ := Module.finite_def.mp ‹Module.Finite R M›
  classical refine ⟨finsuppLinearMap_injective ..,
    fun x => ⟨.onFinset (s.sup fun m => (x m).support) (lapply · ∘ₗ x) fun i h => ?_, ?_⟩⟩
  · contrapose! h; exact LinearMap.ext_on span_s (by simpa using! h)
  · ext; rfl

中文:
定理 finsuppLinearMap_bijective_of_moduleFinite
  条件: [模.有限 R M]
  证明: by
  have ⟨s, span_s⟩ := Module.finite_def.mp ‹Module.Finite R M›
  classical refine ⟨finsuppLinearMap_injective ..,
    fun x => ⟨.onFinset (s.sup fun m => (x m).support) (lapply · ∘ₗ x) fun i h => ?_, ?_⟩⟩
  · contrapose! h; exact LinearMap.ext_on span_s (by simpa using! h)
  · ext; rfl

Depends on / 依赖: Finite, LinearMap, LinearMap.ext_on, Module, Module.Finite, Module.finite_def.mp, classical, contrapose, ext_on, finite_def, finsuppLinearMap_injective, lapply, onFinset, s.sup, span_s, support
-/
theorem finsuppLinearMap_bijective_of_moduleFinite [Module.Finite R M] :
    Function.Bijective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N) := by
  have ⟨s, span_s⟩ := Module.finite_def.mp ‹Module.Finite R M›
  classical refine ⟨finsuppLinearMap_injective ..,
    fun x => ⟨.onFinset (s.sup fun m => (x m).support) (lapply · ∘ₗ x) fun i h => ?_, ?_⟩⟩
  · contrapose! h; exact LinearMap.ext_on span_s (by simpa using! h)
  · ext; rfl

/--
theorem `finsuppLinearMap_bijective_of_finite` / 定理 `finsuppLinearMap_bijective_of_finite`

English:
theorem finsuppLinearMap_bijective_of_finite
  given: [Finite ι]
  proof: finsuppLinearMap_injective ..
  right x := ⟨equivFunOnFinite.symm fun i => lapply i ∘ₗ x, by ext; simp⟩

中文:
定理 finsuppLinearMap_bijective_of_finite
  条件: [有限 ι]
  证明: finsuppLinearMap_injective ..
  right x := ⟨equivFunOnFinite.symm fun i => lapply i ∘ₗ x, by ext; simp⟩

Depends on / 依赖: finsuppLinearMap_injective
-/
theorem finsuppLinearMap_bijective_of_finite [Finite ι] :
    Function.Bijective (finsuppLinearMap S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι ->₀ N) where
  left := finsuppLinearMap_injective ..
  right x := ⟨equivFunOnFinite.symm fun i => lapply i ∘ₗ x, by ext; simp⟩

end LinearMap

namespace Submodule

variable {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

open Set

/--
theorem `fg_of_fg_map_of_fg_inf_ker` / 定理 `fg_of_fg_map_of_fg_inf_ker`

English:
theorem fg_of_fg_map_of_fg_inf_ker
  statement: (f : M ->ₗ[R] P) {s : Submodule R M}
  proof: by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
  obtain ⟨t1, ht1⟩ := hs1
  obtain ⟨t2, ht2⟩ := hs2
  have : forall y in t1, exists x in s, f x = y := by
    intro y hy
    have : y in s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : exists g : P -> M, forall y in t1, g y in s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y in t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  obtain ⟨g, hg⟩ := this
  clear this
  exists t1.image g union t2
  rw [Finset.coe_union]; rw [span_union]; rw [Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x in span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x in s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1]; rw [← Set.image_id (t1 : Set P)]; rw [Finsupp.mem_span_image_iff_linearCombination] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(linearCombination R id).toFun ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        x - linearCombination R id ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_linearCombination]
    refine ⟨_, ?_, rfl⟩
    have : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g]; rw [mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2]; rw [mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]; rw [Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index]; rw [Finsupp.sum]; rw [Finsupp.sum]; rw [map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul]; rw [(hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _

中文:
定理 fg_of_fg_map_of_fg_inf_ker
  结论: (f : M ->ₗ[R] P) {s : 子模 R M}
  证明: by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
  obtain ⟨t1, ht1⟩ := hs1
  obtain ⟨t2, ht2⟩ := hs2
  have : forall y in t1, exists x in s, f x = y := by
    intro y hy
    have : y in s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : exists g : P -> M, forall y in t1, g y in s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y in t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  obtain ⟨g, hg⟩ := this
  clear this
  exists t1.image g union t2
  rw [Finset.coe_union]; rw [span_union]; rw [Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x in span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x in s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1]; rw [← Set.image_id (t1 : Set P)]; rw [Finsupp.mem_span_image_iff_linearCombination] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(linearCombination R id).toFun ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        x - linearCombination R id ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_linearCombination]
    refine ⟨_, ?_, rfl⟩
    have : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g]; rw [mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2]; rw [mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]; rw [Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index]; rw [Finsupp.sum]; rw [Finsupp.sum]; rw [map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul]; rw [(hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _

Depends on / 依赖: Classical, Classical.decEq, dif_po, mem_map, s.map, subset_span
-/
theorem fg_of_fg_map_of_fg_inf_ker (f : M ->ₗ[R] P) {s : Submodule R M}
    (hs1 : (s.map f).FG)
    (hs2 : (s ⊓ LinearMap.ker f).FG) : s.FG := by
  have := Classical.decEq R
  have := Classical.decEq M
  have := Classical.decEq P
  obtain ⟨t1, ht1⟩ := hs1
  obtain ⟨t2, ht2⟩ := hs2
  have : forall y in t1, exists x in s, f x = y := by
    intro y hy
    have : y in s.map f := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : exists g : P -> M, forall y in t1, g y in s ∧ f (g y) = y := by
    choose g hg1 hg2 using this
    exists fun y => if H : y in t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  obtain ⟨g, hg⟩ := this
  clear this
  exists t1.image g union t2
  rw [Finset.coe_union]; rw [span_union]; rw [Finset.coe_image]
  apply le_antisymm
  · refine sup_le (span_le.2 <| image_subset_iff.2 ?_) (span_le.2 ?_)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have : x in span R t2 := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x in s.map f := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1]; rw [← Set.image_id (t1 : Set P)]; rw [Finsupp.mem_span_image_iff_linearCombination] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine
    mem_sup.2
      ⟨(linearCombination R id).toFun ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        x - linearCombination R id ((lmapDomain R R g : (P ->₀ R) -> M ->₀ R) l), ?_,
        add_sub_cancel _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_linearCombination]
    refine ⟨_, ?_, rfl⟩
    have : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmapDomain_supported _ _ g]; rw [mem_map]
    refine ⟨l, hl1, ?_⟩
    rfl
  rw [ht2]; rw [mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]; rw [Finsupp.sum_mapDomain_index]
    · refine s.sum_mem ?_
      intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.linearCombination_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.lmapDomain_apply]
    rw [Finsupp.sum_mapDomain_index]; rw [Finsupp.sum]; rw [Finsupp.sum]; rw [map_sum]
    · rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun y hy => ?_
      unfold id
      rw [f.map_smul]; rw [(hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _

/--
theorem `fg_ker_comp` / 定理 `fg_ker_comp`

English:
theorem fg_ker_comp
  statement: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  proof: by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) <=
      (LinearMap.ker g).comap f from comap_mono bot_le)]

中文:
定理 fg_ker_comp
  结论: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
  证明: by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) <=
      (LinearMap.ker g).comap f from comap_mono bot_le)]

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_comp, LinearMap.range_eq_top, Submodule, Submodule.map_comap_eq, bot_le, comap_mono, fg_of_fg_map_of_fg_inf_ker, inf_of_le_right, ker_comp, map_comap_eq, range_eq_top, top_inf_eq
-/
theorem fg_ker_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P)
    (hf1 : (LinearMap.ker f).FG) (hf2 : (LinearMap.ker g).FG)
    (hsur : Function.Surjective f) : (LinearMap.ker (g.comp f)).FG := by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show (LinearMap.ker f) <=
      (LinearMap.ker g).comap f from comap_mono bot_le)]

/-- If $M → N → P → 0$ is exact and $M$ and $P$ are finitely generated then so is $N$.

This is the `Module.Finite` version of `Submodule.fg_of_fg_map_of_fg_inf_ker`. -/
@[stacks 0519 "(1)"]
/--
lemma `_root_.Module.Finite.of_exact` / 引理 `_root_.Module.Finite.of_exact`

English:
lemma _root_.Module.Finite.of_exact
  statement: {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
  proof: by
  refine ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [← LinearMap.range_eq_top] at h_surj
    rw [Submodule.map_top]; rw [h_surj]
    exact Module.Finite.fg_top
  · simp [LinearMap.exact_iff.1 h_exact]

中文:
引理 _root_.模.有限.of_exact
  结论: {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
  证明: by
  refine ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [← LinearMap.range_eq_top] at h_surj
    rw [Submodule.map_top]; rw [h_surj]
    exact Module.Finite.fg_top
  · simp [LinearMap.exact_iff.1 h_exact]

Depends on / 依赖: Finite, LinearMap, LinearMap.exact_iff, LinearMap.range_eq_top, Module, Module.Finite.fg_top, Submodule, Submodule.map_top, exact_iff, fg_of_fg_map_of_fg_inf_ker, fg_top, h_exact, h_surj, map_top, range_eq_top
-/
lemma _root_.Module.Finite.of_exact {f : M ->ₗ[R] N} {g : N ->ₗ[R] P}
    (h_exact : Function.Exact f g) (h_surj : Function.Surjective g)
    [Module.Finite R M] [Module.Finite R P] : Module.Finite R N := by
  refine ⟨(⊤ : Submodule R _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · rw [← LinearMap.range_eq_top] at h_surj
    rw [Submodule.map_top]; rw [h_surj]
    exact Module.Finite.fg_top
  · simp [LinearMap.exact_iff.1 h_exact]

/--
theorem `_root_.Module.Finite.of_submodule_quotient` / 定理 `_root_.Module.Finite.of_submodule_quotient`

English:
theorem _root_.Module.Finite.of_submodule_quotient
  statement: (N : Submodule R M) [Module.Finite R N]
  proof: .of_exact (LinearMap.exact_subtype_mkQ N) (Quotient.mk_surjective _)

中文:
定理 _root_.模.有限.of_submodule_quotient
  结论: (N : 子模 R M) [模.有限 R N]
  证明: .of_exact (LinearMap.exact_subtype_mkQ N) (Quotient.mk_surjective _)

Depends on / 依赖: LinearMap, LinearMap.exact_subtype_mkQ, Quotient, Quotient.mk_surjective, exact_subtype_mkQ, mk_surjective, of_exact
-/
theorem _root_.Module.Finite.of_submodule_quotient (N : Submodule R M) [Module.Finite R N]
    [Module.Finite R (M ⧸ N)] : Module.Finite R M :=
  .of_exact (LinearMap.exact_subtype_mkQ N) (Quotient.mk_surjective _)

end Submodule

section

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V]

/--
Instance `Module.Finite.finsupp` / 实例 `Module.Finite.finsupp`

English:
instance Module.Finite.finsupp
  signature: {ι : Type*} [_root_.Finite ι] [Module.Finite R V]
  body: Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

中文:
实例 模.有限.finsupp
  签名: {ι : 类型} [_root_.有限 ι] [模.有限 R V]
  定义体: Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

Depends on / 依赖: Finite, Finsupp, Finsupp.linearEquivFunOnFinite, Module, Module.Finite.equiv, linearEquivFunOnFinite
-/
instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι ->₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end

namespace AddMonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

/--
Instance `moduleFinite` / 实例 `moduleFinite`

English:
instance moduleFinite
  signature: : Module.Finite R S[M]
  body: .equiv .symm coeffLinearEquiv _

中文:
实例 moduleFinite
  签名: : 模.有限 R S[M]
  定义体: .equiv .symm coeffLinearEquiv _

Depends on / 依赖: coeffLinearEquiv
-/
instance moduleFinite : Module.Finite R S[M] := .equiv .symm coeffLinearEquiv _

end AddMonoidAlgebra

namespace MonoidAlgebra
variable {M R S : Type*} [Finite M] [Semiring R] [Semiring S] [Module R S] [Module.Finite R S]

/--
Instance `moduleFinite` / 实例 `moduleFinite`

English:
instance moduleFinite
  signature: : Module.Finite R S[M]
  body: .equiv .symm coeffLinearEquiv _

中文:
实例 moduleFinite
  签名: : 模.有限 R S[M]
  定义体: .equiv .symm coeffLinearEquiv _

Depends on / 依赖: coeffLinearEquiv
-/
instance moduleFinite : Module.Finite R S[M] := .equiv .symm coeffLinearEquiv _

end MonoidAlgebra

namespace FreeAbelianGroup
variable {σ : Type*} [Finite σ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite Int (FreeAbelianGroup σ)
  body: .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

中文:
实例 :
  签名: 模.有限 整数 (自由交换群 σ)
  定义体: .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, of_surjective, surjective, toIntLinearEquiv, toIntLinearEquiv.symm.surjective
-/
instance : Module.Finite Int (FreeAbelianGroup σ) :=
  .of_surjective _ (FreeAbelianGroup.equivFinsupp σ).toIntLinearEquiv.symm.surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid.FG (FreeAbelianGroup σ)
  body: by
  rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]; infer_instance

中文:
实例 :
  签名: 加法幺半群.FG (自由交换群 σ)
  定义体: by
  rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]; infer_instance

Depends on / 依赖: AddGroup, AddGroup.fg_iff_addMonoid_fg, Finite, Module, Module.Finite.iff_addGroup_fg, fg_iff_addMonoid_fg, iff_addGroup_fg, infer_instance
-/
instance : AddMonoid.FG (FreeAbelianGroup σ) := by
  rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]; infer_instance

end FreeAbelianGroup
