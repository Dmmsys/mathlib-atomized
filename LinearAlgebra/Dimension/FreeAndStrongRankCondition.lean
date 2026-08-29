/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!

# Some results on free modules over rings satisfying strong rank condition

This file contains some results on free modules over rings satisfying strong rank condition.
Most of them are generalized from the same result assuming the base ring being a division ring,
and are moved from the files `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`
and `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.

-/

@[expose] public section

open Cardinal Module Module Set Submodule

universe u v

section Module

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V]

/--
Definition of `Basis.ofRankEqZero` / `Basis.ofRankEqZero` 的定义

English:
definition Basis.ofRankEqZero
  signature: [Module.Free K V] {ι : Type*} [IsEmpty ι]
  body: haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _

@[simp]

中文:
定义 Basis.ofRankEqZero
  签名: [Module.Free K V] {ι : 类型} [IsEmpty ι]
  定义体: haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _

@[simp]

Depends on / 依赖: Basis.empty, Module, Module.Free.exists_basis, Subsingleton, b.mk_eq_rank, b.repr.toEquiv.subsingleton, exists_basis, mk_eq_rank, mk_eq_zero_iff, subsingleton, toEquiv
-/
noncomputable def Basis.ofRankEqZero [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _

@[simp]
/--
theorem `Basis.ofRankEqZero_apply` / 定理 `Basis.ofRankEqZero_apply`

English:
theorem Basis.ofRankEqZero_apply
  statement: [Module.Free K V] {ι : Type*} [IsEmpty ι]
  proof: rfl

中文:
定理 Basis.ofRankEqZero_apply
  结论: [Module.Free K V] {ι : 类型} [IsEmpty ι]
  证明: rfl
-/
theorem Basis.ofRankEqZero_apply [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) (i : ι) : Basis.ofRankEqZero hV i = 0 := rfl

/--
theorem `le_rank_iff_exists_linearIndependent` / 定理 `le_rank_iff_exists_linearIndependent`

English:
theorem le_rank_iff_exists_linearIndependent
  given: [Module.Free K V] {c : Cardinal}
  proof: by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · intro h
    obtain ⟨κ, t'⟩ := Module.Free.exists_basis (R := K) (M := V)
    let t := t'.reindexRange
    have : LinearIndepOn K id (Set.range t') := by
      convert! t.linearIndependent.linearIndepOn_id
      ext
      simp [t]
  

中文:
定理 le_rank_iff_exists_linearIndependent
  条件: [Module.Free K V] {c : Cardinal}
  证明: by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · intro h
    obtain ⟨κ, t'⟩ := Module.Free.exists_basis (R := K) (M := V)
    let t := t'.reindexRange
    have : LinearIndepOn K id (Set.range t') := by
      convert! t.linearIndependent.linearIndepOn_id
      ext
      simp [t]
  

Depends on / 依赖: LinearIndepOn, Module, Module.Free.exists_basis, Set.range, cardinal_le_rank, convert, exists_basis, le_mk_iff_exists_subset, linearIndepOn_id, linearIndependent, mk_eq_rank, nontrivial_of_invariantBasisNumber, reindexRange, si.cardinal_le_rank, t.linearIndependent.linearIndepOn_id, t.mk_eq_rank, this.mono
-/
theorem le_rank_iff_exists_linearIndependent [Module.Free K V] {c : Cardinal} :
    c <= Module.rank K V ↔ exists s : Set V, #s = c ∧ LinearIndepOn K id s := by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · intro h
    obtain ⟨κ, t'⟩ := Module.Free.exists_basis (R := K) (M := V)
    let t := t'.reindexRange
    have : LinearIndepOn K id (Set.range t') := by
      convert! t.linearIndependent.linearIndepOn_id
      ext
      simp [t]
    rw [← t.mk_eq_rank'']; rw [le_mk_iff_exists_subset] at h
    rcases h with ⟨s, hst, hsc⟩
    exact ⟨s, hsc, this.mono hst⟩
  · rintro ⟨s, rfl, si⟩
    exact si.cardinal_le_rank

/--
theorem `le_rank_iff_exists_linearIndependent_finset` / 定理 `le_rank_iff_exists_linearIndependent_finset`

English:
theorem le_rank_iff_exists_linearIndependent_finset
  proof: by
  simp only [le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

中文:
定理 le_rank_iff_exists_linearIndependent_finset
  证明: by
  simp only [le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

Depends on / 依赖: le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset
-/
theorem le_rank_iff_exists_linearIndependent_finset
    [Module.Free K V] {n : Nat} : ↑n <= Module.rank K V ↔
    exists s : Finset V, s.card = n ∧ LinearIndependent K ((↑) : ↥(s : Set V) -> V) := by
  simp only [le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

/--
theorem `rank_le_one_iff` / 定理 `rank_le_one_iff`

English:
theorem rank_le_one_iff
  given: [Module.Free K V]
  proof: by
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
  constructor
  · intro hd
    rw [← b.mk_eq_rank'']; rw [le_one_iff_subsingleton] at hd
    rcases isEmpty_or_nonempty κ with hb | ⟨⟨i⟩⟩
    · use 0
      have h' : forall v : V, v = 0 := by
        simpa [range_eq_empty, Submodule.eq

中文:
定理 rank_le_one_iff
  条件: [Module.Free K V]
  证明: by
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
  constructor
  · intro hd
    rw [← b.mk_eq_rank'']; rw [le_one_iff_subsingleton] at hd
    rcases isEmpty_or_nonempty κ with hb | ⟨⟨i⟩⟩
    · use 0
      have h' : forall v : V, v = 0 := by
        simpa [range_eq_empty, Submodule.eq

Depends on / 依赖: Module, Module.Free.exists_basis, Submodule, Submodule.eq_bot_iff, b.mk_eq_rank, b.span_eq, b.span_eq.symm, eq_bot_iff, eq_singleton_of_mem, exists_basis, isEmpty_or_nonempty, le_one_iff_subsingleton, mem_range_self, mem_spa, mem_top, mk_eq_rank, range_eq_empty, span_eq, subsingleton_range
-/
theorem rank_le_one_iff [Module.Free K V] :
    Module.rank K V <= 1 ↔ exists v₀ : V, forall v, exists r : K, r • v₀ = v := by
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
  constructor
  · intro hd
    rw [← b.mk_eq_rank'']; rw [le_one_iff_subsingleton] at hd
    rcases isEmpty_or_nonempty κ with hb | ⟨⟨i⟩⟩
    · use 0
      have h' : forall v : V, v = 0 := by
        simpa [range_eq_empty, Submodule.eq_bot_iff] using b.span_eq.symm
      intro v
      simp [h' v]
    · use b i
      have h' : K ∙ b i = ⊤ :=
        (subsingleton_range b).eq_singleton_of_mem (mem_range_self i) ▸ b.span_eq
      intro v
      have hv : v in (⊤ : Submodule K V) := mem_top
      rwa [← h', mem_span_singleton] at hv
  · rintro ⟨v₀, hv₀⟩
    have h : K ∙ v₀ = ⊤ := by
      ext
      simp [mem_span_singleton, hv₀]
    rw [← rank_top]; rw [← h]
    refine (rank_span_le _).trans_eq ?_
    simp

/--
theorem `rank_eq_one_iff` / 定理 `rank_eq_one_iff`

English:
theorem rank_eq_one_iff
  given: [Module.Free K V]
  proof: by
  have := nontrivial_of_invariantBasisNumber K
  refine ⟨fun h => ?_, fun ⟨v₀, h, hv⟩ => (rank_le_one_iff.2 ⟨v₀, hv⟩).antisymm ?_⟩
  · obtain ⟨v₀, hv⟩ := rank_le_one_iff.1 h.le
    refine ⟨v₀, fun hzero => ?_, hv⟩
    simp_rw [hzero, smul_zero, exists_const] at hv
    have : Subsingleton V := .in

中文:
定理 rank_eq_one_iff
  条件: [Module.Free K V]
  证明: by
  have := nontrivial_of_invariantBasisNumber K
  refine ⟨fun h => ?_, fun ⟨v₀, h, hv⟩ => (rank_le_one_iff.2 ⟨v₀, hv⟩).antisymm ?_⟩
  · obtain ⟨v₀, hv⟩ := rank_le_one_iff.1 h.le
    refine ⟨v₀, fun hzero => ?_, hv⟩
    simp_rw [hzero, smul_zero, exists_const] at hv
    have : Subsingleton V := .in

Depends on / 依赖: Cardinal, Cardinal.lt_one_iff, Module, Module.Free.exists_basis, Subsingleton, antisymm, exists_basis, exists_const, h.le, lt_one_iff, mk_eq_zero_if, nontrivial_of_invariantBasisNumber, not_le, one_ne_zero, rank_le_one_iff, rank_subsingleton, simp_rw, smul_zero
-/
theorem rank_eq_one_iff [Module.Free K V] :
    Module.rank K V = 1 ↔ exists v₀ : V, v₀ != 0 ∧ forall v, exists r : K, r • v₀ = v := by
  have := nontrivial_of_invariantBasisNumber K
  refine ⟨fun h => ?_, fun ⟨v₀, h, hv⟩ => (rank_le_one_iff.2 ⟨v₀, hv⟩).antisymm ?_⟩
  · obtain ⟨v₀, hv⟩ := rank_le_one_iff.1 h.le
    refine ⟨v₀, fun hzero => ?_, hv⟩
    simp_rw [hzero, smul_zero, exists_const] at hv
    have : Subsingleton V := .intro fun _ _ => by simp_rw [← hv]
    exact one_ne_zero (h ▸ rank_subsingleton' K V)
  · by_contra H
    rw [not_le]; rw [Cardinal.lt_one_iff] at H
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    have := b.repr.toEquiv.subsingleton
    exact h (Subsingleton.elim _ _)

/--
theorem `rank_submodule_le_one_iff` / 定理 `rank_submodule_le_one_iff`

English:
theorem rank_submodule_le_one_iff
  given: (s : Submodule K V) [Module.Free K s]
  proof: by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  simp

中文:
定理 rank_submodule_le_one_iff
  条件: (s : Submodule K V) [Module.Free K s]
  证明: by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  simp

Depends on / 依赖: le_span_singleton_iff, rank_le_one_iff, simp_rw
-/
theorem rank_submodule_le_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s <= 1 ↔ exists v₀ in s, s <= K ∙ v₀ := by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  simp

/--
theorem `rank_submodule_eq_one_iff` / 定理 `rank_submodule_eq_one_iff`

English:
theorem rank_submodule_eq_one_iff
  given: (s : Submodule K V) [Module.Free K s]
  proof: by
  simp_rw [rank_eq_one_iff, le_span_singleton_iff]
  refine ⟨fun ⟨⟨v₀, hv₀⟩, H, h⟩ => ⟨v₀, hv₀, fun h' => by
    simp only [h', ne_eq] at H; exact H rfl, fun v hv => ?_⟩,
    fun ⟨v₀, hv₀, H, h⟩ => ⟨⟨v₀, hv₀⟩,
      fun h' => H (by rwa [AddSubmonoid.mk_eq_zero] at h'), fun ⟨v, hv⟩ => ?_⟩⟩
  · obt

中文:
定理 rank_submodule_eq_one_iff
  条件: (s : Submodule K V) [Module.Free K s]
  证明: by
  simp_rw [rank_eq_one_iff, le_span_singleton_iff]
  refine ⟨fun ⟨⟨v₀, hv₀⟩, H, h⟩ => ⟨v₀, hv₀, fun h' => by
    simp only [h', ne_eq] at H; exact H rfl, fun v hv => ?_⟩,
    fun ⟨v₀, hv₀, H, h⟩ => ⟨⟨v₀, hv₀⟩,
      fun h' => H (by rwa [AddSubmonoid.mk_eq_zero] at h'), fun ⟨v, hv⟩ => ?_⟩⟩
  · obt

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mk_eq_zero, Subtype, Subtype.ext_iff, coe_smul, ext_iff, le_span_singleton_iff, mk_eq_zero, ne_eq, rank_eq_one_iff, simp_rw
-/
theorem rank_submodule_eq_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s = 1 ↔ exists v₀ in s, v₀ != 0 ∧ s <= K ∙ v₀ := by
  simp_rw [rank_eq_one_iff, le_span_singleton_iff]
  refine ⟨fun ⟨⟨v₀, hv₀⟩, H, h⟩ => ⟨v₀, hv₀, fun h' => by
    simp only [h', ne_eq] at H; exact H rfl, fun v hv => ?_⟩,
    fun ⟨v₀, hv₀, H, h⟩ => ⟨⟨v₀, hv₀⟩,
      fun h' => H (by rwa [AddSubmonoid.mk_eq_zero] at h'), fun ⟨v, hv⟩ => ?_⟩⟩
  · obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul] at hr⟩
  · obtain ⟨r, hr⟩ := h v hv
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul]⟩

/--
theorem `rank_submodule_le_one_iff'` / 定理 `rank_submodule_le_one_iff'`

English:
theorem rank_submodule_le_one_iff'
  given: (s : Submodule K V) [Module.Free K s]
  proof: by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _

中文:
定理 rank_submodule_le_one_iff'
  条件: (s : Submodule K V) [Module.Free K s]
  证明: by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _

Depends on / 依赖: Module, Module.Free.exists_basis, b.linearIndependent.map, b.mk_eq_rank, cardinal_le_rank, cardinal_le_rank.trans, exists_basis, ker_inclusion, linearIndependent, mk_eq_rank, nontrivial_of_invariantBasisNumber, rank_span_le, rank_submodule_le_one_iff
-/
theorem rank_submodule_le_one_iff' (s : Submodule K V) [Module.Free K s] :
    Module.rank K s <= 1 ↔ exists v₀, s <= K ∙ v₀ := by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _ h)
.cardinal_le_rank.trans (rank_span_le {v₀})

/--
theorem `Submodule.rank_le_one_iff_isPrincipal` / 定理 `Submodule.rank_le_one_iff_isPrincipal`

English:
theorem Submodule.rank_le_one_iff_isPrincipal
  given: (W : Submodule K V) [Module.Free K W]
  proof: by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W -> V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, 

中文:
定理 Submodule.rank_le_one_iff_isPrincipal
  条件: (W : Submodule K V) [Module.Free K W]
  证明: by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W -> V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, 

Depends on / 依赖: Submodule, Submodule.isPrincipal_iff, Subtype, Subtype.ext, congr_arg, isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff, rank_le_one_iff, span_singleton_le_iff_mem
-/
theorem Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) [Module.Free K W] :
    Module.rank K W <= 1 ↔ W.IsPrincipal := by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W -> V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, ha⟩⟩
    choose f hf using h
    exact ⟨⟨a, ha⟩, fun v => ⟨f v.1 v.2, Subtype.ext (hf v.1 v.2)⟩⟩

/--
theorem `Module.rank_le_one_iff_top_isPrincipal` / 定理 `Module.rank_le_one_iff_top_isPrincipal`

English:
theorem Module.rank_le_one_iff_top_isPrincipal
  given: [Module.Free K V]
  proof: by
  have := Module.Free.of_equiv (topEquiv (R := K) (M := V)).symm
  rw [← Submodule.rank_le_one_iff_isPrincipal]; rw [rank_top]

中文:
定理 Module.rank_le_one_iff_top_isPrincipal
  条件: [Module.Free K V]
  证明: by
  have := Module.Free.of_equiv (topEquiv (R := K) (M := V)).symm
  rw [← Submodule.rank_le_one_iff_isPrincipal]; rw [rank_top]

Depends on / 依赖: Module, Module.Free.of_equiv, Submodule, Submodule.rank_le_one_iff_isPrincipal, of_equiv, rank_le_one_iff_isPrincipal, rank_top, topEquiv
-/
theorem Module.rank_le_one_iff_top_isPrincipal [Module.Free K V] :
    Module.rank K V <= 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  have := Module.Free.of_equiv (topEquiv (R := K) (M := V)).symm
  rw [← Submodule.rank_le_one_iff_isPrincipal]; rw [rank_top]

/--
theorem `finrank_eq_one_iff` / 定理 `finrank_eq_one_iff`

English:
theorem finrank_eq_one_iff
  given: [Module.Free K V] (ι : Type*) [Unique ι]
  proof: by
  constructor
  · intro h
    exact ⟨Module.basisUnique ι h⟩
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b

中文:
定理 finrank_eq_one_iff
  条件: [Module.Free K V] (ι : 类型) [Unique ι]
  证明: by
  constructor
  · intro h
    exact ⟨Module.basisUnique ι h⟩
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b

Depends on / 依赖: Module, Module.basisUnique, basisUnique, finrank_eq_card_basis
-/
theorem finrank_eq_one_iff [Module.Free K V] (ι : Type*) [Unique ι] :
    finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  constructor
  · intro h
    exact ⟨Module.basisUnique ι h⟩
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b

/--
theorem `finrank_eq_one_iff'` / 定理 `finrank_eq_one_iff'`

English:
theorem finrank_eq_one_iff'
  given: [Module.Free K V]
  proof: by
  rw [← rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

中文:
定理 finrank_eq_one_iff'
  条件: [Module.Free K V]
  证明: by
  rw [← rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

Depends on / 依赖: one_ne_zero, rank_eq_one_iff, toNat_eq_iff
-/
theorem finrank_eq_one_iff' [Module.Free K V] :
    finrank K V = 1 ↔ exists v != 0, forall w : V, exists c : K, c • v = w := by
  rw [← rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

/--
theorem `finrank_le_one_iff` / 定理 `finrank_le_one_iff`

English:
theorem finrank_le_one_iff
  given: [Module.Free K V] [Module.Finite K V]
  proof: by
  rw [← rank_le_one_iff]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

中文:
定理 finrank_le_one_iff
  条件: [Module.Free K V] [Module.Finite K V]
  证明: by
  rw [← rank_le_one_iff]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

Depends on / 依赖: Nat.cast_le_one, cast_le_one, finrank_eq_rank, rank_le_one_iff
-/
theorem finrank_le_one_iff [Module.Free K V] [Module.Finite K V] :
    finrank K V <= 1 ↔ exists v : V, forall w : V, exists c : K, c • v = w := by
  rw [← rank_le_one_iff]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

/--
theorem `Submodule.finrank_le_one_iff_isPrincipal` / 定理 `Submodule.finrank_le_one_iff_isPrincipal`

English:
theorem Submodule.finrank_le_one_iff_isPrincipal
  proof: by
  rw [← W.rank_le_one_iff_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

中文:
定理 Submodule.finrank_le_one_iff_isPrincipal
  证明: by
  rw [← W.rank_le_one_iff_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

Depends on / 依赖: Nat.cast_le_one, W.rank_le_one_iff_isPrincipal, cast_le_one, finrank_eq_rank, rank_le_one_iff_isPrincipal
-/
theorem Submodule.finrank_le_one_iff_isPrincipal
    (W : Submodule K V) [Module.Free K W] [Module.Finite K W] :
    finrank K W <= 1 ↔ W.IsPrincipal := by
  rw [← W.rank_le_one_iff_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

/--
theorem `Module.finrank_le_one_iff_top_isPrincipal` / 定理 `Module.finrank_le_one_iff_top_isPrincipal`

English:
theorem Module.finrank_le_one_iff_top_isPrincipal
  given: [Module.Free K V] [Module.Finite K V]
  proof: by
  rw [← Module.rank_le_one_iff_top_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

中文:
定理 Module.finrank_le_one_iff_top_isPrincipal
  条件: [Module.Free K V] [Module.Finite K V]
  证明: by
  rw [← Module.rank_le_one_iff_top_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

Depends on / 依赖: Module, Module.rank_le_one_iff_top_isPrincipal, Nat.cast_le_one, cast_le_one, finrank_eq_rank, rank_le_one_iff_top_isPrincipal
-/
theorem Module.finrank_le_one_iff_top_isPrincipal [Module.Free K V] [Module.Finite K V] :
    finrank K V <= 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Module.rank_le_one_iff_top_isPrincipal]; rw [← finrank_eq_rank]; rw [Nat.cast_le_one]

variable (K V) in
/--
theorem `lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank` / 定理 `lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank`

English:
theorem lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank
  statement: [Module.Free K V]
  proof: by
  have := nontrivial_of_invariantBasisNumber K
  obtain ⟨s, hs⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- `Module.Finite.finite_basis` is in a much later file, so we copy its proof to here
  have : Finite s := by
    obtain ⟨t, ht⟩ := ‹Module.Finite K V›
    exact basis_finite_of_finite_

中文:
定理 lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank
  结论: [Module.Free K V]
  证明: by
  have := nontrivial_of_invariantBasisNumber K
  obtain ⟨s, hs⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- `Module.Finite.finite_basis` is in a much later file, so we copy its proof to here
  have : Finite s := by
    obtain ⟨t, ht⟩ := ‹Module.Finite K V›
    exact basis_finite_of_finite_

Depends on / 依赖: Module, Module.Free.exists_basis, aestronglyMeasurable, exists_basis, hf.add, hf.aestronglyMeasurable.add, hg.aestronglyMeasurable, nontrivial_of_invariantBasisNumber
-/
theorem lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank [Module.Free K V]
    [Module.Finite K V] : lift.{u} #V = lift.{v} #K ^ lift.{u} (Module.rank K V) := by
  have := nontrivial_of_invariantBasisNumber K
  obtain ⟨s, hs⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- `Module.Finite.finite_basis` is in a much later file, so we copy its proof to here
  have : Finite s := by
    obtain ⟨t, ht⟩ := ‹Module.Finite K V›
    exact basis_finite_of_finite_spans t.finite_toSet ht hs
  have := lift_mk_eq'.2 ⟨hs.repr.toEquiv⟩
  rwa [Finsupp.equivFunOnFinite.cardinal_eq, mk_arrow, hs.mk_eq_rank'', lift_power, lift_lift,
    lift_lift, lift_umax] at this

/--
theorem `cardinalMk_eq_cardinalMk_field_pow_rank` / 定理 `cardinalMk_eq_cardinalMk_field_pow_rank`

English:
theorem cardinalMk_eq_cardinalMk_field_pow_rank
  statement: (K V : Type u) [Ring K] [StrongRankCondition K]
  proof: by
  simpa using lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V

中文:
定理 cardinalMk_eq_cardinalMk_field_pow_rank
  结论: (K V : 类型u) [Ring K] [StrongRankCondition K]
  证明: by
  simpa using lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V

Depends on / 依赖: lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank
-/
theorem cardinalMk_eq_cardinalMk_field_pow_rank (K V : Type u) [Ring K] [StrongRankCondition K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V] :
    #V = #K ^ Module.rank K V := by
  simpa using lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V

variable (K V) in
/--
theorem `cardinal_lt_aleph0_of_finiteDimensional` / 定理 `cardinal_lt_aleph0_of_finiteDimensional`

English:
theorem cardinal_lt_aleph0_of_finiteDimensional
  given: [Finite K] [Module.Free K V] [Module.Finite K V]
  proof: by
  rw [← lift_lt_aleph0.{v]; rw [u}]; rw [lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  exact power_lt_aleph0 (lift_lt_aleph0.2 (lt_aleph0_of_finite K))
    (lift_lt_aleph0.2 (rank_lt_aleph0 K V))

中文:
定理 cardinal_lt_aleph0_of_finiteDimensional
  条件: [Finite K] [Module.Free K V] [Module.Finite K V]
  证明: by
  rw [← lift_lt_aleph0.{v]; rw [u}]; rw [lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  exact power_lt_aleph0 (lift_lt_aleph0.2 (lt_aleph0_of_finite K))
    (lift_lt_aleph0.2 (rank_lt_aleph0 K V))

Depends on / 依赖: lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank, lift_lt_aleph0, lt_aleph0_of_finite, power_lt_aleph0, rank_lt_aleph0
-/
theorem cardinal_lt_aleph0_of_finiteDimensional [Finite K] [Module.Free K V] [Module.Finite K V] :
    #V < ℵ₀ := by
  rw [← lift_lt_aleph0.{v]; rw [u}]; rw [lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  exact power_lt_aleph0 (lift_lt_aleph0.2 (lt_aleph0_of_finite K))
    (lift_lt_aleph0.2 (rank_lt_aleph0 K V))

end Module

namespace Subalgebra

variable {F E : Type*} [CommRing F] [StrongRankCondition F] [Ring E] [Algebra F E]
  {S : Subalgebra F E}

/--
theorem `eq_bot_of_rank_le_one` / 定理 `eq_bot_of_rank_le_one`

English:
theorem eq_bot_of_rank_le_one
  given: (h : Module.rank F S <= 1) [Module.Free F S]
  statement: S = ⊥
  proof: by
  nontriviality E
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := S)
  by_cases h1 : Module.rank F S = 1
  · refine bot_unique fun x hx => Algebra.mem_bot.2 ?_
    rw [← b.mk_eq_rank'']; rw [eq_one_iff_unique]; rw [← unique_iff_subsingleton_and_nonempty] at h1
    obtain ⟨h1⟩ := h1
   

中文:
定理 eq_bot_of_rank_le_one
  条件: (h : Module.rank F S <= 1) [Module.Free F S]
  结论: S = ⊥
  证明: by
  nontriviality E
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := S)
  by_cases h1 : Module.rank F S = 1
  · refine bot_unique fun x hx => Algebra.mem_bot.2 ?_
    rw [← b.mk_eq_rank'']; rw [eq_one_iff_unique]; rw [← unique_iff_subsingleton_and_nonempty] at h1
    obtain ⟨h1⟩ := h1
   

Depends on / 依赖: Algebra, Algebra.mem_bot, Finsupp, Finsupp.uniqueLinearEquiv, Module, Module.Free.exists_basis, Module.rank, Subtype, Subtype.val, b.mk_eq_rank, b.repr, bijective_algebraMap_of_linearEquiv, bot_unique, eq_one_iff_unique, exists_basis, mem_bot, mk_eq_rank, mk_eq_zero_iff, nontriviality, surjective
-/
theorem eq_bot_of_rank_le_one (h : Module.rank F S <= 1) [Module.Free F S] : S = ⊥ := by
  nontriviality E
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := S)
  by_cases h1 : Module.rank F S = 1
  · refine bot_unique fun x hx => Algebra.mem_bot.2 ?_
    rw [← b.mk_eq_rank'']; rw [eq_one_iff_unique]; rw [← unique_iff_subsingleton_and_nonempty] at h1
    obtain ⟨h1⟩ := h1
    obtain ⟨y, hy⟩ := (bijective_algebraMap_of_linearEquiv (b.repr ≪≫ₗ
      Finsupp.uniqueLinearEquiv _ _ default).symm).surjective ⟨x, hx⟩
    exact ⟨y, congr(Subtype.val $(hy))⟩
  have := mk_eq_zero_iff.1 (b.mk_eq_rank''.symm ▸ Cardinal.lt_one_iff.1 (h.lt_of_ne h1))
  have := b.repr.toEquiv.subsingleton
exact False.elim one_ne_zero congr(S.val $(Subsingleton.elim 1 0))

/--
theorem `eq_bot_of_finrank_one` / 定理 `eq_bot_of_finrank_one`

English:
theorem eq_bot_of_finrank_one
  given: (h : finrank F S = 1) [Module.Free F S]
  statement: S = ⊥
  proof: by
  refine Subalgebra.eq_bot_of_rank_le_one ?_
  rw [finrank]; rw [toNat_eq_one] at h
  rw [h]

@[simp]

中文:
定理 eq_bot_of_finrank_one
  条件: (h : finrank F S = 1) [Module.Free F S]
  结论: S = ⊥
  证明: by
  refine Subalgebra.eq_bot_of_rank_le_one ?_
  rw [finrank]; rw [toNat_eq_one] at h
  rw [h]

@[simp]

Depends on / 依赖: Subalgebra, Subalgebra.eq_bot_of_rank_le_one, aestronglyMeasurable, eq_bot_of_rank_le_one, finrank, fun_prop, hf.aestronglyMeasurable.neg, toNat_eq_one
-/
theorem eq_bot_of_finrank_one (h : finrank F S = 1) [Module.Free F S] : S = ⊥ := by
  refine Subalgebra.eq_bot_of_rank_le_one ?_
  rw [finrank]; rw [toNat_eq_one] at h
  rw [h]

@[simp]
/--
theorem `rank_eq_one_iff` / 定理 `rank_eq_one_iff`

English:
theorem rank_eq_one_iff
  given: [Nontrivial E] [Module.Free F S]
  statement: Module.rank F S = 1 ↔ S = ⊥
  proof: by
  refine ⟨fun h => Subalgebra.eq_bot_of_rank_le_one h.le, ?_⟩
  rintro rfl
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := (⊥ : Subalgebra F E))
  refine le_antisymm ?_ ?_
  · have := lift_rank_range_le (Algebra.linearMap F E)
    rwa [← one_eq_range, rank_self, lift_one, lift_le_one_i

中文:
定理 rank_eq_one_iff
  条件: [Nontrivial E] [Module.Free F S]
  结论: Module.rank F S = 1 ↔ S = ⊥
  证明: by
  refine ⟨fun h => Subalgebra.eq_bot_of_rank_le_one h.le, ?_⟩
  rintro rfl
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := (⊥ : Subalgebra F E))
  refine le_antisymm ?_ ?_
  · have := lift_rank_range_le (Algebra.linearMap F E)
    rwa [← one_eq_range, rank_self, lift_one, lift_le_one_i

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.toSubmodule_bot, Cardinal, Cardinal.lt_one_iff, Module, Module.Free.exists_basis, Subalgebra, Subalgebra.eq_bot_of_rank_le_one, b.mk_eq_rank, b.repr.toEquiv.subsingleton, eq_bot_of_rank_le_one, exists_basis, h.le, le_antisymm, lift_le_one_iff, lift_one, lift_rank_range_le, linearMap, lt_one_iff
-/
theorem rank_eq_one_iff [Nontrivial E] [Module.Free F S] : Module.rank F S = 1 ↔ S = ⊥ := by
  refine ⟨fun h => Subalgebra.eq_bot_of_rank_le_one h.le, ?_⟩
  rintro rfl
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := (⊥ : Subalgebra F E))
  refine le_antisymm ?_ ?_
  · have := lift_rank_range_le (Algebra.linearMap F E)
    rwa [← one_eq_range, rank_self, lift_one, lift_le_one_iff,
      ← Algebra.toSubmodule_bot, rank_toSubmodule] at this
  · by_contra H
    rw [not_le]; rw [Cardinal.lt_one_iff] at H
    have := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    have := b.repr.toEquiv.subsingleton
    exact one_ne_zero congr((⊥ : Subalgebra F E).val $(Subsingleton.elim 1 0))

@[simp]
/--
theorem `finrank_eq_one_iff` / 定理 `finrank_eq_one_iff`

English:
theorem finrank_eq_one_iff
  given: [Nontrivial E] [Module.Free F S]
  statement: finrank F S = 1 ↔ S = ⊥
  proof: by
  rw [← Subalgebra.rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

中文:
定理 finrank_eq_one_iff
  条件: [Nontrivial E] [Module.Free F S]
  结论: finrank F S = 1 ↔ S = ⊥
  证明: by
  rw [← Subalgebra.rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

Depends on / 依赖: Subalgebra, Subalgebra.rank_eq_one_iff, one_ne_zero, rank_eq_one_iff, toNat_eq_iff
-/
theorem finrank_eq_one_iff [Nontrivial E] [Module.Free F S] : finrank F S = 1 ↔ S = ⊥ := by
  rw [← Subalgebra.rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

/--
theorem `bot_eq_top_iff_rank_eq_one` / 定理 `bot_eq_top_iff_rank_eq_one`

English:
theorem bot_eq_top_iff_rank_eq_one
  given: [Nontrivial E] [Module.Free F E]
  proof: by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← rank_top]; rw [Subalgebra.rank_eq_one_iff]; rw [eq_comm]

中文:
定理 bot_eq_top_iff_rank_eq_one
  条件: [Nontrivial E] [Module.Free F E]
  证明: by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← rank_top]; rw [Subalgebra.rank_eq_one_iff]; rw [eq_comm]

Depends on / 依赖: Module, Module.Free.of_equiv, Subalgebra, Subalgebra.rank_eq_one_iff, Subalgebra.topEquiv, eq_comm, of_equiv, rank_eq_one_iff, rank_top, toLinearEquiv, toLinearEquiv.symm, topEquiv
-/
theorem bot_eq_top_iff_rank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1 := by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← rank_top]; rw [Subalgebra.rank_eq_one_iff]; rw [eq_comm]

/--
theorem `bot_eq_top_iff_finrank_eq_one` / 定理 `bot_eq_top_iff_finrank_eq_one`

English:
theorem bot_eq_top_iff_finrank_eq_one
  given: [Nontrivial E] [Module.Free F E]
  proof: by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← finrank_top]; rw [← subalgebra_top_finrank_eq_submodule_top_finrank]; rw [Subalgebra.finrank_eq_one_iff]; rw [eq_comm]

alias ⟨_, bot_eq_top_of_rank_eq_one⟩ := bot_eq_top_iff_rank_eq_one

alias ⟨_, b

中文:
定理 bot_eq_top_iff_finrank_eq_one
  条件: [Nontrivial E] [Module.Free F E]
  证明: by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← finrank_top]; rw [← subalgebra_top_finrank_eq_submodule_top_finrank]; rw [Subalgebra.finrank_eq_one_iff]; rw [eq_comm]

alias ⟨_, bot_eq_top_of_rank_eq_one⟩ := bot_eq_top_iff_rank_eq_one

alias ⟨_, b

Depends on / 依赖: Module, Module.Free.of_equiv, Subalgebra, Subalgebra.finrank_eq_one_iff, Subalgebra.topEquiv, eq_comm, finrank_eq_one_iff, finrank_top, of_equiv, subalgebra_top_finrank_eq_submodule_top_finrank, toLinearEquiv, toLinearEquiv.symm, topEquiv
-/
theorem bot_eq_top_iff_finrank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1 := by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← finrank_top]; rw [← subalgebra_top_finrank_eq_submodule_top_finrank]; rw [Subalgebra.finrank_eq_one_iff]; rw [eq_comm]

alias ⟨_, bot_eq_top_of_rank_eq_one⟩ := bot_eq_top_iff_rank_eq_one

alias ⟨_, bot_eq_top_of_finrank_eq_one⟩ := bot_eq_top_iff_finrank_eq_one

attribute [simp] bot_eq_top_of_finrank_eq_one bot_eq_top_of_rank_eq_one

/--
lemma `_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap` / 引理 `_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap`

English:
lemma _root_.Algebra.finrank_eq_one_iff_bijective_algebraMap
  given: [Module.Free F E]
  proof: by
  refine ⟨?_, Module.finrank_of_bijective_algebraMap⟩
  nontriviality E
  refine fun h => ⟨FaithfulSMul.algebraMap_injective F E, ?_⟩
  rwa [Algebra.surjective_algebraMap_iff, eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one]

中文:
引理 _root_.Algebra.finrank_eq_one_iff_bijective_algebraMap
  条件: [Module.Free F E]
  证明: by
  refine ⟨?_, Module.finrank_of_bijective_algebraMap⟩
  nontriviality E
  refine fun h => ⟨FaithfulSMul.algebraMap_injective F E, ?_⟩
  rwa [Algebra.surjective_algebraMap_iff, eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one]

Depends on / 依赖: Algebra, Algebra.surjective_algebraMap_iff, FaithfulSMul, FaithfulSMul.algebraMap_injective, Module, Module.finrank_of_bijective_algebraMap, Subalgebra, Subalgebra.bot_eq_top_iff_finrank_eq_one, algebraMap_injective, bot_eq_top_iff_finrank_eq_one, eq_comm, finrank_of_bijective_algebraMap, nontriviality, surjective_algebraMap_iff
-/
lemma _root_.Algebra.finrank_eq_one_iff_bijective_algebraMap [Module.Free F E] :
    Module.finrank F E = 1 ↔ Function.Bijective (algebraMap F E) := by
  refine ⟨?_, Module.finrank_of_bijective_algebraMap⟩
  nontriviality E
  refine fun h => ⟨FaithfulSMul.algebraMap_injective F E, ?_⟩
  rwa [Algebra.surjective_algebraMap_iff, eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one]

end Subalgebra
