/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Order.Filter.ListTraverse
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Data.Vector.Basic

/-!
# Topology on lists and vectors

-/

@[expose] public section


open TopologicalSpace Set Filter

open Topology

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (List α)
  body: TopologicalSpace.mkOfNhds (traverse nhds)

中文:
实例 :
  签名: TopologicalSpace (List α)
  定义体: TopologicalSpace.mkOfNhds (traverse nhds)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.mkOfNhds, mkOfNhds, traverse
-/
instance : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)

/--
theorem `nhds_list` / 定理 `nhds_list`

English:
theorem nhds_list
  given: (as : List α)
  statement: 𝓝 as = traverse 𝓝 as
  proof: by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
suffices List.cons < > pure a <*> pure l <= List.cons < > 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using! this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_

中文:
定理 nhds_list
  条件: (as : List α)
  结论: 𝓝 as = traverse 𝓝 as
  证明: by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
suffices List.cons < > pure a <*> pure l <= List.cons < > 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using! this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_

Depends on / 依赖: Filter, Filter.map_mono, Filter.seq_mono, IsOpen, List.cons, functor_norm, generalizing, l.Forall, le_rfl, map_mono, mem_traverse_iff, nhds_mkOfNhds, pure_le_nhds, seq_mono, sequence, subseteq, traverse
-/
theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
suffices List.cons < > pure a <*> pure l <= List.cons < > 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using! this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
  · intro l s hs
    rcases (mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : exists v : List (Set α), l.Forall₂ (fun a s => IsOpen s ∧ a in s) v ∧ sequence v subseteq s := by
      induction hu generalizing s with
      | nil =>
        exists []
        simp only [List.forall₂_nil_left_iff]
        exact ⟨trivial, hus⟩
      | cons ht _ ih =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih _ Subset.rfl with ⟨v, hv, hvss⟩
        exact
          ⟨u::v, List.Forall₂.cons hu hv,
            Subset.trans (Set.seq_mono (Set.image_mono hut) hvss) hus⟩
    rcases this with ⟨v, hv, hvs⟩
    have : forallᶠ y in traverse 𝓝 l, y in sequence v :=
mem_traverse _ _ hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    refine Eventually.mono this fun u hu => ?_
    have hu := (List.mem_traverse _ _).1 hu
    have : List.Forall₂ (fun a s => IsOpen s ∧ a in s) u v := by
      refine List.Forall₂.flip ?_
      replace hv := hv.flip
      simp only [List.forall₂_and_left, Function.flip_def] at hv ⊢
      exact ⟨hv.1, hu.flip⟩
    grw [← hvs]
    exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)

@[simp]
/--
theorem `nhds_nil` / 定理 `nhds_nil`

English:
theorem nhds_nil
  statement: 𝓝 ([] : List α) = pure []
  proof: by
  rw [nhds_list]; rw [List.traverse_nil _]

中文:
定理 nhds_nil
  结论: 𝓝 ([] : List α) = pure []
  证明: by
  rw [nhds_list]; rw [List.traverse_nil _]

Depends on / 依赖: List.traverse_nil, nhds_list, traverse_nil
-/
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list]; rw [List.traverse_nil _]

/--
theorem `nhds_cons` / 定理 `nhds_cons`

English:
theorem nhds_cons
  given: (a : α) (l : List α)
  statement: 𝓝 (a::l) = List.cons < > 𝓝 a <*> 𝓝 l
  proof: by
  rw [nhds_list]; rw [List.traverse_cons _]; rw [← nhds_list]

中文:
定理 nhds_cons
  条件: (a : α) (l : List α)
  结论: 𝓝 (a::l) = List.cons < > 𝓝 a <*> 𝓝 l
  证明: by
  rw [nhds_list]; rw [List.traverse_cons _]; rw [← nhds_list]

Depends on / 依赖: List.traverse_cons, nhds_list, traverse_cons
-/
theorem nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons < > 𝓝 a <*> 𝓝 l := by
  rw [nhds_list]; rw [List.traverse_cons _]; rw [← nhds_list]

/--
theorem `List.tendsto_cons` / 定理 `List.tendsto_cons`

English:
theorem List.tendsto_cons
  given: {a : α} {l : List α}
  proof: by
  rw [nhds_cons]; rw [Tendsto]; rw [Filter.map_prod]; exact le_rfl

中文:
定理 List.tendsto_cons
  条件: {a : α} {l : List α}
  证明: by
  rw [nhds_cons]; rw [Tendsto]; rw [Filter.map_prod]; exact le_rfl

Depends on / 依赖: Filter, Filter.map_prod, Tendsto, le_rfl, map_prod, nhds_cons
-/
theorem List.tendsto_cons {a : α} {l : List α} :
    Tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a::l)) := by
  rw [nhds_cons]; rw [Tendsto]; rw [Filter.map_prod]; exact le_rfl

/--
theorem `Filter.Tendsto.cons` / 定理 `Filter.Tendsto.cons`

English:
theorem Filter.Tendsto.cons
  statement: {α : Type*} {f : α -> β} {g : α -> List β} {a : Filter α} {b : β}
  proof: List.tendsto_cons.comp (Tendsto.prodMk hf hg)

中文:
定理 Filter.Tendsto.cons
  结论: {α : 类型} {f : α -> β} {g : α -> List β} {a : Filter α} {b : β}
  证明: List.tendsto_cons.comp (Tendsto.prodMk hf hg)

Depends on / 依赖: List.tendsto_cons.comp, Tendsto, Tendsto.prodMk, prodMk, tendsto_cons
-/
theorem Filter.Tendsto.cons {α : Type*} {f : α -> β} {g : α -> List β} {a : Filter α} {b : β}
    {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) :
    Tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b::l)) :=
  List.tendsto_cons.comp (Tendsto.prodMk hf hg)

namespace List

/--
theorem `tendsto_cons_iff` / 定理 `tendsto_cons_iff`

English:
theorem tendsto_cons_iff
  given: {β : Type*} {f : List α -> β} {b : Filter β} {a : α} {l : List α}
  proof: by
  have : 𝓝 (a::l) = (𝓝 a ×ˢ 𝓝 l).map fun p : α × List α => p.1::p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.map_def, Function.comp_def, functor_norm]
  rw [this]; rw [Filter.tendsto_map'_iff]; rfl

中文:
定理 tendsto_cons_iff
  条件: {β : 类型} {f : List α -> β} {b : Filter β} {a : α} {l : List α}
  证明: by
  have : 𝓝 (a::l) = (𝓝 a ×ˢ 𝓝 l).map fun p : α × List α => p.1::p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.map_def, Function.comp_def, functor_norm]
  rw [this]; rw [Filter.tendsto_map'_iff]; rfl

Depends on / 依赖: Filter, Filter.map_def, Filter.prod_eq, Filter.seq_eq_filter_seq, Filter.tendsto_map, Function, Function.comp_def, _iff, comp_def, functor_norm, map_def, nhds_cons, prod_eq, seq_eq_filter_seq, tendsto_map
-/
theorem tendsto_cons_iff {β : Type*} {f : List α -> β} {b : Filter β} {a : α} {l : List α} :
    Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) b := by
  have : 𝓝 (a::l) = (𝓝 a ×ˢ 𝓝 l).map fun p : α × List α => p.1::p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.map_def, Function.comp_def, functor_norm]
  rw [this]; rw [Filter.tendsto_map'_iff]; rfl

/--
theorem `continuous_cons` / 定理 `continuous_cons`

English:
theorem continuous_cons
  statement: Continuous fun x : α × List α => (x.1::x.2 : List α)
  proof: continuous_iff_continuousAt.mpr fun ⟨_x, _y⟩ => continuousAt_fst.cons continuousAt_snd

中文:
定理 continuous_cons
  结论: Continuous fun x : α × List α => (x.1::x.2 : List α)
  证明: continuous_iff_continuousAt.mpr fun ⟨_x, _y⟩ => continuousAt_fst.cons continuousAt_snd

Depends on / 依赖: continuousAt_fst, continuousAt_fst.cons, continuousAt_snd, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem continuous_cons : Continuous fun x : α × List α => (x.1::x.2 : List α) :=
  continuous_iff_continuousAt.mpr fun ⟨_x, _y⟩ => continuousAt_fst.cons continuousAt_snd

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  statement: {β : Type*} {f : List α -> β} {r : List α -> Filter β}

中文:
定理 tendsto_nhds
  结论: {β : 类型} {f : List α -> β} {r : List α -> Filter β}
-/
theorem tendsto_nhds {β : Type*} {f : List α -> β} {r : List α -> Filter β}
    (h_nil : Tendsto f (pure []) (r []))
    (h_cons :
      forall l a,
        Tendsto f (𝓝 l) (r l) ->
          Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) (r (a::l))) :
    forall l, Tendsto f (𝓝 l) (r l)
  | [] => by rwa [nhds_nil]
  | a::l => by
    rw [tendsto_cons_iff]; exact h_cons l a (@tendsto_nhds _ _ _ h_nil h_cons l)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: α] : DiscreteTopology (List α)
  body: by
  rw [discreteTopology_iff_nhds]; intro l; induction l <;> simp [*, nhds_cons]

中文:
实例 [DiscreteTopology
  签名: α] : DiscreteTopology (List α)
  定义体: by
  rw [discreteTopology_iff_nhds]; intro l; induction l <;> simp [*, nhds_cons]

Depends on / 依赖: discreteTopology_iff_nhds, nhds_cons
-/
instance [DiscreteTopology α] : DiscreteTopology (List α) := by
  rw [discreteTopology_iff_nhds]; intro l; induction l <;> simp [*, nhds_cons]

/--
theorem `continuousAt_length` / 定理 `continuousAt_length`

English:
theorem continuousAt_length
  statement: forall l : List α, ContinuousAt List.length l
  proof: by
  simp only [ContinuousAt, nhds_discrete]
  refine tendsto_nhds ?_ ?_
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine Tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) ?_
    exact Tendsto.comp ih tendsto_snd

中文:
定理 continuousAt_length
  结论: 对任意 l : List α, ContinuousAt List.length l
  证明: by
  simp only [ContinuousAt, nhds_discrete]
  refine tendsto_nhds ?_ ?_
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine Tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) ?_
    exact Tendsto.comp ih tendsto_snd

Depends on / 依赖: ContinuousAt, List.length, Tendsto, Tendsto.comp, length, nhds_discrete, tendsto_nhds, tendsto_pure_pure, tendsto_snd
-/
theorem continuousAt_length : forall l : List α, ContinuousAt List.length l := by
  simp only [ContinuousAt, nhds_discrete]
  refine tendsto_nhds ?_ ?_
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine Tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) ?_
    exact Tendsto.comp ih tendsto_snd

/--
theorem `tendsto_insertIdx'` / 定理 `tendsto_insertIdx'`

English:
theorem tendsto_insertIdx'
  given: {a : α}
  proof: by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.map_def, Function.comp_def, functor_norm]
    rw [this]; rw [tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insertIdx' _ n l).comp <| tendsto_fst

中文:
定理 tendsto_insertIdx'
  条件: {a : α}
  证明: by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.map_def, Function.comp_def, functor_norm]
    rw [this]; rw [tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insertIdx' _ n l).comp <| tendsto_fst

Depends on / 依赖: Filter, Filter.map_def, Filter.prod_eq, Filter.seq_eq_filter_seq, Function, Function.comp_def, _iff, comp_def, functor_norm, map_def, nhds_cons, prodMk, prod_eq, seq_eq_filter_seq, tendsto_fst, tendsto_fst.comp, tendsto_fst.prodMk, tendsto_insertIdx, tendsto_map, tendsto_snd
-/
theorem tendsto_insertIdx' {a : α} :
    forall {n : Nat} {l : List α},
      Tendsto (fun p : α × List α => p.2.insertIdx n p.1) (𝓝 a ×ˢ 𝓝 l) (𝓝 (l.insertIdx n a))
  | 0, _ => tendsto_cons
  | n + 1, [] => by simp
  | n + 1, a'::l => by
    have : 𝓝 a ×ˢ 𝓝 (a'::l) =
        (𝓝 a ×ˢ (𝓝 a' ×ˢ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1::p.2.2) := by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.map_def, Function.comp_def, functor_norm]
    rw [this]; rw [tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insertIdx' _ n l).comp <| tendsto_fst.prodMk <| tendsto_snd.comp tendsto_snd)

/--
theorem `tendsto_insertIdx` / 定理 `tendsto_insertIdx`

English:
theorem tendsto_insertIdx
  statement: {β} {n : Nat} {a : α} {l : List α} {f : β -> α} {g : β -> List α}
  proof: tendsto_insertIdx'.comp (hf.prodMk hg)

中文:
定理 tendsto_insertIdx
  结论: {β} {n : 自然数} {a : α} {l : List α} {f : β -> α} {g : β -> List α}
  证明: tendsto_insertIdx'.comp (hf.prodMk hg)

Depends on / 依赖: hf.prodMk, prodMk, tendsto_insertIdx
-/
theorem tendsto_insertIdx {β} {n : Nat} {a : α} {l : List α} {f : β -> α} {g : β -> List α}
    {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) :
    Tendsto (fun b : β => (g b).insertIdx n (f b)) b (𝓝 (l.insertIdx n a)) :=
  tendsto_insertIdx'.comp (hf.prodMk hg)

/--
theorem `continuous_insertIdx` / 定理 `continuous_insertIdx`

English:
theorem continuous_insertIdx
  given: {n : Nat}
  statement: Continuous fun p : α × List α => p.2.insertIdx n p.1
  proof: continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx'

中文:
定理 continuous_insertIdx
  条件: {n : 自然数}
  结论: Continuous fun p : α × List α => p.2.insertIdx n p.1
  证明: continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx'

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, nhds_prod_eq, tendsto_insertIdx
-/
theorem continuous_insertIdx {n : Nat} : Continuous fun p : α × List α => p.2.insertIdx n p.1 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx'

/--
theorem `tendsto_eraseIdx` / 定理 `tendsto_eraseIdx`

English:
theorem tendsto_eraseIdx

中文:
定理 tendsto_eraseIdx
-/
theorem tendsto_eraseIdx :
    forall {n : Nat} {l : List α}, Tendsto (eraseIdx · n) (𝓝 l) (𝓝 (eraseIdx l n))
  | _, [] => by rw [nhds_nil]; exact tendsto_pure_nhds _ _
  | 0, a::l => by rw [tendsto_cons_iff]; exact tendsto_snd
  | n + 1, a::l => by
    rw [tendsto_cons_iff]
    dsimp [eraseIdx]
    exact tendsto_fst.cons ((@tendsto_eraseIdx n l).comp tendsto_snd)

/--
theorem `continuous_eraseIdx` / 定理 `continuous_eraseIdx`

English:
theorem continuous_eraseIdx
  given: {n : Nat}
  statement: Continuous fun l : List α => eraseIdx l n
  proof: continuous_iff_continuousAt.mpr fun _a => tendsto_eraseIdx

@[to_additive]

中文:
定理 continuous_eraseIdx
  条件: {n : 自然数}
  结论: Continuous fun l : List α => eraseIdx l n
  证明: continuous_iff_continuousAt.mpr fun _a => tendsto_eraseIdx

@[to_additive]

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, tendsto_eraseIdx
-/
theorem continuous_eraseIdx {n : Nat} : Continuous fun l : List α => eraseIdx l n :=
  continuous_iff_continuousAt.mpr fun _a => tendsto_eraseIdx

@[to_additive]
/--
theorem `tendsto_prod` / 定理 `tendsto_prod`

English:
theorem tendsto_prod
  given: [MulOneClass α] [ContinuousMul α] {l : List α}
  proof: by
  induction l with
  | nil => simp +contextual [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  | cons x l ih =>
    simp_rw [tendsto_cons_iff, prod_cons]
    have := continuous_iff_continuousAt.mp continuous_mul (x, l.prod)
    rw [ContinuousAt]; rw [nhds_prod_eq] at this
    exact this.comp (te

中文:
定理 tendsto_prod
  条件: [MulOneClass α] [ContinuousMul α] {l : List α}
  证明: by
  induction l with
  | nil => simp +contextual [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  | cons x l ih =>
    simp_rw [tendsto_cons_iff, prod_cons]
    have := continuous_iff_continuousAt.mp continuous_mul (x, l.prod)
    rw [ContinuousAt]; rw [nhds_prod_eq] at this
    exact this.comp (te

Depends on / 依赖: ContinuousAt, contextual, continuous_iff_continuousAt, continuous_iff_continuousAt.mp, continuous_mul, l.prod, mem_of_mem_nhds, nhds_nil, nhds_prod_eq, prodMap, prod_cons, simp_rw, tendsto_cons_iff, tendsto_id, tendsto_id.prodMap, tendsto_pure_left, this.comp
-/
theorem tendsto_prod [MulOneClass α] [ContinuousMul α] {l : List α} :
    Tendsto List.prod (𝓝 l) (𝓝 l.prod) := by
  induction l with
  | nil => simp +contextual [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  | cons x l ih =>
    simp_rw [tendsto_cons_iff, prod_cons]
    have := continuous_iff_continuousAt.mp continuous_mul (x, l.prod)
    rw [ContinuousAt]; rw [nhds_prod_eq] at this
    exact this.comp (tendsto_id.prodMap ih)

@[to_additive]
/--
theorem `continuous_prod` / 定理 `continuous_prod`

English:
theorem continuous_prod
  given: [MulOneClass α] [ContinuousMul α]
  statement: Continuous (prod : List α -> α)
  proof: continuous_iff_continuousAt.mpr fun _l => tendsto_prod

中文:
定理 continuous_prod
  条件: [MulOneClass α] [ContinuousMul α]
  结论: Continuous (prod : List α -> α)
  证明: continuous_iff_continuousAt.mpr fun _l => tendsto_prod

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, tendsto_prod
-/
theorem continuous_prod [MulOneClass α] [ContinuousMul α] : Continuous (prod : List α -> α) :=
  continuous_iff_continuousAt.mpr fun _l => tendsto_prod

end List

namespace List.Vector

instance (n : Nat) : TopologicalSpace (Vector α n) :=
inferInstanceAs TopologicalSpace (Subtype _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendsto_cons` / 定理 `tendsto_cons`

English:
theorem tendsto_cons
  given: {n : Nat} {a : α} {l : Vector α n}
  proof: by
  rw [tendsto_subtype_rng]; rw [Vector.cons_val]
  exact tendsto_fst.cons (Tendsto.comp continuousAt_subtype_val tendsto_snd)

中文:
定理 tendsto_cons
  条件: {n : 自然数} {a : α} {l : Vector α n}
  证明: by
  rw [tendsto_subtype_rng]; rw [Vector.cons_val]
  exact tendsto_fst.cons (Tendsto.comp continuousAt_subtype_val tendsto_snd)

Depends on / 依赖: Tendsto, Tendsto.comp, Vector, Vector.cons_val, cons_val, continuousAt_subtype_val, tendsto_fst, tendsto_fst.cons, tendsto_snd, tendsto_subtype_rng
-/
theorem tendsto_cons {n : Nat} {a : α} {l : Vector α n} :
    Tendsto (fun p : α × Vector α n => p.1 ::ᵥ p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a ::ᵥ l)) := by
  rw [tendsto_subtype_rng]; rw [Vector.cons_val]
  exact tendsto_fst.cons (Tendsto.comp continuousAt_subtype_val tendsto_snd)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tendsto_insertIdx` / 定理 `tendsto_insertIdx`

English:
theorem tendsto_insertIdx
  given: {n : Nat} {i : Fin (n + 1)} {a : α}

中文:
定理 tendsto_insertIdx
  条件: {n : 自然数} {i : Fin (n + 1)} {a : α}
-/
theorem tendsto_insertIdx {n : Nat} {i : Fin (n + 1)} {a : α} :
    forall {l : Vector α n},
      Tendsto (fun p : α × Vector α n => insertIdx p.1 i p.2) (𝓝 a ×ˢ 𝓝 l)
        (𝓝 (insertIdx a i l))
  | ⟨l, hl⟩ => by
    rw [insertIdx]; rw [tendsto_subtype_rng]
    simp only [insertIdx_val]
    exact List.tendsto_insertIdx tendsto_fst (Tendsto.comp continuousAt_subtype_val tendsto_snd : _)

/--
theorem `continuous_insertIdx'` / 定理 `continuous_insertIdx'`

English:
theorem continuous_insertIdx'
  given: {n : Nat} {i : Fin (n + 1)}
  proof: continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx

中文:
定理 continuous_insertIdx'
  条件: {n : 自然数} {i : Fin (n + 1)}
  证明: continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx

Depends on / 依赖: ContinuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, nhds_prod_eq, tendsto_insertIdx
-/
theorem continuous_insertIdx' {n : Nat} {i : Fin (n + 1)} :
    Continuous fun p : α × Vector α n => Vector.insertIdx p.1 i p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt]; rw [nhds_prod_eq]; exact tendsto_insertIdx

/--
theorem `continuous_insertIdx` / 定理 `continuous_insertIdx`

English:
theorem continuous_insertIdx
  statement: {n : Nat} {i : Fin (n + 1)} {f : β -> α} {g : β -> Vector α n}
  proof: continuous_insertIdx'.comp (hf.prodMk hg)

中文:
定理 continuous_insertIdx
  结论: {n : 自然数} {i : Fin (n + 1)} {f : β -> α} {g : β -> Vector α n}
  证明: continuous_insertIdx'.comp (hf.prodMk hg)

Depends on / 依赖: continuous_insertIdx, hf.prodMk, prodMk
-/
theorem continuous_insertIdx {n : Nat} {i : Fin (n + 1)} {f : β -> α} {g : β -> Vector α n}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => Vector.insertIdx (f b) i (g b) :=
  continuous_insertIdx'.comp (hf.prodMk hg)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `continuousAt_eraseIdx` / 定理 `continuousAt_eraseIdx`

English:
theorem continuousAt_eraseIdx
  given: {n : Nat} {i : Fin (n + 1)}

中文:
定理 continuousAt_eraseIdx
  条件: {n : 自然数} {i : Fin (n + 1)}
-/
theorem continuousAt_eraseIdx {n : Nat} {i : Fin (n + 1)} :
    forall {l : Vector α (n + 1)}, ContinuousAt (Vector.eraseIdx i) l
  | ⟨l, hl⟩ => by
    rw [ContinuousAt]; rw [Vector.eraseIdx]; rw [tendsto_subtype_rng]
    simp only [Vector.eraseIdx_val]
    exact Tendsto.comp List.tendsto_eraseIdx continuousAt_subtype_val

/--
theorem `continuous_eraseIdx` / 定理 `continuous_eraseIdx`

English:
theorem continuous_eraseIdx
  given: {n : Nat} {i : Fin (n + 1)}
  proof: continuous_iff_continuousAt.mpr fun ⟨_a, _l⟩ => continuousAt_eraseIdx

中文:
定理 continuous_eraseIdx
  条件: {n : 自然数} {i : Fin (n + 1)}
  证明: continuous_iff_continuousAt.mpr fun ⟨_a, _l⟩ => continuousAt_eraseIdx

Depends on / 依赖: continuousAt_eraseIdx, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr
-/
theorem continuous_eraseIdx {n : Nat} {i : Fin (n + 1)} :
    Continuous (Vector.eraseIdx i : Vector α (n + 1) -> Vector α n) :=
  continuous_iff_continuousAt.mpr fun ⟨_a, _l⟩ => continuousAt_eraseIdx

end List.Vector
