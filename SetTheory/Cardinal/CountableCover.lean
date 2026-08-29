/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Map

/-!
# Cardinality of a set with a countable cover

Assume that a set `t` is eventually covered by a countable family of sets, all with
cardinality `≤ a`. Then `t` itself has cardinality at most `a`. This is proved in
`Cardinal.mk_subtype_le_of_countable_eventually_mem`.

Versions are also given when `t = univ`, and with `= a` instead of `≤ a`.
-/

public section

open Set Order Filter
open scoped Cardinal

namespace Cardinal

universe u v

/--
lemma `mk_subtype_le_of_countable_eventually_mem_aux` / 引理 `mk_subtype_le_of_countable_eventually_mem_aux`

English:
lemma mk_subtype_le_of_countable_eventually_mem_aux
  statement: {α ι : Type u} {a : Cardinal}
  proof: by
  rcases lt_or_ge a ℵ₀ with ha | ha
  /- case `a` finite. In this case, it suffices to show that any finite subset `s` of `t` has
  cardinality at most `a`. For this, we pick `i` such that `f i` contains all the points in `s`,
  and apply the assumption that the cardinality of `f i` is at most `a

中文:
引理 mk_subtype_le_of_countable_eventually_mem_aux
  结论: {α ι : 类型u} {a : 基数}
  证明: by
  rcases lt_or_ge a ℵ₀ with ha | ha
  /- case `a` finite. In this case, it suffices to show that any finite subset `s` of `t` has
  cardinality at most `a`. For this, we pick `i` such that `f i` contains all the points in `s`,
  and apply the assumption that the cardinality of `f i` is at most `a

Depends on / 依赖: lt_or_ge
-/
lemma mk_subtype_le_of_countable_eventually_mem_aux {α ι : Type u} {a : Cardinal}
    [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : forall x in t, forallᶠ i in l, x in f i)
    (h'f : forall i, #(f i) <= a) : #t <= a := by
  rcases lt_or_ge a ℵ₀ with ha | ha
  /- case `a` finite. In this case, it suffices to show that any finite subset `s` of `t` has
  cardinality at most `a`. For this, we pick `i` such that `f i` contains all the points in `s`,
  and apply the assumption that the cardinality of `f i` is at most `a`. -/
  · obtain ⟨n, rfl⟩ : exists (n : Nat), a = n := lt_aleph0.1 ha
    apply mk_le_iff_forall_finset_subset_card_le.2 (fun s hs => ?_)
    have A : forall x in s, forallᶠ i in l, x in f i := fun x hx => ht x (hs hx)
    have B : forallᶠ i in l, forall x in s, x in f i := (s.eventually_all).2 A
    rcases B.exists with ⟨i, hi⟩
    have : forall i, Fintype (f i) := fun i => (lt_aleph0_iff_fintype.1 ((h'f i).trans_lt ha)).some
    let u : Finset α := (f i).toFinset
    have I1 : s.card <= u.card := by
      have : s subseteq u := fun x hx => by simpa only [u, Set.mem_toFinset] using hi x hx
      exact Finset.card_le_card this
    have I2 : (u.card : Cardinal) <= n := by
      convert! h'f i; simp only [u, Set.toFinset_card, mk_fintype]
    exact I1.trans (Nat.cast_le.1 I2)
  -- case `a` infinite:
  · have : t subseteq ⋃ i, f i := by
      intro x hx
      obtain ⟨i, hi⟩ : exists i, x in f i := (ht x hx).exists
      exact mem_iUnion_of_mem i hi
    calc #t <= #(⋃ i, f i) := mk_le_mk_of_subset this
      _ <= sum (fun i => #(f i)) := mk_iUnion_le_sum_mk
      _ <= sum (fun _ => a) := sum_le_sum _ _ h'f
      _ = #ι * a := by simp
      _ <= ℵ₀ * a := by grw [mk_le_aleph0]
      _ = a := aleph0_mul_eq ha

/--
lemma `mk_subtype_le_of_countable_eventually_mem` / 引理 `mk_subtype_le_of_countable_eventually_mem`

English:
lemma mk_subtype_le_of_countable_eventually_mem
  statement: {α : Type u} {ι : Type v} {a : Cardinal}
  proof: by
  let g : ULift.{u, v} ι -> Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) <= Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l')

中文:
引理 mk_subtype_le_of_countable_eventually_mem
  结论: {α : 类型u} {ι : 类型v} {a : 基数}
  证明: by
  let g : ULift.{u, v} ι -> Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) <= Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l')

Depends on / 依赖: Cardinal, Cardinal.lift, Filter, Filter.map, Function, Function.comp_apply, ULift.down, ULift.up, comp_apply, eventually_map, i.down, mem_preimage, mk_subtype_le_of_countable_eventually_mem_aux
-/
lemma mk_subtype_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l]
    {t : Set α} (ht : forall x in t, forallᶠ i in l, x in f i)
    (h'f : forall i, #(f i) <= a) : #t <= a := by
  let g : ULift.{u, v} ι -> Set (ULift.{v, u} α) := (ULift.down ⁻¹' ·) ∘ f ∘ ULift.down
  suffices #(ULift.down.{v} ⁻¹' t) <= Cardinal.lift.{v, u} a by simpa
  let l' : Filter (ULift.{u} ι) := Filter.map ULift.up l
  apply mk_subtype_le_of_countable_eventually_mem_aux (ι := ULift.{u} ι) (l := l') (f := g)
  · intro x hx
    simpa only [Function.comp_apply, mem_preimage, eventually_map] using! ht _ hx
  · intro i
    simpa [g] using! h'f i.down

/--
lemma `mk_le_of_countable_eventually_mem` / 引理 `mk_le_of_countable_eventually_mem`

English:
lemma mk_le_of_countable_eventually_mem
  statement: {α : Type u} {ι : Type v} {a : Cardinal}
  proof: by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ => ht x) h'f

中文:
引理 mk_le_of_countable_eventually_mem
  结论: {α : 类型u} {ι : 类型v} {a : 基数}
  证明: by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ => ht x) h'f

Depends on / 依赖: mk_subtype_le_of_countable_eventually_mem, mk_univ
-/
lemma mk_le_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] (ht : forall x, forallᶠ i in l, x in f i)
    (h'f : forall i, #(f i) <= a) : #α <= a := by
  rw [← mk_univ]
  exact mk_subtype_le_of_countable_eventually_mem (l := l) (fun x _ => ht x) h'f

/--
lemma `mk_of_countable_eventually_mem` / 引理 `mk_of_countable_eventually_mem`

English:
lemma mk_of_countable_eventually_mem
  statement: {α : Type u} {ι : Type v} {a : Cardinal}
  proof: by
  apply le_antisymm
  · apply mk_le_of_countable_eventually_mem ht (fun i => (h'f i).le)
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    rw [← (h'f i)]
    exact mk_set_le (f i)

中文:
引理 mk_of_countable_eventually_mem
  结论: {α : 类型u} {ι : 类型v} {a : 基数}
  证明: by
  apply le_antisymm
  · apply mk_le_of_countable_eventually_mem ht (fun i => (h'f i).le)
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    rw [← (h'f i)]
    exact mk_set_le (f i)

Depends on / 依赖: Nonempty, le_antisymm, mk_le_of_countable_eventually_mem, mk_set_le, nonempty_of_neBot
-/
lemma mk_of_countable_eventually_mem {α : Type u} {ι : Type v} {a : Cardinal}
    [Countable ι] {f : ι -> Set α} {l : Filter ι} [NeBot l] (ht : forall x, forallᶠ i in l, x in f i)
    (h'f : forall i, #(f i) = a) : #α = a := by
  apply le_antisymm
  · apply mk_le_of_countable_eventually_mem ht (fun i => (h'f i).le)
  · obtain ⟨i⟩ : Nonempty ι := nonempty_of_neBot l
    rw [← (h'f i)]
    exact mk_set_le (f i)

end Cardinal
