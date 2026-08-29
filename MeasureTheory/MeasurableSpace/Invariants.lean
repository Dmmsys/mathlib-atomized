/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
/-!
# σ-algebra of sets invariant under a self-map

In this file we define `MeasurableSpace.invariants (f : α → α)`
to be the σ-algebra of sets `s : Set α` such that
- `s` is measurable w.r.t. the canonical σ-algebra on `α`;
- and `f ⁻¹' s = s`.
-/

@[expose] public section

open Set Function
open scoped MeasureTheory

namespace MeasurableSpace

variable {α : Type*}

/-- Given a self-map `f : α → α`,
`invariants f` is the σ-algebra of measurable sets that are invariant under `f`.

A set `s` is `(invariants f)`-measurable
iff it is measurable w.r.t. the canonical σ-algebra on `α` and `f ⁻¹' s = s`. -/
@[instance_reducible]
/--
Definition of `invariants` / `invariants` 的定义

English:
definition invariants
  signature: [m : MeasurableSpace α] (f : α -> α)
  body: { m ⊓ ⟨fun s => f ⁻¹' s = s, by simp, by simp, fun f hf => by simp [hf]⟩ with
    MeasurableSet' := fun s => MeasurableSet[m] s ∧ f ⁻¹' s = s }

中文:
定义 invariants
  签名: [m : MeasurableSpace α] (f : α -> α)
  定义体: { m ⊓ ⟨fun s => f ⁻¹' s = s, by simp, by simp, fun f hf => by simp [hf]⟩ with
    MeasurableSet' := fun s => MeasurableSet[m] s ∧ f ⁻¹' s = s }

Depends on / 依赖: MeasurableSet
-/
def invariants [m : MeasurableSpace α] (f : α -> α) : MeasurableSpace α :=
  { m ⊓ ⟨fun s => f ⁻¹' s = s, by simp, by simp, fun f hf => by simp [hf]⟩ with
    MeasurableSet' := fun s => MeasurableSet[m] s ∧ f ⁻¹' s = s }

variable [MeasurableSpace α]

/--
theorem `measurableSet_invariants` / 定理 `measurableSet_invariants`

English:
theorem measurableSet_invariants
  given: {f : α -> α} {s : Set α}
  proof: .rfl

@[simp]

中文:
定理 measurableSet_invariants
  条件: {f : α -> α} {s : Set α}
  证明: .rfl

@[simp]
-/
theorem measurableSet_invariants {f : α -> α} {s : Set α} :
    MeasurableSet[invariants f] s ↔ MeasurableSet s ∧ f ⁻¹' s = s :=
  .rfl

@[simp]
/--
theorem `invariants_id` / 定理 `invariants_id`

English:
theorem invariants_id
  statement: invariants (id : α -> α) = ‹MeasurableSpace α›
  proof: ext fun _ => ⟨And.left, fun h => ⟨h, rfl⟩⟩

中文:
定理 invariants_id
  结论: invariants (id : α -> α) = ‹MeasurableSpace α›
  证明: ext fun _ => ⟨And.left, fun h => ⟨h, rfl⟩⟩

Depends on / 依赖: And.left
-/
theorem invariants_id : invariants (id : α -> α) = ‹MeasurableSpace α› :=
  ext fun _ => ⟨And.left, fun h => ⟨h, rfl⟩⟩

/--
theorem `invariants_le` / 定理 `invariants_le`

English:
theorem invariants_le
  given: (f : α -> α)
  statement: invariants f <= ‹MeasurableSpace α›
  proof: fun _ => And.left

中文:
定理 invariants_le
  条件: (f : α -> α)
  结论: invariants f <= ‹MeasurableSpace α›
  证明: fun _ => And.left

Depends on / 依赖: And.left
-/
theorem invariants_le (f : α -> α) : invariants f <= ‹MeasurableSpace α› := fun _ => And.left

/--
theorem `inf_le_invariants_comp` / 定理 `inf_le_invariants_comp`

English:
theorem inf_le_invariants_comp
  given: (f g : α -> α)
  proof: fun s hs =>
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩

中文:
定理 inf_le_invariants_comp
  条件: (f g : α -> α)
  证明: fun s hs =>
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩
-/
theorem inf_le_invariants_comp (f g : α -> α) :
    invariants f ⊓ invariants g <= invariants (f ∘ g) := fun s hs =>
  ⟨hs.1.1, by rw [preimage_comp, hs.1.2, hs.2.2]⟩

/--
theorem `le_invariants_iterate` / 定理 `le_invariants_iterate`

English:
theorem le_invariants_iterate
  given: (f : α -> α) (n : Nat)
  proof: by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

中文:
定理 le_invariants_iterate
  条件: (f : α -> α) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

Depends on / 依赖: inf_le_invariants_comp, invariants_le, le_inf, le_rfl, le_trans
-/
theorem le_invariants_iterate (f : α -> α) (n : Nat) :
    invariants f <= invariants (f^[n]) := by
  induction n with
  | zero => simp [invariants_le]
  | succ n ihn => exact le_trans (le_inf ihn le_rfl) (inf_le_invariants_comp _ _)

variable {β : Type*} [MeasurableSpace β]

/--
theorem `measurable_invariants_dom` / 定理 `measurable_invariants_dom`

English:
theorem measurable_invariants_dom
  given: {f : α -> α} {g : α -> β}
  proof: by
  simp only [Measurable, ← forall_and]; rfl

中文:
定理 measurable_invariants_dom
  条件: {f : α -> α} {g : α -> β}
  证明: by
  simp only [Measurable, ← forall_and]; rfl

Depends on / 依赖: Measurable, forall_and
-/
theorem measurable_invariants_dom {f : α -> α} {g : α -> β} :
    Measurable[invariants f] g ↔ Measurable g ∧ forall s, MeasurableSet s -> (g ∘ f) ⁻¹' s = g ⁻¹' s := by
  simp only [Measurable, ← forall_and]; rfl

/--
theorem `measurable_invariants_of_semiconj` / 定理 `measurable_invariants_of_semiconj`

English:
theorem measurable_invariants_of_semiconj
  statement: {fa : α -> α} {fb : β -> β} {g : α -> β} (hg : Measurable g)
  proof: fun s hs =>
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩

中文:
定理 measurable_invariants_of_semiconj
  结论: {fa : α -> α} {fb : β -> β} {g : α -> β} (hg : Measurable g)
  证明: fun s hs =>
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩
-/
theorem measurable_invariants_of_semiconj {fa : α -> α} {fb : β -> β} {g : α -> β} (hg : Measurable g)
    (hfg : Semiconj g fa fb) : @Measurable _ _ (invariants fa) (invariants fb) g := fun s hs =>
  ⟨hg hs.1, by rw [← preimage_comp, hfg.comp_eq, preimage_comp, hs.2]⟩

/--
theorem `comp_eq_of_measurable_invariants` / 定理 `comp_eq_of_measurable_invariants`

English:
theorem comp_eq_of_measurable_invariants
  statement: {f : α -> α} {g : α -> β} [MeasurableSingletonClass β]
  proof: by
  funext x
  suffices x in f ⁻¹' g ⁻¹' {g x} by simpa
  rw [(h <| measurableSet_singleton (g x)).2]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]

中文:
定理 comp_eq_of_measurable_invariants
  结论: {f : α -> α} {g : α -> β} [MeasurableSingletonClass β]
  证明: by
  funext x
  suffices x in f ⁻¹' g ⁻¹' {g x} by simpa
  rw [(h <| measurableSet_singleton (g x)).2]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]

Depends on / 依赖: Set.mem_preimage, Set.mem_singleton_iff, measurableSet_singleton, mem_preimage, mem_singleton_iff
-/
theorem comp_eq_of_measurable_invariants {f : α -> α} {g : α -> β} [MeasurableSingletonClass β]
    (h : Measurable[invariants f] g) : g ∘ f = g := by
  funext x
  suffices x in f ⁻¹' g ⁻¹' {g x} by simpa
  rw [(h <| measurableSet_singleton (g x)).2]; rw [Set.mem_preimage]; rw [Set.mem_singleton_iff]

end MeasurableSpace
