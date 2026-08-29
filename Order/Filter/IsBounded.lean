/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Filter.Cofinite

/-!
# Lemmas about `Is(Co)Bounded(Under)`

This file proves several lemmas about
`IsBounded`, `IsBoundedUnder`, `IsCobounded` and `IsCoboundedUnder`.
-/

public section

open Set Function

variable {α β γ ι : Type*}

namespace Filter

section Relation

variable {r : α -> α -> Prop} {f g : Filter α}

/--
theorem `isBounded_iff` / 定理 `isBounded_iff`

English:
theorem isBounded_iff
  statement: f.IsBounded r ↔ exists s in f.sets, exists b, s subseteq { x | r x b }
  proof: Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩

中文:
定理 isBounded_iff
  结论: f.IsBounded r ↔ 存在 s in f.sets, 存在 b, s subseteq { x | r x b }
  证明: Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩

Depends on / 依赖: Iff.intro, Subset, Subset.refl, mem_of_superset
-/
theorem isBounded_iff : f.IsBounded r ↔ exists s in f.sets, exists b, s subseteq { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩

/--
theorem `isBoundedUnder_of` / 定理 `isBoundedUnder_of`

English:
theorem isBoundedUnder_of
  given: {f : Filter β} {u : β -> α}
  statement: (exists b, forall x, r (u x) b) -> f.IsBoundedUnder r u

中文:
定理 isBoundedUnder_of
  条件: {f : Filter β} {u : β -> α}
  结论: (存在 b, 对任意 x, r (u x) b) -> f.IsBoundedUnder r u
-/
theorem isBoundedUnder_of {f : Filter β} {u : β -> α} : (exists b, forall x, r (u x) b) -> f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show forallᶠ x in f, r (u x) b from Eventually.of_forall hb⟩

/--
theorem `isBounded_bot` / 定理 `isBounded_bot`

English:
theorem isBounded_bot
  statement: IsBounded r ⊥ ↔ Nonempty α
  proof: by simp [IsBounded, exists_true_iff_nonempty]

中文:
定理 isBounded_bot
  结论: IsBounded r ⊥ ↔ Nonempty α
  证明: by simp [IsBounded, exists_true_iff_nonempty]

Depends on / 依赖: IsBounded, exists_true_iff_nonempty
-/
theorem isBounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [IsBounded, exists_true_iff_nonempty]

/--
theorem `isBounded_top` / 定理 `isBounded_top`

English:
theorem isBounded_top
  statement: IsBounded r ⊤ ↔ exists t, forall x, r x t
  proof: by simp [IsBounded]

中文:
定理 isBounded_top
  结论: IsBounded r ⊤ ↔ 存在 t, 对任意 x, r x t
  证明: by simp [IsBounded]

Depends on / 依赖: IsBounded
-/
theorem isBounded_top : IsBounded r ⊤ ↔ exists t, forall x, r x t := by simp [IsBounded]

/--
theorem `isBounded_principal` / 定理 `isBounded_principal`

English:
theorem isBounded_principal
  given: (s : Set α)
  statement: IsBounded r (𝓟 s) ↔ exists t, forall x in s, r x t
  proof: by
  simp [IsBounded]

中文:
定理 isBounded_principal
  条件: (s : Set α)
  结论: IsBounded r (𝓟 s) ↔ 存在 t, 对任意 x in s, r x t
  证明: by
  simp [IsBounded]

Depends on / 依赖: IsBounded
-/
theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ exists t, forall x in s, r x t := by
  simp [IsBounded]

/--
theorem `isBounded_sup` / 定理 `isBounded_sup`

English:
theorem isBounded_sup
  given: [IsTrans α r] [IsDirected α r]
  proof: directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩

中文:
定理 isBounded_sup
  条件: [IsTrans α r] [IsDirected α r]
  证明: directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩

Depends on / 依赖: directed_of
-/
theorem isBounded_sup [IsTrans α r] [IsDirected α r] :
    IsBounded r f -> IsBounded r g -> IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩

/--
theorem `IsBounded.mono` / 定理 `IsBounded.mono`

English:
theorem IsBounded.mono
  given: (h : f <= g)
  statement: IsBounded r g -> IsBounded r f

中文:
定理 IsBounded.mono
  条件: (h : f <= g)
  结论: IsBounded r g -> IsBounded r f
-/
theorem IsBounded.mono (h : f <= g) : IsBounded r g -> IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩

/--
theorem `IsBoundedUnder.mono` / 定理 `IsBoundedUnder.mono`

English:
theorem IsBoundedUnder.mono
  given: {f g : Filter β} {u : β -> α} (h : f <= g)
  proof: fun hg => IsBounded.mono (map_mono h) hg

@[to_dual mono_ge]

中文:
定理 IsBoundedUnder.mono
  条件: {f g : Filter β} {u : β -> α} (h : f <= g)
  证明: fun hg => IsBounded.mono (map_mono h) hg

@[to_dual mono_ge]

Depends on / 依赖: IsBounded, IsBounded.mono, map_mono
-/
theorem IsBoundedUnder.mono {f g : Filter β} {u : β -> α} (h : f <= g) :
    g.IsBoundedUnder r u -> f.IsBoundedUnder r u := fun hg => IsBounded.mono (map_mono h) hg

@[to_dual mono_ge]
/--
theorem `IsBoundedUnder.mono_le` / 定理 `IsBoundedUnder.mono_le`

English:
theorem IsBoundedUnder.mono_le
  statement: [Preorder β] {l : Filter α} {u v : α -> β}
  proof: by
  apply hu.imp
exact fun b hb => (eventually_map.1 hb).mp hv.mono fun x => le_trans

中文:
定理 IsBoundedUnder.mono_le
  结论: [Preorder β] {l : Filter α} {u v : α -> β}
  证明: by
  apply hu.imp
exact fun b hb => (eventually_map.1 hb).mp hv.mono fun x => le_trans

Depends on / 依赖: eventually_map, hu.imp, hv.mono, le_trans
-/
theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α -> β}
    (hu : IsBoundedUnder (· <= ·) l u) (hv : v <=ᶠ[l] u) : IsBoundedUnder (· <= ·) l v := by
  apply hu.imp
exact fun b hb => (eventually_map.1 hb).mp hv.mono fun x => le_trans

/--
theorem `isBoundedUnder_const` / 定理 `isBoundedUnder_const`

English:
theorem isBoundedUnder_const
  given: [Std.Refl r] {l : Filter β} {a : α}
  statement: IsBoundedUnder r l fun _ => a
  proof: ⟨a, eventually_map.2 Eventually.of_forall fun _ => refl _⟩

中文:
定理 isBoundedUnder_const
  条件: [Std.Refl r] {l : Filter β} {a : α}
  结论: IsBoundedUnder r l fun _ => a
  证明: ⟨a, eventually_map.2 Eventually.of_forall fun _ => refl _⟩

Depends on / 依赖: Eventually, Eventually.of_forall, eventually_map, of_forall
-/
theorem isBoundedUnder_const [Std.Refl r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
⟨a, eventually_map.2 Eventually.of_forall fun _ => refl _⟩

/--
theorem `IsBounded.isBoundedUnder` / 定理 `IsBounded.isBoundedUnder`

English:
theorem IsBounded.isBoundedUnder
  statement: {q : β -> β -> Prop} {u : α -> β}

中文:
定理 IsBounded.isBoundedUnder
  结论: {q : β -> β -> 命题} {u : α -> β}
-/
theorem IsBounded.isBoundedUnder {q : β -> β -> Prop} {u : α -> β}
    (hu : forall a₀ a₁, r a₀ a₁ -> q (u a₀) (u a₁)) : f.IsBounded r -> f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show forallᶠ x in f, q (u x) (u b) from h.mono fun x => hu x b⟩

/--
theorem `IsBoundedUnder.comp` / 定理 `IsBoundedUnder.comp`

English:
theorem IsBoundedUnder.comp
  statement: {l : Filter γ} {q : β -> β -> Prop} {u : γ -> α} {v : α -> β}

中文:
定理 IsBoundedUnder.comp
  结论: {l : Filter γ} {q : β -> β -> 命题} {u : γ -> α} {v : α -> β}
-/
theorem IsBoundedUnder.comp {l : Filter γ} {q : β -> β -> Prop} {u : γ -> α} {v : α -> β}
    (hv : forall a₀ a₁, r a₀ a₁ -> q (v a₀) (v a₁)) : l.IsBoundedUnder r u -> l.IsBoundedUnder q (v ∘ u)
  | ⟨a, h⟩ => ⟨v a, show forallᶠ x in map u l, q (v x) (v a) from h.mono fun x => hv x a⟩

/--
lemma `isBoundedUnder_map_iff` / 引理 `isBoundedUnder_map_iff`

English:
lemma isBoundedUnder_map_iff
  statement: {ι κ X : Type*} {r : X -> X -> Prop} {f : ι -> X} {φ : κ -> ι}
  proof: Iff.rfl

中文:
引理 isBoundedUnder_map_iff
  结论: {ι κ X : 类型} {r : X -> X -> 命题} {f : ι -> X} {φ : κ -> ι}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isBoundedUnder_map_iff {ι κ X : Type*} {r : X -> X -> Prop} {f : ι -> X} {φ : κ -> ι}
    {𝓕 : Filter κ} :
    (map φ 𝓕).IsBoundedUnder r f ↔ 𝓕.IsBoundedUnder r (f ∘ φ) :=
  Iff.rfl

/--
lemma `Tendsto.isBoundedUnder_comp` / 引理 `Tendsto.isBoundedUnder_comp`

English:
lemma Tendsto.isBoundedUnder_comp
  statement: {ι κ X : Type*} {r : X -> X -> Prop} {f : ι -> X} {φ : κ -> ι}
  proof: isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

中文:
引理 Tendsto.isBoundedUnder_comp
  结论: {ι κ X : 类型} {r : X -> X -> 命题} {f : ι -> X} {φ : κ -> ι}
  证明: isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

Depends on / 依赖: _bounded.mono, isBoundedUnder_map_iff, isBoundedUnder_map_iff.mp
-/
lemma Tendsto.isBoundedUnder_comp {ι κ X : Type*} {r : X -> X -> Prop} {f : ι -> X} {φ : κ -> ι}
    {𝓕 : Filter ι} {𝓖 : Filter κ} (φ_tendsto : Tendsto φ 𝓖 𝓕) (𝓕_bounded : 𝓕.IsBoundedUnder r f) :
    𝓖.IsBoundedUnder r (f ∘ φ) :=
  isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

section Preorder
variable [Preorder α] {f : Filter β} {u : β -> α} {s : Set β}

@[to_dual eventually_ge]
/--
lemma `IsBoundedUnder.eventually_le` / 引理 `IsBoundedUnder.eventually_le`

English:
lemma IsBoundedUnder.eventually_le
  given: (h : IsBoundedUnder (· <= ·) f u)
  proof: by
  tauto

@[to_dual isBoundedUnder_of_eventually_ge]

中文:
引理 IsBoundedUnder.eventually_le
  条件: (h : IsBoundedUnder (· <= ·) f u)
  证明: by
  tauto

@[to_dual isBoundedUnder_of_eventually_ge]
-/
lemma IsBoundedUnder.eventually_le (h : IsBoundedUnder (· <= ·) f u) :
    exists a, forallᶠ x in f, u x <= a := by
  tauto

@[to_dual isBoundedUnder_of_eventually_ge]
/--
lemma `isBoundedUnder_of_eventually_le` / 引理 `isBoundedUnder_of_eventually_le`

English:
lemma isBoundedUnder_of_eventually_le
  given: {a : α} (h : forallᶠ x in f, u x <= a)
  proof: ⟨a, h⟩

@[to_dual]

中文:
引理 isBoundedUnder_of_eventually_le
  条件: {a : α} (h : 对任意ᶠ x in f, u x <= a)
  证明: ⟨a, h⟩

@[to_dual]
-/
lemma isBoundedUnder_of_eventually_le {a : α} (h : forallᶠ x in f, u x <= a) :
    IsBoundedUnder (· <= ·) f u := ⟨a, h⟩

@[to_dual]
/--
lemma `isBoundedUnder_iff_eventually_bddAbove` / 引理 `isBoundedUnder_iff_eventually_bddAbove`

English:
lemma isBoundedUnder_iff_eventually_bddAbove
  proof: by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨{a | u a <= b}, ⟨b, by rintro _ ⟨a, ha, rfl⟩; exact ha⟩, hb⟩
  · rintro ⟨s, ⟨b, hb⟩, hs⟩
exact ⟨b, hs.mono by simpa [upperBounds] using hb⟩

@[to_dual]

中文:
引理 isBoundedUnder_iff_eventually_bddAbove
  证明: by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨{a | u a <= b}, ⟨b, by rintro _ ⟨a, ha, rfl⟩; exact ha⟩, hb⟩
  · rintro ⟨s, ⟨b, hb⟩, hs⟩
exact ⟨b, hs.mono by simpa [upperBounds] using hb⟩

@[to_dual]

Depends on / 依赖: hs.mono, upperBounds
-/
lemma isBoundedUnder_iff_eventually_bddAbove :
    f.IsBoundedUnder (· <= ·) u ↔ exists s, BddAbove (u '' s) ∧ forallᶠ x in f, x in s := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨{a | u a <= b}, ⟨b, by rintro _ ⟨a, ha, rfl⟩; exact ha⟩, hb⟩
  · rintro ⟨s, ⟨b, hb⟩, hs⟩
exact ⟨b, hs.mono by simpa [upperBounds] using hb⟩

@[to_dual]
/--
lemma `_root_.BddAbove.isBoundedUnder` / 引理 `_root_.BddAbove.isBoundedUnder`

English:
lemma _root_.BddAbove.isBoundedUnder
  given: (hs : s in f) (hu : BddAbove (u '' s))
  proof: isBoundedUnder_iff_eventually_bddAbove.2 ⟨_, hu, hs⟩

中文:
引理 _root_.BddAbove.isBoundedUnder
  条件: (hs : s in f) (hu : BddAbove (u '' s))
  证明: isBoundedUnder_iff_eventually_bddAbove.2 ⟨_, hu, hs⟩

Depends on / 依赖: isBoundedUnder_iff_eventually_bddAbove
-/
lemma _root_.BddAbove.isBoundedUnder (hs : s in f) (hu : BddAbove (u '' s)) :
    f.IsBoundedUnder (· <= ·) u := isBoundedUnder_iff_eventually_bddAbove.2 ⟨_, hu, hs⟩

/-- A bounded above function `u` is in particular eventually bounded above. -/
@[to_dual /-- A bounded below function `u` is in particular eventually bounded below. -/]
/--
lemma `_root_.BddAbove.isBoundedUnder_of_range` / 引理 `_root_.BddAbove.isBoundedUnder_of_range`

English:
lemma _root_.BddAbove.isBoundedUnder_of_range
  given: (hu : BddAbove (Set.range u))
  proof: BddAbove.isBoundedUnder (s := univ) f.univ_mem (by simpa)

@[to_dual ge_of_finite]

中文:
引理 _root_.BddAbove.isBoundedUnder_of_range
  条件: (hu : BddAbove (Set.range u))
  证明: BddAbove.isBoundedUnder (s := univ) f.univ_mem (by simpa)

@[to_dual ge_of_finite]

Depends on / 依赖: BddAbove, BddAbove.isBoundedUnder, f.univ_mem, isBoundedUnder, univ_mem
-/
lemma _root_.BddAbove.isBoundedUnder_of_range (hu : BddAbove (Set.range u)) :
    f.IsBoundedUnder (· <= ·) u := BddAbove.isBoundedUnder (s := univ) f.univ_mem (by simpa)

@[to_dual ge_of_finite]
/--
lemma `IsBoundedUnder.le_of_finite` / 引理 `IsBoundedUnder.le_of_finite`

English:
lemma IsBoundedUnder.le_of_finite
  statement: [Nonempty α] [IsDirectedOrder α] [Finite β]
  proof: (Set.toFinite _).bddAbove.isBoundedUnder_of_range

中文:
引理 IsBoundedUnder.le_of_finite
  结论: [Nonempty α] [IsDirectedOrder α] [Finite β]
  证明: (Set.toFinite _).bddAbove.isBoundedUnder_of_range

Depends on / 依赖: Set.toFinite, bddAbove, bddAbove.isBoundedUnder_of_range, isBoundedUnder_of_range, toFinite
-/
lemma IsBoundedUnder.le_of_finite [Nonempty α] [IsDirectedOrder α] [Finite β]
    {f : Filter β} {u : β -> α} : IsBoundedUnder (· <= ·) f u :=
  (Set.toFinite _).bddAbove.isBoundedUnder_of_range

end Preorder

@[to_dual isBoundedUnder_ge_comp]
/--
theorem `_root_.Monotone.isBoundedUnder_le_comp` / 定理 `_root_.Monotone.isBoundedUnder_le_comp`

English:
theorem _root_.Monotone.isBoundedUnder_le_comp
  statement: [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
  proof: hl.comp hv

@[to_dual isBoundedUnder_ge_comp]

中文:
定理 _root_.Monotone.isBoundedUnder_le_comp
  结论: [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
  证明: hl.comp hv

@[to_dual isBoundedUnder_ge_comp]

Depends on / 依赖: hl.comp
-/
theorem _root_.Monotone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
    {v : α -> β} (hv : Monotone v) (hl : l.IsBoundedUnder (· <= ·) u) :
    l.IsBoundedUnder (· <= ·) (v ∘ u) :=
  hl.comp hv

@[to_dual isBoundedUnder_ge_comp]
/--
theorem `_root_.Antitone.isBoundedUnder_le_comp` / 定理 `_root_.Antitone.isBoundedUnder_le_comp`

English:
theorem _root_.Antitone.isBoundedUnder_le_comp
  statement: [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
  proof: hl.comp (swap hv)

@[to_dual]

中文:
定理 _root_.Antitone.isBoundedUnder_le_comp
  结论: [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
  证明: hl.comp (swap hv)

@[to_dual]

Depends on / 依赖: hl.comp
-/
theorem _root_.Antitone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ -> α}
    {v : α -> β} (hv : Antitone v) (hl : l.IsBoundedUnder (fun x1 x2 => x2 <= x1) u) :
    l.IsBoundedUnder (· <= ·) (v ∘ u) :=
  hl.comp (swap hv)

@[to_dual]
/--
theorem `not_isBoundedUnder_of_tendsto_atTop` / 定理 `not_isBoundedUnder_of_tendsto_atTop`

English:
theorem not_isBoundedUnder_of_tendsto_atTop
  statement: [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α}
  proof: by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_atTop.mp hf) b'
  have : { x : α | f x <= b } inter { x : α | b' <= f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_gt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')

中文:
定理 not_isBoundedUnder_of_tendsto_atTop
  结论: [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α}
  证明: by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_atTop.mp hf) b'
  have : { x : α | f x <= b } inter { x : α | b' <= f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_gt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')

Depends on / 依赖: eq_empty_of_subset_empty, eventually_map, exists_gt, hb.and, le_trans, ne_empty, nonempty_of_mem, not_le_of_gt, tendsto_atTop, tendsto_atTop.mp
-/
theorem not_isBoundedUnder_of_tendsto_atTop [Preorder β] [NoMaxOrder β] {f : α -> β} {l : Filter α}
    [l.NeBot] (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· <= ·) l f := by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_atTop.mp hf) b'
  have : { x : α | f x <= b } inter { x : α | b' <= f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_gt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this

@[to_dual]
/--
theorem `IsBoundedUnder.bddAbove_range_of_cofinite` / 定理 `IsBoundedUnder.bddAbove_range_of_cofinite`

English:
theorem IsBoundedUnder.bddAbove_range_of_cofinite
  statement: [Preorder β] [IsDirectedOrder β] {f : α -> β}
  proof: by
  rcases hf with ⟨b, hb⟩
  have : Nonempty β := ⟨b⟩
  rw [← image_univ]; rw [← union_compl_self { x | f x <= b }]; rw [image_union]; rw [bddAbove_union]
  exact ⟨⟨b, forall_mem_image.2 fun x => id⟩, (hb.image f).bddAbove⟩

@[to_dual]

中文:
定理 IsBoundedUnder.bddAbove_range_of_cofinite
  结论: [Preorder β] [IsDirectedOrder β] {f : α -> β}
  证明: by
  rcases hf with ⟨b, hb⟩
  have : Nonempty β := ⟨b⟩
  rw [← image_univ]; rw [← union_compl_self { x | f x <= b }]; rw [image_union]; rw [bddAbove_union]
  exact ⟨⟨b, forall_mem_image.2 fun x => id⟩, (hb.image f).bddAbove⟩

@[to_dual]

Depends on / 依赖: Nonempty, bddAbove, bddAbove_union, forall_mem_image, hb.image, image_union, image_univ, union_compl_self
-/
theorem IsBoundedUnder.bddAbove_range_of_cofinite [Preorder β] [IsDirectedOrder β] {f : α -> β}
    (hf : IsBoundedUnder (· <= ·) cofinite f) : BddAbove (range f) := by
  rcases hf with ⟨b, hb⟩
  have : Nonempty β := ⟨b⟩
  rw [← image_univ]; rw [← union_compl_self { x | f x <= b }]; rw [image_union]; rw [bddAbove_union]
  exact ⟨⟨b, forall_mem_image.2 fun x => id⟩, (hb.image f).bddAbove⟩

@[to_dual]
/--
theorem `IsBoundedUnder.bddAbove_range` / 定理 `IsBoundedUnder.bddAbove_range`

English:
theorem IsBoundedUnder.bddAbove_range
  statement: [Preorder β] [IsDirectedOrder β] {f : Nat -> β}
  proof: by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bddAbove_range_of_cofinite

中文:
定理 IsBoundedUnder.bddAbove_range
  结论: [Preorder β] [IsDirectedOrder β] {f : 自然数 -> β}
  证明: by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bddAbove_range_of_cofinite

Depends on / 依赖: Nat.cofinite_eq_atTop, bddAbove_range_of_cofinite, cofinite_eq_atTop, hf.bddAbove_range_of_cofinite
-/
theorem IsBoundedUnder.bddAbove_range [Preorder β] [IsDirectedOrder β] {f : Nat -> β}
    (hf : IsBoundedUnder (· <= ·) atTop f) : BddAbove (range f) := by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bddAbove_range_of_cofinite

/--
theorem `IsCobounded.mk` / 定理 `IsCobounded.mk`

English:
theorem IsCobounded.mk
  given: [IsTrans α r] (a : α) (h : forall s in f, exists x in s, r a x)
  statement: f.IsCobounded r
  proof: ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩

中文:
定理 IsCobounded.mk
  条件: [IsTrans α r] (a : α) (h : 对任意 s in f, 存在 x in s, r a x)
  结论: f.IsCobounded r
  证明: ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩

Depends on / 依赖: _root_, _root_.trans
-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : forall s in f, exists x in s, r a x) : f.IsCobounded r :=
  ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩

/--
theorem `IsBounded.isCobounded_flip` / 定理 `IsBounded.isCobounded_flip`

English:
theorem IsBounded.isCobounded_flip
  given: [IsTrans α r] [NeBot f]
  statement: f.IsBounded r -> f.IsCobounded (flip r)
  proof: (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩

@[to_dual isCobounded_ge]

中文:
定理 IsBounded.isCobounded_flip
  条件: [IsTrans α r] [NeBot f]
  结论: f.IsBounded r -> f.IsCobounded (flip r)
  证明: (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩

@[to_dual isCobounded_ge]

Depends on / 依赖: ha.and
-/
theorem IsBounded.isCobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r -> f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨_, rxa, rbx⟩ := (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩

@[to_dual isCobounded_ge]
/--
theorem `IsBounded.isCobounded_le` / 定理 `IsBounded.isCobounded_le`

English:
theorem IsBounded.isCobounded_le
  given: [Preorder α] [NeBot f] (h : f.IsBounded (fun x1 x2 => x2 <= x1))
  proof: h.isCobounded_flip

中文:
定理 IsBounded.isCobounded_le
  条件: [Preorder α] [NeBot f] (h : f.IsBounded (fun x1 x2 => x2 <= x1))
  证明: h.isCobounded_flip

Depends on / 依赖: h.isCobounded_flip, isCobounded_flip
-/
theorem IsBounded.isCobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (fun x1 x2 => x2 <= x1)) :
    f.IsCobounded (· <= ·) :=
  h.isCobounded_flip

/--
theorem `IsBoundedUnder.isCoboundedUnder_flip` / 定理 `IsBoundedUnder.isCoboundedUnder_flip`

English:
theorem IsBoundedUnder.isCoboundedUnder_flip
  statement: {u : γ -> α} {l : Filter γ} [IsTrans α r] [NeBot l]
  proof: h.isCobounded_flip

@[to_dual isCoboundedUnder_ge]

中文:
定理 IsBoundedUnder.isCoboundedUnder_flip
  结论: {u : γ -> α} {l : Filter γ} [IsTrans α r] [NeBot l]
  证明: h.isCobounded_flip

@[to_dual isCoboundedUnder_ge]

Depends on / 依赖: Algebra, Algebra.IsPushout.isAlgebraic, IsPushout, h.isCobounded_flip, isAlgebraic, isCobounded_flip
-/
theorem IsBoundedUnder.isCoboundedUnder_flip {u : γ -> α} {l : Filter γ} [IsTrans α r] [NeBot l]
    (h : l.IsBoundedUnder r u) : l.IsCoboundedUnder (flip r) u :=
  h.isCobounded_flip

@[to_dual isCoboundedUnder_ge]
/--
theorem `IsBoundedUnder.isCoboundedUnder_le` / 定理 `IsBoundedUnder.isCoboundedUnder_le`

English:
theorem IsBoundedUnder.isCoboundedUnder_le
  statement: {u : γ -> α} {l : Filter γ} [Preorder α] [NeBot l]
  proof: h.isCoboundedUnder_flip

@[to_dual isCoboundedUnder_ge_of_eventually_le]

中文:
定理 IsBoundedUnder.isCoboundedUnder_le
  结论: {u : γ -> α} {l : Filter γ} [Preorder α] [NeBot l]
  证明: h.isCoboundedUnder_flip

@[to_dual isCoboundedUnder_ge_of_eventually_le]

Depends on / 依赖: Algebra, Algebra.isAlgebraic_of_not_injective, Function, Function.Injective, Injective, MvPolynomial, MvPolynomial.map_injective_iff, algebraMap, h.isCoboundedUnder_flip, h.noZeroDivisors, infer_instance, isAlgebraic_of_not_injective, isCoboundedUnder_flip, map_injective_iff, map_mul, map_zero, noZeroDivisors
-/
theorem IsBoundedUnder.isCoboundedUnder_le {u : γ -> α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (fun x1 x2 => x2 <= x1) u) : l.IsCoboundedUnder (· <= ·) u :=
  h.isCoboundedUnder_flip

@[to_dual isCoboundedUnder_ge_of_eventually_le]
/--
lemma `isCoboundedUnder_le_of_eventually_le` / 引理 `isCoboundedUnder_le_of_eventually_le`

English:
lemma isCoboundedUnder_le_of_eventually_le
  statement: [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
  proof: IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

@[to_dual isCoboundedUnder_ge_of_le]

中文:
引理 isCoboundedUnder_le_of_eventually_le
  结论: [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
  证明: IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

@[to_dual isCoboundedUnder_ge_of_le]

Depends on / 依赖: IsBoundedUnder, IsBoundedUnder.isCoboundedUnder_le, isCoboundedUnder_le
-/
lemma isCoboundedUnder_le_of_eventually_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
    (hf : forallᶠ i in l, x <= f i) :
    IsCoboundedUnder (· <= ·) l f :=
  IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

@[to_dual isCoboundedUnder_ge_of_le]
/--
lemma `isCoboundedUnder_le_of_le` / 引理 `isCoboundedUnder_le_of_le`

English:
lemma isCoboundedUnder_le_of_le
  statement: [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
  proof: isCoboundedUnder_le_of_eventually_le l (Eventually.of_forall hf)

中文:
引理 isCoboundedUnder_le_of_le
  结论: [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
  证明: isCoboundedUnder_le_of_eventually_le l (Eventually.of_forall hf)

Depends on / 依赖: Eventually, Eventually.of_forall, isCoboundedUnder_le_of_eventually_le, of_forall
-/
lemma isCoboundedUnder_le_of_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α}
    (hf : forall i, x <= f i) :
    IsCoboundedUnder (· <= ·) l f :=
  isCoboundedUnder_le_of_eventually_le l (Eventually.of_forall hf)


/--
theorem `isCobounded_bot` / 定理 `isCobounded_bot`

English:
theorem isCobounded_bot
  statement: IsCobounded r ⊥ ↔ exists b, forall x, r b x
  proof: by simp [IsCobounded]

中文:
定理 isCobounded_bot
  结论: IsCobounded r ⊥ ↔ 存在 b, 对任意 x, r b x
  证明: by simp [IsCobounded]

Depends on / 依赖: IsCobounded
-/
theorem isCobounded_bot : IsCobounded r ⊥ ↔ exists b, forall x, r b x := by simp [IsCobounded]

/--
theorem `isCobounded_top` / 定理 `isCobounded_top`

English:
theorem isCobounded_top
  statement: IsCobounded r ⊤ ↔ Nonempty α
  proof: by
  simp +contextual [IsCobounded,
    exists_true_iff_nonempty]

中文:
定理 isCobounded_top
  结论: IsCobounded r ⊤ ↔ Nonempty α
  证明: by
  simp +contextual [IsCobounded,
    exists_true_iff_nonempty]

Depends on / 依赖: Algebra, Algebra.IsPushout.comp_iff, IsCobounded, IsPushout, MvPolynomial, comp_iff, contextual, exists_true_iff_nonempty
-/
theorem isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp +contextual [IsCobounded,
    exists_true_iff_nonempty]

/--
theorem `isCobounded_principal` / 定理 `isCobounded_principal`

English:
theorem isCobounded_principal
  given: (s : Set α)
  proof: by simp [IsCobounded]

中文:
定理 isCobounded_principal
  条件: (s : Set α)
  证明: by simp [IsCobounded]

Depends on / 依赖: IsCobounded
-/
theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ exists b, forall a, (forall x in s, r x a) -> r b a := by simp [IsCobounded]

/--
theorem `IsCobounded.mono` / 定理 `IsCobounded.mono`

English:
theorem IsCobounded.mono
  given: (h : f <= g)
  statement: f.IsCobounded r -> g.IsCobounded r

中文:
定理 IsCobounded.mono
  条件: (h : f <= g)
  结论: f.IsCobounded r -> g.IsCobounded r
-/
theorem IsCobounded.mono (h : f <= g) : f.IsCobounded r -> g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩

/-- For nontrivial filters in linear orders, coboundedness for `≤` implies frequent boundedness
from below. -/
@[to_dual frequently_le
/-- For nontrivial filters in linear orders, coboundedness for `≥` implies frequent boundedness
from above. -/]
/--
lemma `IsCobounded.frequently_ge` / 引理 `IsCobounded.frequently_ge`

English:
lemma IsCobounded.frequently_ge
  given: [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· <= ·) f)
  proof: by
  obtain ⟨t, ht⟩ := cobdd
  rcases isBot_or_exists_lt t with tbot | ⟨t', ht'⟩
  · exact ⟨t, .of_forall fun r => tbot r⟩
  refine ⟨t', fun ev => ?_⟩
  specialize ht t' (by filter_upwards [ev] with _ h using (not_le.mp h).le)
  exact not_lt_of_ge ht ht'

中文:
引理 IsCobounded.frequently_ge
  条件: [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· <= ·) f)
  证明: by
  obtain ⟨t, ht⟩ := cobdd
  rcases isBot_or_exists_lt t with tbot | ⟨t', ht'⟩
  · exact ⟨t, .of_forall fun r => tbot r⟩
  refine ⟨t', fun ev => ?_⟩
  specialize ht t' (by filter_upwards [ev] with _ h using (not_le.mp h).le)
  exact not_lt_of_ge ht ht'

Depends on / 依赖: filter_upwards, isBot_or_exists_lt, not_le, not_le.mp, not_lt_of_ge, of_forall, specialize
-/
lemma IsCobounded.frequently_ge [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· <= ·) f) :
    exists l, existsᶠ x in f, l <= x := by
  obtain ⟨t, ht⟩ := cobdd
  rcases isBot_or_exists_lt t with tbot | ⟨t', ht'⟩
  · exact ⟨t, .of_forall fun r => tbot r⟩
  refine ⟨t', fun ev => ?_⟩
  specialize ht t' (by filter_upwards [ev] with _ h using (not_le.mp h).le)
  exact not_lt_of_ge ht ht'

/-- In linear orders, frequent boundedness from below implies coboundedness for `≤`. -/
@[to_dual of_frequently_le
/-- In linear orders, frequent boundedness from above implies coboundedness for `≥`. -/]
/--
lemma `IsCobounded.of_frequently_ge` / 引理 `IsCobounded.of_frequently_ge`

English:
lemma IsCobounded.of_frequently_ge
  given: [LinearOrder α] {l : α} (freq_ge : existsᶠ x in f, l <= x)
  proof: by
  rcases isBot_or_exists_lt l with lbot | ⟨l', hl'⟩
  · exact ⟨l, fun x _ => lbot x⟩
  refine ⟨l', fun u hu => ?_⟩
  obtain ⟨w, l_le_w, w_le_u⟩ := (freq_ge.and_eventually hu).exists
  exact hl'.le.trans (l_le_w.trans w_le_u)

@[to_dual frequently_le]

中文:
引理 IsCobounded.of_frequently_ge
  条件: [LinearOrder α] {l : α} (freq_ge : 存在ᶠ x in f, l <= x)
  证明: by
  rcases isBot_or_exists_lt l with lbot | ⟨l', hl'⟩
  · exact ⟨l, fun x _ => lbot x⟩
  refine ⟨l', fun u hu => ?_⟩
  obtain ⟨w, l_le_w, w_le_u⟩ := (freq_ge.and_eventually hu).exists
  exact hl'.le.trans (l_le_w.trans w_le_u)

@[to_dual frequently_le]

Depends on / 依赖: and_eventually, freq_ge, freq_ge.and_eventually, isBot_or_exists_lt, l_le_w, l_le_w.trans, le.trans, w_le_u
-/
lemma IsCobounded.of_frequently_ge [LinearOrder α] {l : α} (freq_ge : existsᶠ x in f, l <= x) :
    IsCobounded (· <= ·) f := by
  rcases isBot_or_exists_lt l with lbot | ⟨l', hl'⟩
  · exact ⟨l, fun x _ => lbot x⟩
  refine ⟨l', fun u hu => ?_⟩
  obtain ⟨w, l_le_w, w_le_u⟩ := (freq_ge.and_eventually hu).exists
  exact hl'.le.trans (l_le_w.trans w_le_u)

@[to_dual frequently_le]
/--
lemma `IsCoboundedUnder.frequently_ge` / 引理 `IsCoboundedUnder.frequently_ge`

English:
lemma IsCoboundedUnder.frequently_ge
  statement: [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι -> α}
  proof: IsCobounded.frequently_ge h

@[to_dual of_frequently_le]

中文:
引理 IsCoboundedUnder.frequently_ge
  结论: [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι -> α}
  证明: IsCobounded.frequently_ge h

@[to_dual of_frequently_le]

Depends on / 依赖: IsCobounded, IsCobounded.frequently_ge, frequently_ge
-/
lemma IsCoboundedUnder.frequently_ge [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι -> α}
    (h : IsCoboundedUnder (· <= ·) f u) :
    exists a, existsᶠ x in f, a <= u x :=
  IsCobounded.frequently_ge h

@[to_dual of_frequently_le]
/--
lemma `IsCoboundedUnder.of_frequently_ge` / 引理 `IsCoboundedUnder.of_frequently_ge`

English:
lemma IsCoboundedUnder.of_frequently_ge
  statement: [LinearOrder α] {f : Filter ι} {u : ι -> α}
  proof: IsCobounded.of_frequently_ge freq_ge

中文:
引理 IsCoboundedUnder.of_frequently_ge
  结论: [LinearOrder α] {f : Filter ι} {u : ι -> α}
  证明: IsCobounded.of_frequently_ge freq_ge

Depends on / 依赖: IsCobounded, IsCobounded.of_frequently_ge, freq_ge, of_frequently_ge
-/
lemma IsCoboundedUnder.of_frequently_ge [LinearOrder α] {f : Filter ι} {u : ι -> α}
    {a : α} (freq_ge : existsᶠ x in f, a <= u x) :
    IsCoboundedUnder (· <= ·) f u :=
  IsCobounded.of_frequently_ge freq_ge

end Relation

section add_and_sum

open Filter Set

variable {α : Type*} {f : Filter α}
variable {R : Type*}

/--
lemma `isBoundedUnder_sum` / 引理 `isBoundedUnder_sum`

English:
lemma isBoundedUnder_sum
  statement: {κ : Type*} [AddCommMonoid R] {r : R -> R -> Prop}
  proof: by
  induction s using Finset.cons_induction
  case empty =>
    rw [Finset.sum_empty]
    exact ⟨0, by simp_all only [eventually_map, Pi.zero_apply, eventually_true]⟩
  case cons k₀ s k₀_notin_s ih =>
    simp only [Finset.forall_mem_cons] at *
    simpa only [Finset.sum_cons] using hr _ _ h.1 (ih 

中文:
引理 isBoundedUnder_sum
  结论: {κ : 类型} [AddCommMonoid R] {r : R -> R -> 命题}
  证明: by
  induction s using Finset.cons_induction
  case empty =>
    rw [Finset.sum_empty]
    exact ⟨0, by simp_all only [eventually_map, Pi.zero_apply, eventually_true]⟩
  case cons k₀ s k₀_notin_s ih =>
    simp only [Finset.forall_mem_cons] at *
    simpa only [Finset.sum_cons] using hr _ _ h.1 (ih 

Depends on / 依赖: Finset, Finset.cons_induction, Finset.forall_mem_cons, Finset.sum_cons, Finset.sum_empty, Pi.zero_apply, cons_induction, eventually_map, eventually_true, forall_mem_cons, sum_cons, sum_empty, zero_apply
-/
lemma isBoundedUnder_sum {κ : Type*} [AddCommMonoid R] {r : R -> R -> Prop}
    (hr : forall (v₁ v₂ : α -> R), f.IsBoundedUnder r v₁ -> f.IsBoundedUnder r v₂
      -> f.IsBoundedUnder r (v₁ + v₂)) (hr₀ : r 0 0)
    {u : κ -> α -> R} (s : Finset κ) (h : forall k in s, f.IsBoundedUnder r (u k)) :
    f.IsBoundedUnder r (∑ k in s, u k) := by
  induction s using Finset.cons_induction
  case empty =>
    rw [Finset.sum_empty]
    exact ⟨0, by simp_all only [eventually_map, Pi.zero_apply, eventually_true]⟩
  case cons k₀ s k₀_notin_s ih =>
    simp only [Finset.forall_mem_cons] at *
    simpa only [Finset.sum_cons] using hr _ _ h.1 (ih h.2)

variable [Preorder R]

@[to_dual isBoundedUnder_ge_add]
/--
lemma `isBoundedUnder_le_add` / 引理 `isBoundedUnder_le_add`

English:
lemma isBoundedUnder_le_add
  statement: [Add R] [AddLeftMono R] [AddRightMono R]
  proof: by
  obtain ⟨U, hU⟩ := u_bdd_le
  obtain ⟨V, hV⟩ := v_bdd_le
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

@[to_dual isBoundedUnder_ge_sum]

中文:
引理 isBoundedUnder_le_add
  结论: [Add R] [AddLeftMono R] [AddRightMono R]
  证明: by
  obtain ⟨U, hU⟩ := u_bdd_le
  obtain ⟨V, hV⟩ := v_bdd_le
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

@[to_dual isBoundedUnder_ge_sum]

Depends on / 依赖: Pi.add_apply, add_apply, add_le_add, eventually_map, filter_upwards, u_bdd_le, v_bdd_le
-/
lemma isBoundedUnder_le_add [Add R] [AddLeftMono R] [AddRightMono R]
    {u v : α -> R} (u_bdd_le : f.IsBoundedUnder (· <= ·) u) (v_bdd_le : f.IsBoundedUnder (· <= ·) v) :
    f.IsBoundedUnder (· <= ·) (u + v) := by
  obtain ⟨U, hU⟩ := u_bdd_le
  obtain ⟨V, hV⟩ := v_bdd_le
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

@[to_dual isBoundedUnder_ge_sum]
/--
lemma `isBoundedUnder_le_sum` / 引理 `isBoundedUnder_le_sum`

English:
lemma isBoundedUnder_le_sum
  statement: {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
  proof: fun h => isBoundedUnder_sum (fun _ _ => isBoundedUnder_le_add) le_rfl s h

中文:
引理 isBoundedUnder_le_sum
  结论: {κ : 类型} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
  证明: fun h => isBoundedUnder_sum (fun _ _ => isBoundedUnder_le_add) le_rfl s h

Depends on / 依赖: isBoundedUnder_le_add, isBoundedUnder_sum, le_rfl
-/
lemma isBoundedUnder_le_sum {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
    {u : κ -> α -> R} (s : Finset κ) :
    (forall k in s, f.IsBoundedUnder (· <= ·) (u k)) -> f.IsBoundedUnder (· <= ·) (∑ k in s, u k) :=
  fun h => isBoundedUnder_sum (fun _ _ => isBoundedUnder_le_add) le_rfl s h

end add_and_sum

section add_and_sum

variable {α R : Type*} [LinearOrder R] [Add R] {f : Filter α} [f.NeBot]
  [AddLeftMono R] [AddRightMono R]
  {u v : α -> R}

@[to_dual isCoboundedUnder_ge_add]
/--
lemma `isCoboundedUnder_le_add` / 引理 `isCoboundedUnder_le_add`

English:
lemma isCoboundedUnder_le_add
  statement: (hu : f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u)
  proof: by
  obtain ⟨U, hU⟩ := hu.eventually_ge
  obtain ⟨V, hV⟩ := hv.frequently_ge
  apply IsCoboundedUnder.of_frequently_ge (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx => add_le_add hx.2 hx.1

中文:
引理 isCoboundedUnder_le_add
  结论: (hu : f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u)
  证明: by
  obtain ⟨U, hU⟩ := hu.eventually_ge
  obtain ⟨V, hV⟩ := hv.frequently_ge
  apply IsCoboundedUnder.of_frequently_ge (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx => add_le_add hx.2 hx.1

Depends on / 依赖: IsCoboundedUnder, IsCoboundedUnder.of_frequently_ge, add_le_add, and_eventually, eventually_ge, frequently_ge, hV.and_eventually, hu.eventually_ge, hv.frequently_ge, of_frequently_ge
-/
lemma isCoboundedUnder_le_add (hu : f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u)
    (hv : f.IsCoboundedUnder (· <= ·) v) :
    f.IsCoboundedUnder (· <= ·) (u + v) := by
  obtain ⟨U, hU⟩ := hu.eventually_ge
  obtain ⟨V, hV⟩ := hv.frequently_ge
  apply IsCoboundedUnder.of_frequently_ge (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx => add_le_add hx.2 hx.1

end add_and_sum

section mul

/--
lemma `isBoundedUnder_le_mul_of_nonneg` / 引理 `isBoundedUnder_le_mul_of_nonneg`

English:
lemma isBoundedUnder_le_mul_of_nonneg
  statement: [Preorder α] [Mul α] [Zero α] [PosMulMono α]
  proof: by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₃] with x x_U x_V v_0
  have U_0 : 0 <= U := by
    obtain ⟨y, y_0, y_U⟩ := (h₁.and_eventually hU).exists
    exact y_0.trans y_U
  exact (

中文:
引理 isBoundedUnder_le_mul_of_nonneg
  结论: [Preorder α] [Mul α] [Zero α] [PosMulMono α]
  证明: by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₃] with x x_U x_V v_0
  have U_0 : 0 <= U := by
    obtain ⟨y, y_0, y_U⟩ := (h₁.and_eventually hU).exists
    exact y_0.trans y_U
  exact (

Depends on / 依赖: and_eventually, eventually_le, filter_upwards, isBoundedUnder_of_eventually_le, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, y_0.trans
-/
lemma isBoundedUnder_le_mul_of_nonneg [Preorder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} {u v : ι -> α} (h₁ : existsᶠ x in f, 0 <= u x)
    (h₂ : IsBoundedUnder (· <= ·) f u) (h₃ : 0 <=ᶠ[f] v)
    (h₄ : IsBoundedUnder (· <= ·) f v) :
    IsBoundedUnder (· <= ·) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₃] with x x_U x_V v_0
  have U_0 : 0 <= U := by
    obtain ⟨y, y_0, y_U⟩ := (h₁.and_eventually hU).exists
    exact y_0.trans y_U
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V U_0)

/--
lemma `isCoboundedUnder_ge_mul_of_nonneg` / 引理 `isCoboundedUnder_ge_mul_of_nonneg`

English:
lemma isCoboundedUnder_ge_mul_of_nonneg
  statement: [LinearOrder α] [Mul α] [Zero α] [PosMulMono α]
  proof: by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  refine IsCoboundedUnder.of_frequently_le (a := U * V) ?_
  apply (hV.and_eventually (hU.and (h₁.and h₃))).mono
  intro x ⟨x_V, x_U, u_0, v_0⟩
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x

中文:
引理 isCoboundedUnder_ge_mul_of_nonneg
  结论: [LinearOrder α] [Mul α] [Zero α] [PosMulMono α]
  证明: by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  refine IsCoboundedUnder.of_frequently_le (a := U * V) ?_
  apply (hV.and_eventually (hU.and (h₁.and h₃))).mono
  intro x ⟨x_V, x_U, u_0, v_0⟩
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x

Depends on / 依赖: IsCoboundedUnder, IsCoboundedUnder.of_frequently_le, and_eventually, eventually_le, frequently_le, hU.and, hV.and_eventually, mul_le_mul_of_nonneg_left, mul_le_mul_of_nonneg_right, of_frequently_le, u_0.trans
-/
lemma isCoboundedUnder_ge_mul_of_nonneg [LinearOrder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} [f.NeBot] {u v : ι -> α} (h₁ : 0 <=ᶠ[f] u)
    (h₂ : IsBoundedUnder (· <= ·) f u)
    (h₃ : 0 <=ᶠ[f] v)
    (h₄ : IsCoboundedUnder (fun x1 x2 => x2 <= x1) f v) :
    IsCoboundedUnder (fun x1 x2 => x2 <= x1) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  refine IsCoboundedUnder.of_frequently_le (a := U * V) ?_
  apply (hV.and_eventually (hU.and (h₁.and h₃))).mono
  intro x ⟨x_V, x_U, u_0, v_0⟩
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V (u_0.trans x_U))

end mul

section Nonempty
variable [Preorder α] [Nonempty α] {f : Filter β} {u : β -> α}

@[to_dual isBounded_ge_atTop]
/--
theorem `isBounded_le_atBot` / 定理 `isBounded_le_atBot`

English:
theorem isBounded_le_atBot
  statement: (atBot : Filter α).IsBounded (· <= ·)
  proof: ‹Nonempty α›.elim fun a => ⟨a, eventually_le_atBot _⟩

@[to_dual isBoundedUnder_ge_atTop]

中文:
定理 isBounded_le_atBot
  结论: (atBot : Filter α).IsBounded (· <= ·)
  证明: ‹Nonempty α›.elim fun a => ⟨a, eventually_le_atBot _⟩

@[to_dual isBoundedUnder_ge_atTop]

Depends on / 依赖: Nonempty, eventually_le_atBot
-/
theorem isBounded_le_atBot : (atBot : Filter α).IsBounded (· <= ·) :=
  ‹Nonempty α›.elim fun a => ⟨a, eventually_le_atBot _⟩

@[to_dual isBoundedUnder_ge_atTop]
/--
theorem `Tendsto.isBoundedUnder_le_atBot` / 定理 `Tendsto.isBoundedUnder_le_atBot`

English:
theorem Tendsto.isBoundedUnder_le_atBot
  given: (h : Tendsto u f atBot)
  statement: f.IsBoundedUnder (· <= ·) u
  proof: isBounded_le_atBot.mono h

@[to_dual]

中文:
定理 Tendsto.isBoundedUnder_le_atBot
  条件: (h : Tendsto u f atBot)
  结论: f.IsBoundedUnder (· <= ·) u
  证明: isBounded_le_atBot.mono h

@[to_dual]

Depends on / 依赖: isBounded_le_atBot, isBounded_le_atBot.mono
-/
theorem Tendsto.isBoundedUnder_le_atBot (h : Tendsto u f atBot) : f.IsBoundedUnder (· <= ·) u :=
  isBounded_le_atBot.mono h

@[to_dual]
/--
theorem `bddAbove_range_of_tendsto_atTop_atBot` / 定理 `bddAbove_range_of_tendsto_atTop_atBot`

English:
theorem bddAbove_range_of_tendsto_atTop_atBot
  statement: [IsDirectedOrder α] {u : Nat -> α}
  proof: hx.isBoundedUnder_le_atBot.bddAbove_range

中文:
定理 bddAbove_range_of_tendsto_atTop_atBot
  结论: [IsDirectedOrder α] {u : 自然数 -> α}
  证明: hx.isBoundedUnder_le_atBot.bddAbove_range

Depends on / 依赖: bddAbove_range, hx.isBoundedUnder_le_atBot.bddAbove_range, isBoundedUnder_le_atBot
-/
theorem bddAbove_range_of_tendsto_atTop_atBot [IsDirectedOrder α] {u : Nat -> α}
    (hx : Tendsto u atTop atBot) : BddAbove (Set.range u) :=
  hx.isBoundedUnder_le_atBot.bddAbove_range

/--
theorem `bddBelow_range_of_tendsto_atTop_atTop` / 定理 `bddBelow_range_of_tendsto_atTop_atTop`

English:
theorem bddBelow_range_of_tendsto_atTop_atTop
  statement: [IsCodirectedOrder α] {u : Nat -> α}
  proof: hx.isBoundedUnder_ge_atTop.bddBelow_range

中文:
定理 bddBelow_range_of_tendsto_atTop_atTop
  结论: [IsCodirectedOrder α] {u : 自然数 -> α}
  证明: hx.isBoundedUnder_ge_atTop.bddBelow_range

Depends on / 依赖: bddBelow_range, hx.isBoundedUnder_ge_atTop.bddBelow_range, isBoundedUnder_ge_atTop
-/
theorem bddBelow_range_of_tendsto_atTop_atTop [IsCodirectedOrder α] {u : Nat -> α}
    (hx : Tendsto u atTop atTop) : BddBelow (Set.range u) :=
  hx.isBoundedUnder_ge_atTop.bddBelow_range

end Nonempty

@[to_dual isCobounded_ge_of_top]
/--
theorem `isCobounded_le_of_bot` / 定理 `isCobounded_le_of_bot`

English:
theorem isCobounded_le_of_bot
  given: [LE α] [OrderBot α] {f : Filter α}
  statement: f.IsCobounded (· <= ·)
  proof: ⟨⊥, fun _ _ => bot_le⟩

@[to_dual isBounded_ge_of_bot]

中文:
定理 isCobounded_le_of_bot
  条件: [LE α] [OrderBot α] {f : Filter α}
  结论: f.IsCobounded (· <= ·)
  证明: ⟨⊥, fun _ _ => bot_le⟩

@[to_dual isBounded_ge_of_bot]

Depends on / 依赖: bot_le
-/
theorem isCobounded_le_of_bot [LE α] [OrderBot α] {f : Filter α} : f.IsCobounded (· <= ·) :=
  ⟨⊥, fun _ _ => bot_le⟩

@[to_dual isBounded_ge_of_bot]
/--
theorem `isBounded_le_of_top` / 定理 `isBounded_le_of_top`

English:
theorem isBounded_le_of_top
  given: [LE α] [OrderTop α] {f : Filter α}
  statement: f.IsBounded (· <= ·)
  proof: ⟨⊤, Eventually.of_forall fun _ => le_top⟩

@[to_dual (attr := simp) isBoundedUnder_ge_comp]

中文:
定理 isBounded_le_of_top
  条件: [LE α] [OrderTop α] {f : Filter α}
  结论: f.IsBounded (· <= ·)
  证明: ⟨⊤, Eventually.of_forall fun _ => le_top⟩

@[to_dual (attr := simp) isBoundedUnder_ge_comp]

Depends on / 依赖: Eventually, Eventually.of_forall, le_top, of_forall
-/
theorem isBounded_le_of_top [LE α] [OrderTop α] {f : Filter α} : f.IsBounded (· <= ·) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

@[to_dual (attr := simp) isBoundedUnder_ge_comp]
/--
theorem `_root_.OrderIso.isBoundedUnder_le_comp` / 定理 `_root_.OrderIso.isBoundedUnder_le_comp`

English:
theorem _root_.OrderIso.isBoundedUnder_le_comp
  statement: [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
  proof: (Function.Surjective.exists e.surjective).trans
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

中文:
定理 _root_.OrderIso.isBoundedUnder_le_comp
  结论: [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
  证明: (Function.Surjective.exists e.surjective).trans
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

Depends on / 依赖: Function, Function.Surjective.exists, Surjective, e.le_iff_le, e.surjective, eventually_map, exists_congr, le_iff_le, surjective
-/
theorem _root_.OrderIso.isBoundedUnder_le_comp [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
    {u : γ -> α} : (IsBoundedUnder (· <= ·) l fun x => e (u x)) ↔ IsBoundedUnder (· <= ·) l u :=
(Function.Surjective.exists e.surjective).trans
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

-- TODO: use `to_dual` in combination with `to_additive`
@[to_additive (attr := simp)]
/--
theorem `isBoundedUnder_le_inv` / 定理 `isBoundedUnder_le_inv`

English:
theorem isBoundedUnder_le_inv
  statement: [CommGroup α] [Preorder α] [IsOrderedMonoid α]
  proof: (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]

中文:
定理 isBoundedUnder_le_inv
  结论: [CommGroup α] [Preorder α] [IsOrderedMonoid α]
  证明: (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.inv, isBoundedUnder_ge_comp
-/
theorem isBoundedUnder_le_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β -> α} :
    (IsBoundedUnder (· <= ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· >= ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]
/--
theorem `isBoundedUnder_ge_inv` / 定理 `isBoundedUnder_ge_inv`

English:
theorem isBoundedUnder_ge_inv
  statement: [CommGroup α] [Preorder α] [IsOrderedMonoid α]
  proof: (OrderIso.inv α).isBoundedUnder_le_comp

@[to_dual]

中文:
定理 isBoundedUnder_ge_inv
  结论: [CommGroup α] [Preorder α] [IsOrderedMonoid α]
  证明: (OrderIso.inv α).isBoundedUnder_le_comp

@[to_dual]

Depends on / 依赖: OrderIso, OrderIso.inv, isBoundedUnder_le_comp
-/
theorem isBoundedUnder_ge_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β -> α} :
    (IsBoundedUnder (· >= ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· <= ·) l u :=
  (OrderIso.inv α).isBoundedUnder_le_comp

@[to_dual]
/--
theorem `IsBoundedUnder.sup` / 定理 `IsBoundedUnder.sup`

English:
theorem IsBoundedUnder.sup
  given: [SemilatticeSup α] {f : Filter β} {u v : β -> α}

中文:
定理 IsBoundedUnder.sup
  条件: [SemilatticeSup α] {f : Filter β} {u v : β -> α}
-/
theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β -> α} :
    f.IsBoundedUnder (· <= ·) u ->
      f.IsBoundedUnder (· <= ·) v -> f.IsBoundedUnder (· <= ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : forallᶠ x in f, u x <= bu)⟩, ⟨bv, (hv : forallᶠ x in f, v x <= bv)⟩ =>
    ⟨bu ⊔ bv, show forallᶠ x in f, u x ⊔ v x <= bu ⊔ bv
      by filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[to_dual (attr := simp) isBoundedUnder_ge_inf]
/--
theorem `isBoundedUnder_le_sup` / 定理 `isBoundedUnder_le_sup`

English:
theorem isBoundedUnder_le_sup
  given: [SemilatticeSup α] {f : Filter β} {u v : β -> α}
  proof: ⟨fun h =>
⟨h.mono_le Eventually.of_forall fun _ => le_sup_left,
h.mono_le Eventually.of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

中文:
定理 isBoundedUnder_le_sup
  条件: [SemilatticeSup α] {f : Filter β} {u v : β -> α}
  证明: ⟨fun h =>
⟨h.mono_le Eventually.of_forall fun _ => le_sup_left,
h.mono_le Eventually.of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

Depends on / 依赖: Eventually, Eventually.of_forall, h.mono_le, le_sup_left, le_sup_right, mono_le, of_forall
-/
theorem isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β -> α} :
    (f.IsBoundedUnder (· <= ·) fun a => u a ⊔ v a) ↔
      f.IsBoundedUnder (· <= ·) u ∧ f.IsBoundedUnder (· <= ·) v :=
  ⟨fun h =>
⟨h.mono_le Eventually.of_forall fun _ => le_sup_left,
h.mono_le Eventually.of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩

/--
theorem `isBoundedUnder_le_abs` / 定理 `isBoundedUnder_le_abs`

English:
theorem isBoundedUnder_le_abs
  statement: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  proof: isBoundedUnder_le_sup.trans and_congr Iff.rfl isBoundedUnder_le_neg

中文:
定理 isBoundedUnder_le_abs
  结论: [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  证明: isBoundedUnder_le_sup.trans and_congr Iff.rfl isBoundedUnder_le_neg

Depends on / 依赖: Iff.rfl, and_congr, isBoundedUnder_le_neg, isBoundedUnder_le_sup, isBoundedUnder_le_sup.trans
-/
theorem isBoundedUnder_le_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {f : Filter β} {u : β -> α} :
    (f.IsBoundedUnder (· <= ·) fun a => |u a|) ↔
      f.IsBoundedUnder (· <= ·) u ∧ f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u :=
isBoundedUnder_le_sup.trans and_congr Iff.rfl isBoundedUnder_le_neg

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`. -/
macro "isBoundedDefault" : tactic =>
  `(tactic| first
    | apply isCobounded_le_of_bot
    | apply isCobounded_ge_of_top
    | apply isBounded_le_of_top
    | apply isBounded_ge_of_bot
    | assumption)

end Filter

open Filter

section Order

@[to_dual isBoundedUnder_ge_comp_iff]
/--
theorem `Monotone.isBoundedUnder_le_comp_iff` / 定理 `Monotone.isBoundedUnder_le_comp_iff`

English:
theorem Monotone.isBoundedUnder_le_comp_iff
  statement: [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
  proof: by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : exists b, forall a >= b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_ge hx⟩

@[to_dual isBoundedUnder

中文:
定理 Monotone.isBoundedUnder_le_comp_iff
  结论: [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
  证明: by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : exists b, forall a >= b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_ge hx⟩

@[to_dual isBoundedUnder

Depends on / 依赖: eventually_atTop, eventually_gt_atTop, eventually_map, h.isBoundedUnder, h.le, hc.mono, isBoundedUnder, not_ge, not_lt
-/
theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β -> γ} {f : α -> β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· <= ·) l (g ∘ f) ↔ IsBoundedUnder (· <= ·) l f := by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : exists b, forall a >= b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_ge hx⟩

@[to_dual isBoundedUnder_ge_comp_iff]
/--
theorem `Antitone.isBoundedUnder_le_comp_iff` / 定理 `Antitone.isBoundedUnder_le_comp_iff`

English:
theorem Antitone.isBoundedUnder_le_comp_iff
  statement: [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
  proof: hg.dual_right.isBoundedUnder_ge_comp_iff hg'

中文:
定理 Antitone.isBoundedUnder_le_comp_iff
  结论: [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
  证明: hg.dual_right.isBoundedUnder_ge_comp_iff hg'

Depends on / 依赖: dual_right, hg.dual_right.isBoundedUnder_ge_comp_iff, isBoundedUnder_ge_comp_iff
-/
theorem Antitone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β -> γ} {f : α -> β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· <= ·) l (g ∘ f) ↔ IsBoundedUnder (fun x1 x2 => x2 <= x1) l f :=
  hg.dual_right.isBoundedUnder_ge_comp_iff hg'

end Order

section MinMax

/--
theorem `isCoboundedUnder_le_max` / 定理 `isCoboundedUnder_le_max`

English:
theorem isCoboundedUnder_le_max
  statement: [LinearOrder β] {f : Filter α} {u v : α -> β}
  proof: by
  rcases h with (h' | h') <;>
  · rcases h' with ⟨b, hb⟩
    use b
    intro c hc
    apply hb c
    rw [eventually_map] at hc ⊢
    refine hc.mono (fun _ => ?_)
    simp +contextual only [implies_true, max_le_iff]

中文:
定理 isCoboundedUnder_le_max
  结论: [LinearOrder β] {f : Filter α} {u v : α -> β}
  证明: by
  rcases h with (h' | h') <;>
  · rcases h' with ⟨b, hb⟩
    use b
    intro c hc
    apply hb c
    rw [eventually_map] at hc ⊢
    refine hc.mono (fun _ => ?_)
    simp +contextual only [implies_true, max_le_iff]

Depends on / 依赖: contextual, eventually_map, hc.mono, implies_true, max_le_iff
-/
theorem isCoboundedUnder_le_max [LinearOrder β] {f : Filter α} {u v : α -> β}
    (h : f.IsCoboundedUnder (· <= ·) u ∨ f.IsCoboundedUnder (· <= ·) v) :
    f.IsCoboundedUnder (· <= ·) (fun a => max (u a) (v a)) := by
  rcases h with (h' | h') <;>
  · rcases h' with ⟨b, hb⟩
    use b
    intro c hc
    apply hb c
    rw [eventually_map] at hc ⊢
    refine hc.mono (fun _ => ?_)
    simp +contextual only [implies_true, max_le_iff]

open Finset

@[to_dual isBoundedUnder_ge_finset_inf']
/--
theorem `isBoundedUnder_le_finset_sup'` / 定理 `isBoundedUnder_le_finset_sup'`

English:
theorem isBoundedUnder_le_finset_sup'
  statement: [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι -> α -> β}
  proof: by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h => ?_
  simp only [sup'_le_iff]
  exact fun i i_s => le_trans (h i i_s) (le_sup' m i_s)

@[to_dual isCoboundedUnder_ge_finset_inf']

中文:
定理 isBoundedUnder_le_finset_sup'
  结论: [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι -> α -> β}
  证明: by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h => ?_
  simp only [sup'_le_iff]
  exact fun i i_s => le_trans (h i i_s) (le_sup' m i_s)

@[to_dual isCoboundedUnder_ge_finset_inf']

Depends on / 依赖: _le_iff, eventually_all_finset, eventually_map, hm.mono, le_sup, le_trans
-/
theorem isBoundedUnder_le_finset_sup' [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι -> α -> β}
    {s : Finset ι} (hs : s.Nonempty) (h : forall i in s, f.IsBoundedUnder (· <= ·) (F i)) :
    f.IsBoundedUnder (· <= ·) (fun a => sup' s hs (fun i => F i a)) := by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h => ?_
  simp only [sup'_le_iff]
  exact fun i i_s => le_trans (h i i_s) (le_sup' m i_s)

@[to_dual isCoboundedUnder_ge_finset_inf']
/--
theorem `isCoboundedUnder_le_finset_sup'` / 定理 `isCoboundedUnder_le_finset_sup'`

English:
theorem isCoboundedUnder_le_finset_sup'
  statement: [LinearOrder β] {f : Filter α} {F : ι -> α -> β}
  proof: by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc => hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h => ?_
  simp only [sup'_le_iff] at h ⊢
  exact h i i_s

@[to_dual isBoundedUnder_ge_finset_inf]

中文:
定理 isCoboundedUnder_le_finset_sup'
  结论: [LinearOrder β] {f : Filter α} {F : ι -> α -> β}
  证明: by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc => hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h => ?_
  simp only [sup'_le_iff] at h ⊢
  exact h i i_s

@[to_dual isBoundedUnder_ge_finset_inf]

Depends on / 依赖: _le_iff, eventually_map, hc.mono
-/
theorem isCoboundedUnder_le_finset_sup' [LinearOrder β] {f : Filter α} {F : ι -> α -> β}
    {s : Finset ι} (hs : s.Nonempty) (h : exists i in s, f.IsCoboundedUnder (· <= ·) (F i)) :
    f.IsCoboundedUnder (· <= ·) (fun a => sup' s hs (fun i => F i a)) := by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc => hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h => ?_
  simp only [sup'_le_iff] at h ⊢
  exact h i i_s

@[to_dual isBoundedUnder_ge_finset_inf]
/--
theorem `isBoundedUnder_le_finset_sup` / 定理 `isBoundedUnder_le_finset_sup`

English:
theorem isBoundedUnder_le_finset_sup
  statement: [LinearOrder β] [OrderBot β] {f : Filter α} {F : ι -> α -> β}
  proof: by
  choose! m hm using h
  use sup s m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  exact hm.mono fun _ h => sup_mono_fun h

中文:
定理 isBoundedUnder_le_finset_sup
  结论: [LinearOrder β] [OrderBot β] {f : Filter α} {F : ι -> α -> β}
  证明: by
  choose! m hm using h
  use sup s m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  exact hm.mono fun _ h => sup_mono_fun h

Depends on / 依赖: eventually_all_finset, eventually_map, hm.mono, sup_mono_fun
-/
theorem isBoundedUnder_le_finset_sup [LinearOrder β] [OrderBot β] {f : Filter α} {F : ι -> α -> β}
    {s : Finset ι} (h : forall i in s, f.IsBoundedUnder (· <= ·) (F i)) :
    f.IsBoundedUnder (· <= ·) (fun a => sup s (fun i => F i a)) := by
  choose! m hm using h
  use sup s m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  exact hm.mono fun _ h => sup_mono_fun h

end MinMax

section FrequentlyBounded

variable {R S : Type*} {F : Filter R} [LinearOrder R] [LinearOrder S]

@[to_dual frequently_le_map_of_frequently_le]
/--
lemma `Monotone.frequently_ge_map_of_frequently_ge` / 引理 `Monotone.frequently_ge_map_of_frequently_ge`

English:
lemma Monotone.frequently_ge_map_of_frequently_ge
  statement: {f : R -> S} (f_incr : Monotone f)
  proof: by
  refine fun ev => freq_ge ?_
  simp only [not_le] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
exact lt_irrefl (f l) lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

@[to_dual frequently_ge_map_of_frequently_le]

中文:
引理 Monotone.frequently_ge_map_of_frequently_ge
  结论: {f : R -> S} (f_incr : Monotone f)
  证明: by
  refine fun ev => freq_ge ?_
  simp only [not_le] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
exact lt_irrefl (f l) lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

@[to_dual frequently_ge_map_of_frequently_le]

Depends on / 依赖: f_incr, filter_upwards, freq_ge, lt_irrefl, lt_of_le_of_lt, not_le, not_lt, not_lt.mp
-/
lemma Monotone.frequently_ge_map_of_frequently_ge {f : R -> S} (f_incr : Monotone f)
    {l : R} (freq_ge : existsᶠ x in F, l <= x) :
    existsᶠ x' in F.map f, f l <= x' := by
  refine fun ev => freq_ge ?_
  simp only [not_le] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
exact lt_irrefl (f l) lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

@[to_dual frequently_ge_map_of_frequently_le]
/--
lemma `Antitone.frequently_le_map_of_frequently_ge` / 引理 `Antitone.frequently_le_map_of_frequently_ge`

English:
lemma Antitone.frequently_le_map_of_frequently_ge
  statement: {f : R -> S} (f_decr : Antitone f)
  proof: Monotone.frequently_ge_map_of_frequently_ge (S := Sᵒᵈ) f_decr frbdd

@[to_dual isCoboundedUnder_ge_of_isCobounded]

中文:
引理 Antitone.frequently_le_map_of_frequently_ge
  结论: {f : R -> S} (f_decr : Antitone f)
  证明: Monotone.frequently_ge_map_of_frequently_ge (S := Sᵒᵈ) f_decr frbdd

@[to_dual isCoboundedUnder_ge_of_isCobounded]

Depends on / 依赖: Monotone, Monotone.frequently_ge_map_of_frequently_ge, f_decr, frequently_ge_map_of_frequently_ge
-/
lemma Antitone.frequently_le_map_of_frequently_ge {f : R -> S} (f_decr : Antitone f)
    {l : R} (frbdd : existsᶠ x in F, l <= x) :
    existsᶠ y in F.map f, y <= f l :=
  Monotone.frequently_ge_map_of_frequently_ge (S := Sᵒᵈ) f_decr frbdd

@[to_dual isCoboundedUnder_ge_of_isCobounded]
/--
lemma `Monotone.isCoboundedUnder_le_of_isCobounded` / 引理 `Monotone.isCoboundedUnder_le_of_isCobounded`

English:
lemma Monotone.isCoboundedUnder_le_of_isCobounded
  statement: {f : R -> S} (f_incr : Monotone f)
  proof: by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_ge cobdd
exact IsCobounded.of_frequently_ge f_incr.frequently_ge_map_of_frequently_ge hl

@[to_dual isCoboundedUnder_ge_of_isCobounded]

中文:
引理 Monotone.isCoboundedUnder_le_of_isCobounded
  结论: {f : R -> S} (f_incr : Monotone f)
  证明: by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_ge cobdd
exact IsCobounded.of_frequently_ge f_incr.frequently_ge_map_of_frequently_ge hl

@[to_dual isCoboundedUnder_ge_of_isCobounded]

Depends on / 依赖: IsCobounded, IsCobounded.frequently_ge, IsCobounded.of_frequently_ge, f_incr, f_incr.frequently_ge_map_of_frequently_ge, frequently_ge, frequently_ge_map_of_frequently_ge, of_frequently_ge
-/
lemma Monotone.isCoboundedUnder_le_of_isCobounded {f : R -> S} (f_incr : Monotone f)
    [NeBot F] (cobdd : IsCobounded (· <= ·) F) :
    F.IsCoboundedUnder (· <= ·) f := by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_ge cobdd
exact IsCobounded.of_frequently_ge f_incr.frequently_ge_map_of_frequently_ge hl

@[to_dual isCoboundedUnder_ge_of_isCobounded]
/--
lemma `Antitone.isCoboundedUnder_le_of_isCobounded` / 引理 `Antitone.isCoboundedUnder_le_of_isCobounded`

English:
lemma Antitone.isCoboundedUnder_le_of_isCobounded
  statement: {f : R -> S} (f_decr : Antitone f)
  proof: by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_le cobdd
exact IsCobounded.of_frequently_ge f_decr.frequently_ge_map_of_frequently_le hl

中文:
引理 Antitone.isCoboundedUnder_le_of_isCobounded
  结论: {f : R -> S} (f_decr : Antitone f)
  证明: by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_le cobdd
exact IsCobounded.of_frequently_ge f_decr.frequently_ge_map_of_frequently_le hl

Depends on / 依赖: IsCobounded, IsCobounded.frequently_le, IsCobounded.of_frequently_ge, f_decr, f_decr.frequently_ge_map_of_frequently_le, frequently_ge_map_of_frequently_le, frequently_le, of_frequently_ge
-/
lemma Antitone.isCoboundedUnder_le_of_isCobounded {f : R -> S} (f_decr : Antitone f)
    [NeBot F] (cobdd : IsCobounded (fun x1 x2 => x2 <= x1) F) :
    F.IsCoboundedUnder (· <= ·) f := by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_le cobdd
exact IsCobounded.of_frequently_ge f_decr.frequently_ge_map_of_frequently_le hl

end FrequentlyBounded
