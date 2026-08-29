/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Disjoint
public import Mathlib.Order.Filter.Tendsto

/-!
# Limits of `Filter.atTop` and `Filter.atBot`

In this file we prove many lemmas on the combination of `Filter.atTop` and `Filter.atBot`
and `Tendsto`.
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual]
/--
theorem `not_tendsto_const_atTop` / 定理 `not_tendsto_const_atTop`

English:
theorem not_tendsto_const_atTop
  given: [Preorder α] [NoTopOrder α] (x : α) (l : Filter β) [l.NeBot]
  proof: tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)

@[to_dual eventually_lt_atBot]

中文:
定理 not_tendsto_const_atTop
  条件: [预序 α] [无顶序 α] (x : α) (l : 滤子 β) [l.NeBot]
  证明: tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)

@[to_dual eventually_lt_atBot]

Depends on / 依赖: disjoint_pure_atTop, not_tendsto, tendsto_const_pure, tendsto_const_pure.not_tendsto
-/
theorem not_tendsto_const_atTop [Preorder α] [NoTopOrder α] (x : α) (l : Filter β) [l.NeBot] :
    ¬Tendsto (fun _ => x) l atTop :=
  tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)

@[to_dual eventually_lt_atBot]
/--
theorem `Tendsto.eventually_gt_atTop` / 定理 `Tendsto.eventually_gt_atTop`

English:
theorem Tendsto.eventually_gt_atTop
  statement: [Preorder β] [NoTopOrder β] {f : α -> β} {l : Filter α}
  proof: hf.eventually (eventually_gt_atTop c)

@[to_dual eventually_le_atBot]

中文:
定理 收敛.eventually_gt_atTop
  结论: [预序 β] [无顶序 β] {f : α -> β} {l : 滤子 α}
  证明: hf.eventually (eventually_gt_atTop c)

@[to_dual eventually_le_atBot]
-/
protected theorem Tendsto.eventually_gt_atTop [Preorder β] [NoTopOrder β] {f : α -> β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : forallᶠ x in l, c < f x :=
  hf.eventually (eventually_gt_atTop c)

@[to_dual eventually_le_atBot]
/--
theorem `Tendsto.eventually_ge_atTop` / 定理 `Tendsto.eventually_ge_atTop`

English:
theorem Tendsto.eventually_ge_atTop
  statement: [Preorder β] {f : α -> β} {l : Filter α}
  proof: hf.eventually (eventually_ge_atTop c)

@[to_dual]

中文:
定理 收敛.eventually_ge_atTop
  结论: [预序 β] {f : α -> β} {l : 滤子 α}
  证明: hf.eventually (eventually_ge_atTop c)

@[to_dual]
-/
protected theorem Tendsto.eventually_ge_atTop [Preorder β] {f : α -> β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : forallᶠ x in l, c <= f x :=
  hf.eventually (eventually_ge_atTop c)

@[to_dual]
/--
theorem `Tendsto.eventually_ne_atTop` / 定理 `Tendsto.eventually_ne_atTop`

English:
theorem Tendsto.eventually_ne_atTop
  statement: [Preorder β] [NoTopOrder β] {f : α -> β} {l : Filter α}
  proof: hf.eventually (eventually_ne_atTop c)

中文:
定理 收敛.eventually_ne_atTop
  结论: [预序 β] [无顶序 β] {f : α -> β} {l : 滤子 α}
  证明: hf.eventually (eventually_ne_atTop c)
-/
protected theorem Tendsto.eventually_ne_atTop [Preorder β] [NoTopOrder β] {f : α -> β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : forallᶠ x in l, f x != c :=
  hf.eventually (eventually_ne_atTop c)

/--
theorem `Tendsto.eventually_ne_atTop'` / 定理 `Tendsto.eventually_ne_atTop'`

English:
theorem Tendsto.eventually_ne_atTop'
  statement: [Preorder β] [NoTopOrder β] {f : α -> β}
  proof: (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f

@[to_dual OrderBot.atBot_eq]

中文:
定理 收敛.eventually_ne_atTop'
  结论: [预序 β] [无顶序 β] {f : α -> β}
  证明: (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f

@[to_dual OrderBot.atBot_eq]
-/
protected theorem Tendsto.eventually_ne_atTop' [Preorder β] [NoTopOrder β] {f : α -> β}
    {l : Filter α} (hf : Tendsto f l atTop) (c : α) : forallᶠ x in l, x != c :=
  (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f

@[to_dual OrderBot.atBot_eq]
/--
theorem `OrderTop.atTop_eq` / 定理 `OrderTop.atTop_eq`

English:
theorem OrderTop.atTop_eq
  given: (α) [PartialOrder α] [OrderTop α]
  statement: (atTop : Filter α) = pure ⊤
  proof: by
  rw [isTop_top.atTop_eq]; rw [Ici_top]; rw [principal_singleton]

@[to_dual]

中文:
定理 有顶序.atTop_eq
  条件: (α) [偏序 α] [有顶序 α]
  结论: (atTop : 滤子 α) = pure ⊤
  证明: by
  rw [isTop_top.atTop_eq]; rw [Ici_top]; rw [principal_singleton]

@[to_dual]

Depends on / 依赖: Ici_top, atTop_eq, isTop_top, isTop_top.atTop_eq, principal_singleton
-/
theorem OrderTop.atTop_eq (α) [PartialOrder α] [OrderTop α] : (atTop : Filter α) = pure ⊤ := by
  rw [isTop_top.atTop_eq]; rw [Ici_top]; rw [principal_singleton]

@[to_dual]
/--
theorem `tendsto_atTop_pure` / 定理 `tendsto_atTop_pure`

English:
theorem tendsto_atTop_pure
  given: [PartialOrder α] [OrderTop α] (f : α -> β)
  proof: (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _

@[to_dual]

中文:
定理 tendsto_atTop_pure
  条件: [偏序 α] [有顶序 α] (f : α -> β)
  证明: (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _

@[to_dual]

Depends on / 依赖: OrderTop, OrderTop.atTop_eq, atTop_eq, tendsto_pure_pure
-/
theorem tendsto_atTop_pure [PartialOrder α] [OrderTop α] (f : α -> β) :
    Tendsto f atTop (pure <| f ⊤) :=
  (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _

@[to_dual]
/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  given: [Preorder β] {m : α -> β} {f : Filter α}
  proof: by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]

@[to_dual]

中文:
定理 tendsto_atTop
  条件: [预序 β] {m : α -> β} {f : 滤子 α}
  证明: by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]

@[to_dual]

Depends on / 依赖: mem_Ici, tendsto_iInf, tendsto_principal
-/
theorem tendsto_atTop [Preorder β] {m : α -> β} {f : Filter α} :
    Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a := by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]

@[to_dual]
/--
theorem `tendsto_atTop_mono'` / 定理 `tendsto_atTop_mono'`

English:
theorem tendsto_atTop_mono'
  given: [Preorder β] (l : Filter α) ⦃f₁ f₂
  statement: α -> β⦄ (h : f₁ <=ᶠ[l] f₂)
  proof: tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans

@[to_dual]

中文:
定理 tendsto_atTop_mono'
  条件: [预序 β] (l : 滤子 α) ⦃f₁ f₂
  结论: α -> β⦄ (h : f₁ <=ᶠ[l] f₂)
  证明: tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans

@[to_dual]

Depends on / 依赖: filter_upwards, le_trans, tendsto_atTop
-/
theorem tendsto_atTop_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂)
    (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l atTop :=
  tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans

@[to_dual]
/--
theorem `tendsto_atTop_mono` / 定理 `tendsto_atTop_mono`

English:
theorem tendsto_atTop_mono
  given: [Preorder β] {l : Filter α} {f g : α -> β} (h : forall n, f n <= g n)
  proof: tendsto_atTop_mono' l Eventually.of_forall h

中文:
定理 tendsto_atTop_mono
  条件: [预序 β] {l : 滤子 α} {f g : α -> β} (h : 对任意 n, f n <= g n)
  证明: tendsto_atTop_mono' l Eventually.of_forall h

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, tendsto_atTop_mono
-/
theorem tendsto_atTop_mono [Preorder β] {l : Filter α} {f g : α -> β} (h : forall n, f n <= g n) :
    Tendsto f l atTop -> Tendsto g l atTop :=
tendsto_atTop_mono' l Eventually.of_forall h

end Filter

namespace Filter


/--
theorem `_root_.StrictMono.tendsto_atTop` / 定理 `_root_.StrictMono.tendsto_atTop`

English:
theorem _root_.StrictMono.tendsto_atTop
  given: {φ : Nat -> Nat} (h : StrictMono φ)
  statement: Tendsto φ atTop atTop
  proof: tendsto_atTop_mono h.id_le tendsto_id

中文:
定理 _root_.严格递增.tendsto_atTop
  条件: {φ : 自然数 -> 自然数} (h : 严格递增 φ)
  结论: 收敛 φ atTop atTop
  证明: tendsto_atTop_mono h.id_le tendsto_id

Depends on / 依赖: h.id_le, id_le, tendsto_atTop_mono, tendsto_id
-/
theorem _root_.StrictMono.tendsto_atTop {φ : Nat -> Nat} (h : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_mono h.id_le tendsto_id

/-- If `f` is a monotone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`.

This lemma together with `exists_seq_monotone_tendsto_atTop_atTop` below
is useful to reduce a statement
about a monotone family indexed by a type with countably generated `atTop` (e.g., `ℝ`)
to the case of a family indexed by natural numbers. -/
@[to_dual
/-- If `f` is a monotone function and `g` tends to `atBot` along a nontrivial filter.
then the lower bounds of the range of `f ∘ g`
are the same as the lower bounds of the range of `f`. -/]
/--
theorem `_root_.Monotone.upperBounds_range_comp_tendsto_atTop` / 定理 `_root_.Monotone.upperBounds_range_comp_tendsto_atTop`

English:
theorem _root_.Monotone.upperBounds_range_comp_tendsto_atTop
  statement: [Preorder β] [Preorder γ]
  proof: by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : exists a, b <= g a := (hg.eventually_ge_atTop b).exists
exact (hf ha).trans hc mem_range_self _

中文:
定理 _root_.递增.upperBounds_range_comp_tendsto_atTop
  结论: [预序 β] [预序 γ]
  证明: by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : exists a, b <= g a := (hg.eventually_ge_atTop b).exists
exact (hf ha).trans hc mem_range_self _

Depends on / 依赖: Subset, Subset.antisymm, antisymm, eventually_ge_atTop, hg.eventually_ge_atTop, mem_range_self, range_comp_subset_range, upperBounds_mono_set
-/
theorem _root_.Monotone.upperBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Monotone f) {g : α -> β} (hg : Tendsto g l atTop) :
    upperBounds (range (f ∘ g)) = upperBounds (range f) := by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : exists a, b <= g a := (hg.eventually_ge_atTop b).exists
exact (hf ha).trans hc mem_range_self _

/-- If `f` is an antitone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/
@[to_dual
/-- If `f` is an antitone function and `g` tends to `atBot` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/]
/--
theorem `_root_.Antitone.lowerBounds_range_comp_tendsto_atTop` / 定理 `_root_.Antitone.lowerBounds_range_comp_tendsto_atTop`

English:
theorem _root_.Antitone.lowerBounds_range_comp_tendsto_atTop
  statement: [Preorder β] [Preorder γ]
  proof: hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg

@[to_dual]

中文:
定理 _root_.递减.lowerBounds_range_comp_tendsto_atTop
  结论: [预序 β] [预序 γ]
  证明: hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg

@[to_dual]

Depends on / 依赖: dual_left, hf.dual_left.lowerBounds_range_comp_tendsto_atBot, lowerBounds_range_comp_tendsto_atBot
-/
theorem _root_.Antitone.lowerBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β -> γ} (hf : Antitone f) {g : α -> β} (hg : Tendsto g l atTop) :
    lowerBounds (range (f ∘ g)) = lowerBounds (range f) :=
  hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg

@[to_dual]
/--
theorem `tendsto_atTop_atTop_of_monotone` / 定理 `tendsto_atTop_atTop_of_monotone`

English:
theorem tendsto_atTop_atTop_of_monotone
  statement: [Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f)
  proof: tendsto_iInf.2 fun b =>
tendsto_principal.2
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')

@[to_dual]

中文:
定理 tendsto_atTop_atTop_of_monotone
  结论: [预序 α] [预序 β] {f : α -> β} (hf : 递增 f)
  证明: tendsto_iInf.2 fun b =>
tendsto_principal.2
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')

@[to_dual]

Depends on / 依赖: le_trans, mem_atTop, mem_of_superset, tendsto_iInf, tendsto_principal
-/
theorem tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f)
    (h : forall b, exists a, b <= f a) : Tendsto f atTop atTop :=
  tendsto_iInf.2 fun b =>
tendsto_principal.2
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')

@[to_dual]
/--
theorem `tendsto_atTop_atBot_of_antitone` / 定理 `tendsto_atTop_atBot_of_antitone`

English:
theorem tendsto_atTop_atBot_of_antitone
  statement: [Preorder α] [Preorder β] {f : α -> β} (hf : Antitone f)
  proof: @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone

@[to_dual]

中文:
定理 tendsto_atTop_atBot_of_antitone
  结论: [预序 α] [预序 β] {f : α -> β} (hf : 递减 f)
  证明: @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone

@[to_dual]

Depends on / 依赖: tendsto_atTop_atTop_of_monotone
-/
theorem tendsto_atTop_atBot_of_antitone [Preorder α] [Preorder β] {f : α -> β} (hf : Antitone f)
    (h : forall b, exists a, f a <= b) : Tendsto f atTop atBot :=
  @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone

@[to_dual]
/--
theorem `comap_embedding_atTop` / 定理 `comap_embedding_atTop`

English:
theorem comap_embedding_atTop
  statement: [Preorder β] [Preorder γ] {e : β -> γ}
  proof: le_antisymm
    (le_iInf fun b =>
le_principal_iff.2 mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap

中文:
定理 comap_embedding_atTop
  结论: [预序 β] [预序 γ] {e : β -> γ}
  证明: le_antisymm
    (le_iInf fun b =>
le_principal_iff.2 mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap

Depends on / 依赖: le_antisymm, le_comap, le_iInf, le_principal_iff, mem_atTop, mem_comap, tendsto_atTop_atTop_of_monotone
-/
theorem comap_embedding_atTop [Preorder β] [Preorder γ] {e : β -> γ}
    (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, exists b, c <= e b) : comap e atTop = atTop :=
  le_antisymm
    (le_iInf fun b =>
le_principal_iff.2 mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap

/-- A function `f` goes to `∞` independent of an order-preserving embedding `e`. -/
@[to_dual (reorder := hm (b₁ b₂))
/-- A function `f` goes to `-∞` independent of an order-preserving embedding `e`. -/]
/--
theorem `tendsto_atTop_embedding` / 定理 `tendsto_atTop_embedding`

English:
theorem tendsto_atTop_embedding
  statement: [Preorder β] [Preorder γ] {f : α -> β} {e : β -> γ} {l : Filter α}
  proof: by
  rw [← comap_embedding_atTop hm hu]; rw [tendsto_comap_iff]

中文:
定理 tendsto_atTop_embedding
  结论: [预序 β] [预序 γ] {f : α -> β} {e : β -> γ} {l : 滤子 α}
  证明: by
  rw [← comap_embedding_atTop hm hu]; rw [tendsto_comap_iff]

Depends on / 依赖: comap_embedding_atTop, tendsto_comap_iff
-/
theorem tendsto_atTop_embedding [Preorder β] [Preorder γ] {f : α -> β} {e : β -> γ} {l : Filter α}
    (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, exists b, c <= e b) :
    Tendsto (e ∘ f) l atTop ↔ Tendsto f l atTop := by
  rw [← comap_embedding_atTop hm hu]; rw [tendsto_comap_iff]

/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
above, then `Tendsto u atTop atTop`. -/
@[to_dual
/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
below, then `Tendsto u atBot atBot`. -/]
/--
theorem `tendsto_atTop_atTop_of_monotone'` / 定理 `tendsto_atTop_atTop_of_monotone'`

English:
theorem tendsto_atTop_atTop_of_monotone'
  statement: [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u)
  proof: by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩

中文:
定理 tendsto_atTop_atTop_of_monotone'
  结论: [预序 ι] [线性序 α] {u : ι -> α} (h : 递增 u)
  证明: by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩

Depends on / 依赖: h.tendsto_atTop_atTop, le_of_lt, not_bddAbove_iff, tendsto_atTop_atTop
-/
theorem tendsto_atTop_atTop_of_monotone' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u)
    (H : ¬BddAbove (range u)) : Tendsto u atTop atTop := by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩

/-- If a monotone function `u : ι → α` tends to `atTop` along *some* non-trivial filter `l`, then
it tends to `atTop` along `atTop`. -/
@[to_dual
/-- If a monotone function `u : ι → α` tends to `atBot` along *some* non-trivial filter `l`, then
it tends to `atBot` along `atBot`. -/]
/--
theorem `tendsto_atTop_of_monotone_of_filter` / 定理 `tendsto_atTop_of_monotone_of_filter`

English:
theorem tendsto_atTop_of_monotone_of_filter
  statement: [Preorder ι] [Preorder α] {l : Filter ι} {u : ι -> α}
  proof: h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists

@[to_dual]

中文:
定理 tendsto_atTop_of_monotone_of_filter
  结论: [预序 ι] [预序 α] {l : 滤子 ι} {u : ι -> α}
  证明: h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists

@[to_dual]

Depends on / 依赖: eventually, h.tendsto_atTop_atTop, hu.eventually, mem_atTop, tendsto_atTop_atTop
-/
theorem tendsto_atTop_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι -> α}
    (h : Monotone u) [NeBot l] (hu : Tendsto u l atTop) : Tendsto u atTop atTop :=
  h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists

@[to_dual]
/--
theorem `tendsto_atTop_of_monotone_of_subseq` / 定理 `tendsto_atTop_of_monotone_of_subseq`

English:
theorem tendsto_atTop_of_monotone_of_subseq
  statement: [Preorder ι] [Preorder α] {u : ι -> α} {φ : ι' -> ι}
  proof: tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)

中文:
定理 tendsto_atTop_of_monotone_of_subseq
  结论: [预序 ι] [预序 α] {u : ι -> α} {φ : ι' -> ι}
  证明: tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)

Depends on / 依赖: tendsto_atTop_of_monotone_of_filter, tendsto_map
-/
theorem tendsto_atTop_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι -> α} {φ : ι' -> ι}
    (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l atTop) :
    Tendsto u atTop atTop :=
  tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)

end Filter
