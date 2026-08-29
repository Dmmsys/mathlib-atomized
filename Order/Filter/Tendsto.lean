/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Map

/-!
# Convergence in terms of filters

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from `Topology/Basic`.
-/

public section

open Set Filter

variable {α β γ : Type*} {ι : Sort*}

namespace Filter

/--
theorem `tendsto_def` / 定理 `tendsto_def`

English:
theorem tendsto_def
  given: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β}
  proof: Iff.rfl

中文:
定理 tendsto_def
  条件: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁ :=
  Iff.rfl

/--
theorem `tendsto_iff_eventually` / 定理 `tendsto_iff_eventually`

English:
theorem tendsto_iff_eventually
  given: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β}
  proof: Iff.rfl

中文:
定理 tendsto_iff_eventually
  条件: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem tendsto_iff_eventually {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ forall ⦃p : β -> Prop⦄, (forallᶠ y in l₂, p y) -> forallᶠ x in l₁, p (f x) :=
  Iff.rfl

/--
theorem `tendsto_iff_forall_eventually_mem` / 定理 `tendsto_iff_forall_eventually_mem`

English:
theorem tendsto_iff_forall_eventually_mem
  given: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β}
  proof: Iff.rfl

中文:
定理 tendsto_iff_对任意_eventually_mem
  条件: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem tendsto_iff_forall_eventually_mem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ forall s in l₂, forallᶠ x in l₁, f x in s :=
  Iff.rfl

/--
lemma `Tendsto.eventually_mem` / 引理 `Tendsto.eventually_mem`

English:
lemma Tendsto.eventually_mem
  statement: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
  proof: hf h

中文:
引理 收敛.eventually_mem
  结论: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} {s : 集合 β}
  证明: hf h
-/
lemma Tendsto.eventually_mem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
    (hf : Tendsto f l₁ l₂) (h : s in l₂) : forallᶠ x in l₁, f x in s :=
  hf h

/--
theorem `Tendsto.eventually` / 定理 `Tendsto.eventually`

English:
theorem Tendsto.eventually
  statement: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {p : β -> Prop}
  proof: hf h

中文:
定理 收敛.eventually
  结论: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} {p : β -> 命题}
  证明: hf h
-/
theorem Tendsto.eventually {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {p : β -> Prop}
    (hf : Tendsto f l₁ l₂) (h : forallᶠ y in l₂, p y) : forallᶠ x in l₁, p (f x) :=
  hf h

/--
theorem `not_tendsto_iff_exists_frequently_notMem` / 定理 `not_tendsto_iff_exists_frequently_notMem`

English:
theorem not_tendsto_iff_exists_frequently_notMem
  given: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β}
  proof: by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]

中文:
定理 not_tendsto_iff_存在_frequently_notMem
  条件: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]

Depends on / 依赖: exists_prop, not_eventually, not_forall, tendsto_iff_forall_eventually_mem
-/
theorem not_tendsto_iff_exists_frequently_notMem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} :
    ¬Tendsto f l₁ l₂ ↔ exists s in l₂, existsᶠ x in l₁, f x ∉ s := by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]

/--
theorem `Tendsto.frequently` / 定理 `Tendsto.frequently`

English:
theorem Tendsto.frequently
  statement: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {p : β -> Prop}
  proof: mt hf.eventually h

中文:
定理 收敛.frequently
  结论: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} {p : β -> 命题}
  证明: mt hf.eventually h

Depends on / 依赖: eventually, hf.eventually
-/
theorem Tendsto.frequently {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} {p : β -> Prop}
    (hf : Tendsto f l₁ l₂) (h : existsᶠ x in l₁, p (f x)) : existsᶠ y in l₂, p y :=
  mt hf.eventually h

/--
theorem `Tendsto.frequently_map` / 定理 `Tendsto.frequently_map`

English:
theorem Tendsto.frequently_map
  statement: {l₁ : Filter α} {l₂ : Filter β} {p : α -> Prop} {q : β -> Prop}
  proof: c.frequently (h.mono w)

@[simp]

中文:
定理 收敛.frequently_map
  结论: {l₁ : 滤子 α} {l₂ : 滤子 β} {p : α -> 命题} {q : β -> 命题}
  证明: c.frequently (h.mono w)

@[simp]

Depends on / 依赖: c.frequently, frequently, h.mono
-/
theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α -> Prop} {q : β -> Prop}
    (f : α -> β) (c : Filter.Tendsto f l₁ l₂) (w : forall x, p x -> q (f x)) (h : existsᶠ x in l₁, p x) :
    existsᶠ y in l₂, q y :=
  c.frequently (h.mono w)

@[simp]
/--
theorem `tendsto_bot` / 定理 `tendsto_bot`

English:
theorem tendsto_bot
  given: {f : α -> β} {l : Filter β}
  statement: Tendsto f ⊥ l
  proof: by simp [Tendsto]

@[simp]

中文:
定理 tendsto_bot
  条件: {f : α -> β} {l : 滤子 β}
  结论: 收敛 f ⊥ l
  证明: by simp [Tendsto]

@[simp]

Depends on / 依赖: Tendsto
-/
theorem tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f ⊥ l := by simp [Tendsto]

@[simp]
/--
theorem `tendsto_bot_right_iff` / 定理 `tendsto_bot_right_iff`

English:
theorem tendsto_bot_right_iff
  given: {f : α -> β} {l : Filter α}
  statement: Tendsto f l ⊥ ↔ l = ⊥
  proof: by
  simp [Tendsto]

中文:
定理 tendsto_bot_right_iff
  条件: {f : α -> β} {l : 滤子 α}
  结论: 收敛 f l ⊥ ↔ l = ⊥
  证明: by
  simp [Tendsto]

Depends on / 依赖: Tendsto
-/
theorem tendsto_bot_right_iff {f : α -> β} {l : Filter α} : Tendsto f l ⊥ ↔ l = ⊥ := by
  simp [Tendsto]

/--
theorem `Tendsto.of_neBot_imp` / 定理 `Tendsto.of_neBot_imp`

English:
theorem Tendsto.of_neBot_imp
  statement: {f : α -> β} {la : Filter α} {lb : Filter β}
  proof: by
  rcases eq_or_neBot la with rfl | hla
  · exact tendsto_bot
  · exact h hla

中文:
定理 收敛.of_neBot_imp
  结论: {f : α -> β} {la : 滤子 α} {lb : 滤子 β}
  证明: by
  rcases eq_or_neBot la with rfl | hla
  · exact tendsto_bot
  · exact h hla

Depends on / 依赖: eq_or_neBot, tendsto_bot
-/
theorem Tendsto.of_neBot_imp {f : α -> β} {la : Filter α} {lb : Filter β}
    (h : NeBot la -> Tendsto f la lb) : Tendsto f la lb := by
  rcases eq_or_neBot la with rfl | hla
  · exact tendsto_bot
  · exact h hla

/--
theorem `tendsto_top` / 定理 `tendsto_top`

English:
theorem tendsto_top
  given: {f : α -> β} {l : Filter α}
  statement: Tendsto f l ⊤
  proof: le_top

中文:
定理 tendsto_top
  条件: {f : α -> β} {l : 滤子 α}
  结论: 收敛 f l ⊤
  证明: le_top
-/
@[simp] theorem tendsto_top {f : α -> β} {l : Filter α} : Tendsto f l ⊤ := le_top

/--
theorem `le_map_of_right_inverse` / 定理 `le_map_of_right_inverse`

English:
theorem le_map_of_right_inverse
  statement: {mab : α -> β} {mba : β -> α} {f : Filter α} {g : Filter β}
  proof: by
  rw [← @map_id _ g]; rw [← map_congr h₁]; rw [← map_map]
  exact map_mono h₂

中文:
定理 le_map_of_right_inverse
  结论: {mab : α -> β} {mba : β -> α} {f : 滤子 α} {g : 滤子 β}
  证明: by
  rw [← @map_id _ g]; rw [← map_congr h₁]; rw [← map_map]
  exact map_mono h₂

Depends on / 依赖: map_congr, map_id, map_map, map_mono
-/
theorem le_map_of_right_inverse {mab : α -> β} {mba : β -> α} {f : Filter α} {g : Filter β}
    (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g <= map mab f := by
  rw [← @map_id _ g]; rw [← map_congr h₁]; rw [← map_map]
  exact map_mono h₂

/--
theorem `tendsto_of_isEmpty` / 定理 `tendsto_of_isEmpty`

English:
theorem tendsto_of_isEmpty
  given: [IsEmpty α] {f : α -> β} {la : Filter α} {lb : Filter β}
  proof: by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]

中文:
定理 tendsto_of_isEmpty
  条件: [是空 α] {f : α -> β} {la : 滤子 α} {lb : 滤子 β}
  证明: by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]

Depends on / 依赖: filter_eq_bot_of_isEmpty, tendsto_bot
-/
theorem tendsto_of_isEmpty [IsEmpty α] {f : α -> β} {la : Filter α} {lb : Filter β} :
    Tendsto f la lb := by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]

/--
theorem `eventuallyEq_of_left_inv_of_right_inv` / 定理 `eventuallyEq_of_left_inv_of_right_inv`

English:
theorem eventuallyEq_of_left_inv_of_right_inv
  statement: {f : α -> β} {g₁ g₂ : β -> α} {fa : Filter α}
  proof: (htendsto.eventually hleft).mp hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl

中文:
定理 eventuallyEq_of_left_inv_of_right_inv
  结论: {f : α -> β} {g₁ g₂ : β -> α} {fa : 滤子 α}
  证明: (htendsto.eventually hleft).mp hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl

Depends on / 依赖: congr_arg, eventually, hr.symm, hright, hright.mono, htendsto, htendsto.eventually
-/
theorem eventuallyEq_of_left_inv_of_right_inv {f : α -> β} {g₁ g₂ : β -> α} {fa : Filter α}
    {fb : Filter β} (hleft : forallᶠ x in fa, g₁ (f x) = x) (hright : forallᶠ y in fb, f (g₂ y) = y)
    (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂ :=
(htendsto.eventually hleft).mp hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl

/--
theorem `tendsto_iff_comap` / 定理 `tendsto_iff_comap`

English:
theorem tendsto_iff_comap
  given: {f : α -> β} {l₁ : Filter α} {l₂ : Filter β}
  proof: map_le_iff_le_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap

中文:
定理 tendsto_iff_comap
  条件: {f : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β}
  证明: map_le_iff_le_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap

Depends on / 依赖: map_le_iff_le_comap
-/
theorem tendsto_iff_comap {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f :=
  map_le_iff_le_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap

/--
theorem `Tendsto.disjoint` / 定理 `Tendsto.disjoint`

English:
theorem Tendsto.disjoint
  statement: {f : α -> β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
  proof: (disjoint_comap hd).mono h₁.le_comap h₂.le_comap

中文:
定理 收敛.disjoint
  结论: {f : α -> β} {la₁ la₂ : 滤子 α} {lb₁ lb₂ : 滤子 β}
  证明: (disjoint_comap hd).mono h₁.le_comap h₂.le_comap
-/
protected theorem Tendsto.disjoint {f : α -> β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
    (h₁ : Tendsto f la₁ lb₁) (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap

/--
theorem `tendsto_congr'` / 定理 `tendsto_congr'`

English:
theorem tendsto_congr'
  given: {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
  proof: by rw [Tendsto, Tendsto, map_congr hl]

中文:
定理 tendsto_congr'
  条件: {f₁ f₂ : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} (hl : f₁ =ᶠ[l₁] f₂)
  证明: by rw [Tendsto, Tendsto, map_congr hl]

Depends on / 依赖: Tendsto, map_congr
-/
theorem tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by rw [Tendsto, Tendsto, map_congr hl]

/--
theorem `Tendsto.congr'` / 定理 `Tendsto.congr'`

English:
theorem Tendsto.congr'
  statement: {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
  proof: (tendsto_congr' hl).1 h

中文:
定理 收敛.congr'
  结论: {f₁ f₂ : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} (hl : f₁ =ᶠ[l₁] f₂)
  证明: (tendsto_congr' hl).1 h

Depends on / 依赖: tendsto_congr
-/
theorem Tendsto.congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
    (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h

/--
theorem `tendsto_congr` / 定理 `tendsto_congr`

English:
theorem tendsto_congr
  given: {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (h : forall x, f₁ x = f₂ x)
  proof: tendsto_congr' (univ_mem' h)

中文:
定理 tendsto_congr
  条件: {f₁ f₂ : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} (h : 对任意 x, f₁ x = f₂ x)
  证明: tendsto_congr' (univ_mem' h)

Depends on / 依赖: tendsto_congr, univ_mem
-/
theorem tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (h : forall x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)

/--
theorem `Tendsto.congr` / 定理 `Tendsto.congr`

English:
theorem Tendsto.congr
  given: {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (h : forall x, f₁ x = f₂ x)
  proof: (tendsto_congr h).1

中文:
定理 收敛.congr
  条件: {f₁ f₂ : α -> β} {l₁ : 滤子 α} {l₂ : 滤子 β} (h : 对任意 x, f₁ x = f₂ x)
  证明: (tendsto_congr h).1

Depends on / 依赖: tendsto_congr
-/
theorem Tendsto.congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (h : forall x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ -> Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1

/--
theorem `tendsto_id'` / 定理 `tendsto_id'`

English:
theorem tendsto_id'
  given: {x y : Filter α}
  statement: Tendsto id x y ↔ x <= y
  proof: Iff.rfl

中文:
定理 tendsto_id'
  条件: {x y : 滤子 α}
  结论: 收敛 id x y ↔ x <= y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <= y :=
  Iff.rfl

/--
theorem `tendsto_id` / 定理 `tendsto_id`

English:
theorem tendsto_id
  given: {x : Filter α}
  statement: Tendsto id x x
  proof: le_refl x

中文:
定理 tendsto_id
  条件: {x : 滤子 α}
  结论: 收敛 id x x
  证明: le_refl x

Depends on / 依赖: le_refl
-/
theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_refl x

/--
theorem `Tendsto.comp` / 定理 `Tendsto.comp`

English:
theorem Tendsto.comp
  statement: {f : α -> β} {g : β -> γ} {x : Filter α} {y : Filter β} {z : Filter γ}
  proof: fun _ hs => hf (hg hs)

中文:
定理 收敛.comp
  结论: {f : α -> β} {g : β -> γ} {x : 滤子 α} {y : 滤子 β} {z : 滤子 γ}
  证明: fun _ hs => hf (hg hs)
-/
theorem Tendsto.comp {f : α -> β} {g : β -> γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hg : Tendsto g y z) (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun _ hs => hf (hg hs)

/--
theorem `Tendsto.iterate` / 定理 `Tendsto.iterate`

English:
theorem Tendsto.iterate
  given: {f : α -> α} {l : Filter α} (h : Tendsto f l l)

中文:
定理 收敛.iterate
  条件: {f : α -> α} {l : 滤子 α} (h : 收敛 f l l)
-/
protected theorem Tendsto.iterate {f : α -> α} {l : Filter α} (h : Tendsto f l l) :
    forall n, Tendsto (f^[n]) l l
  | 0 => tendsto_id
  | (n + 1) => (h.iterate n).comp h

/--
theorem `Tendsto.mono_left` / 定理 `Tendsto.mono_left`

English:
theorem Tendsto.mono_left
  statement: {f : α -> β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
  proof: (map_mono h).trans hx

中文:
定理 收敛.mono_left
  结论: {f : α -> β} {x y : 滤子 α} {z : 滤子 β} (hx : 收敛 f x z)
  证明: (map_mono h).trans hx

Depends on / 依赖: map_mono
-/
theorem Tendsto.mono_left {f : α -> β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
    (h : y <= x) : Tendsto f y z :=
  (map_mono h).trans hx

/--
theorem `Tendsto.mono_right` / 定理 `Tendsto.mono_right`

English:
theorem Tendsto.mono_right
  statement: {f : α -> β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
  proof: le_trans hy hz

中文:
定理 收敛.mono_right
  结论: {f : α -> β} {x : 滤子 α} {y z : 滤子 β} (hy : 收敛 f x y)
  证明: le_trans hy hz

Depends on / 依赖: le_trans
-/
theorem Tendsto.mono_right {f : α -> β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
    (hz : y <= z) : Tendsto f x z :=
  le_trans hy hz

/--
theorem `Tendsto.neBot` / 定理 `Tendsto.neBot`

English:
theorem Tendsto.neBot
  given: {f : α -> β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x]
  proof: (hx.map _).mono h

中文:
定理 收敛.neBot
  条件: {f : α -> β} {x : 滤子 α} {y : 滤子 β} (h : 收敛 f x y) [hx : NeBot x]
  证明: (hx.map _).mono h

Depends on / 依赖: hx.map
-/
theorem Tendsto.neBot {f : α -> β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] :
    NeBot y :=
  (hx.map _).mono h

/--
theorem `tendsto_map` / 定理 `tendsto_map`

English:
theorem tendsto_map
  given: {f : α -> β} {x : Filter α}
  statement: Tendsto f x (map f x)
  proof: le_refl (map f x)

@[simp]

中文:
定理 tendsto_map
  条件: {f : α -> β} {x : 滤子 α}
  结论: 收敛 f x (map f x)
  证明: le_refl (map f x)

@[simp]

Depends on / 依赖: le_refl
-/
theorem tendsto_map {f : α -> β} {x : Filter α} : Tendsto f x (map f x) :=
  le_refl (map f x)

@[simp]
/--
theorem `tendsto_map'_iff` / 定理 `tendsto_map'_iff`

English:
theorem tendsto_map'_iff
  given: {f : β -> γ} {g : α -> β} {x : Filter α} {y : Filter γ}
  proof: by
  rw [Tendsto]; rw [Tendsto]; rw [map_map]

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff

中文:
定理 tendsto_map'_iff
  条件: {f : β -> γ} {g : α -> β} {x : 滤子 α} {y : 滤子 γ}
  证明: by
  rw [Tendsto]; rw [Tendsto]; rw [map_map]

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff

Depends on / 依赖: Tendsto, map_map
-/
theorem tendsto_map'_iff {f : β -> γ} {g : α -> β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y := by
  rw [Tendsto]; rw [Tendsto]; rw [map_map]

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff

/--
theorem `tendsto_comap` / 定理 `tendsto_comap`

English:
theorem tendsto_comap
  given: {f : α -> β} {x : Filter β}
  statement: Tendsto f (comap f x) x
  proof: map_comap_le

@[simp]

中文:
定理 tendsto_comap
  条件: {f : α -> β} {x : 滤子 β}
  结论: 收敛 f (comap f x) x
  证明: map_comap_le

@[simp]

Depends on / 依赖: map_comap_le
-/
theorem tendsto_comap {f : α -> β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le

@[simp]
/--
theorem `tendsto_comap_iff` / 定理 `tendsto_comap_iff`

English:
theorem tendsto_comap_iff
  given: {f : α -> β} {g : β -> γ} {a : Filter α} {c : Filter γ}
  proof: ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp by rwa [map_map]⟩

中文:
定理 tendsto_comap_iff
  条件: {f : α -> β} {g : β -> γ} {a : 滤子 α} {c : 滤子 γ}
  证明: ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp by rwa [map_map]⟩

Depends on / 依赖: map_le_iff_le_comap, map_le_iff_le_comap.mp, map_map, tendsto_comap, tendsto_comap.comp
-/
theorem tendsto_comap_iff {f : α -> β} {g : β -> γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp by rwa [map_map]⟩

/--
theorem `tendsto_comap'_iff` / 定理 `tendsto_comap'_iff`

English:
theorem tendsto_comap'_iff
  given: {m : α -> β} {f : Filter α} {g : Filter β} {i : γ -> α} (h : range i in f)
  proof: by
  rw [Tendsto]; rw [← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]

中文:
定理 tendsto_comap'_iff
  条件: {m : α -> β} {f : 滤子 α} {g : 滤子 β} {i : γ -> α} (h : range i in f)
  证明: by
  rw [Tendsto]; rw [← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]

Depends on / 依赖: Tendsto, map_comap_of_mem, map_compose
-/
theorem tendsto_comap'_iff {m : α -> β} {f : Filter α} {g : Filter β} {i : γ -> α} (h : range i in f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g := by
  rw [Tendsto]; rw [← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]

/--
theorem `Tendsto.of_tendsto_comp` / 定理 `Tendsto.of_tendsto_comp`

English:
theorem Tendsto.of_tendsto_comp
  statement: {f : α -> β} {g : β -> γ} {a : Filter α} {b : Filter β} {c : Filter γ}
  proof: by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a <= comap (g ∘ f) c := hfg
    _ <= comap f b := by simpa [comap_comap] using comap_mono hg

中文:
定理 收敛.of_tendsto_comp
  结论: {f : α -> β} {g : β -> γ} {a : 滤子 α} {b : 滤子 β} {c : 滤子 γ}
  证明: by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a <= comap (g ∘ f) c := hfg
    _ <= comap f b := by simpa [comap_comap] using comap_mono hg

Depends on / 依赖: comap_comap, comap_mono, tendsto_iff_comap
-/
theorem Tendsto.of_tendsto_comp {f : α -> β} {g : β -> γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c <= b) : Tendsto f a b := by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a <= comap (g ∘ f) c := hfg
    _ <= comap f b := by simpa [comap_comap] using comap_mono hg

/--
theorem `comap_eq_of_inverse` / 定理 `comap_eq_of_inverse`

English:
theorem comap_eq_of_inverse
  statement: {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α) (eq : ψ ∘ φ = id)
  proof: by
  refine ((comap_mono <| map_le_iff_le_comap.1 hψ).trans ?_).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap]; rw [eq]; rw [comap_id]

中文:
定理 comap_eq_of_inverse
  结论: {f : 滤子 α} {g : 滤子 β} {φ : α -> β} (ψ : β -> α) (eq : ψ ∘ φ = id)
  证明: by
  refine ((comap_mono <| map_le_iff_le_comap.1 hψ).trans ?_).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap]; rw [eq]; rw [comap_id]

Depends on / 依赖: antisymm, comap_comap, comap_id, comap_mono, map_le_iff_le_comap
-/
theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α) (eq : ψ ∘ φ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f := by
  refine ((comap_mono <| map_le_iff_le_comap.1 hψ).trans ?_).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap]; rw [eq]; rw [comap_id]

/--
theorem `map_eq_of_inverse` / 定理 `map_eq_of_inverse`

English:
theorem map_eq_of_inverse
  statement: {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α) (eq : φ ∘ ψ = id)
  proof: by
  refine le_antisymm hφ (le_trans ?_ (map_mono hψ))
  rw [map_map]; rw [eq]; rw [map_id]

中文:
定理 map_eq_of_inverse
  结论: {f : 滤子 α} {g : 滤子 β} {φ : α -> β} (ψ : β -> α) (eq : φ ∘ ψ = id)
  证明: by
  refine le_antisymm hφ (le_trans ?_ (map_mono hψ))
  rw [map_map]; rw [eq]; rw [map_id]

Depends on / 依赖: le_antisymm, le_trans, map_id, map_map, map_mono
-/
theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α) (eq : φ ∘ ψ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g := by
  refine le_antisymm hφ (le_trans ?_ (map_mono hψ))
  rw [map_map]; rw [eq]; rw [map_id]

/--
theorem `tendsto_inf` / 定理 `tendsto_inf`

English:
theorem tendsto_inf
  given: {f : α -> β} {x : Filter α} {y₁ y₂ : Filter β}
  proof: by
  simp only [Tendsto, le_inf_iff]

中文:
定理 tendsto_inf
  条件: {f : α -> β} {x : 滤子 α} {y₁ y₂ : 滤子 β}
  证明: by
  simp only [Tendsto, le_inf_iff]

Depends on / 依赖: Tendsto, le_inf_iff
-/
theorem tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [Tendsto, le_inf_iff]

/--
theorem `tendsto_inf_left` / 定理 `tendsto_inf_left`

English:
theorem tendsto_inf_left
  given: {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y)
  proof: le_trans (map_mono inf_le_left) h

中文:
定理 tendsto_inf_left
  条件: {f : α -> β} {x₁ x₂ : 滤子 α} {y : 滤子 β} (h : 收敛 f x₁ y)
  证明: le_trans (map_mono inf_le_left) h

Depends on / 依赖: inf_le_left, le_trans, map_mono
-/
theorem tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h

/--
theorem `tendsto_inf_right` / 定理 `tendsto_inf_right`

English:
theorem tendsto_inf_right
  given: {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y)
  proof: le_trans (map_mono inf_le_right) h

中文:
定理 tendsto_inf_right
  条件: {f : α -> β} {x₁ x₂ : 滤子 α} {y : 滤子 β} (h : 收敛 f x₂ y)
  证明: le_trans (map_mono inf_le_right) h

Depends on / 依赖: inf_le_right, le_trans, map_mono
-/
theorem tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h

/--
theorem `Tendsto.inf` / 定理 `Tendsto.inf`

English:
theorem Tendsto.inf
  statement: {f : α -> β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
  proof: tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]

中文:
定理 收敛.下确界
  结论: {f : α -> β} {x₁ x₂ : 滤子 α} {y₁ y₂ : 滤子 β} (h₁ : 收敛 f x₁ y₁)
  证明: tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]

Depends on / 依赖: tendsto_inf, tendsto_inf_left, tendsto_inf_right
-/
theorem Tendsto.inf {f : α -> β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
    (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]
/--
theorem `tendsto_iInf` / 定理 `tendsto_iInf`

English:
theorem tendsto_iInf
  given: {f : α -> β} {x : Filter α} {y : ι -> Filter β}
  proof: by
  simp only [Tendsto, le_iInf_iff]

中文:
定理 tendsto_iInf
  条件: {f : α -> β} {x : 滤子 α} {y : ι -> 滤子 β}
  证明: by
  simp only [Tendsto, le_iInf_iff]

Depends on / 依赖: Tendsto, le_iInf_iff
-/
theorem tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> Filter β} :
    Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i) := by
  simp only [Tendsto, le_iInf_iff]

/--
theorem `tendsto_iInf'` / 定理 `tendsto_iInf'`

English:
theorem tendsto_iInf'
  statement: {f : α -> β} {x : ι -> Filter α} {y : Filter β} (i : ι)
  proof: hi.mono_left iInf_le _ _

中文:
定理 tendsto_iInf'
  结论: {f : α -> β} {x : ι -> 滤子 α} {y : 滤子 β} (i : ι)
  证明: hi.mono_left iInf_le _ _

Depends on / 依赖: hi.mono_left, iInf_le, mono_left
-/
theorem tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y : Filter β} (i : ι)
    (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y :=
hi.mono_left iInf_le _ _

/--
theorem `tendsto_iInf_iInf` / 定理 `tendsto_iInf_iInf`

English:
theorem tendsto_iInf_iInf
  statement: {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β}
  proof: tendsto_iInf.2 fun i => tendsto_iInf' i (h i)

@[simp]

中文:
定理 tendsto_iInf_iInf
  结论: {f : α -> β} {x : ι -> 滤子 α} {y : ι -> 滤子 β}
  证明: tendsto_iInf.2 fun i => tendsto_iInf' i (h i)

@[simp]

Depends on / 依赖: tendsto_iInf
-/
theorem tendsto_iInf_iInf {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β}
    (h : forall i, Tendsto f (x i) (y i)) : Tendsto f (iInf x) (iInf y) :=
  tendsto_iInf.2 fun i => tendsto_iInf' i (h i)

@[simp]
/--
theorem `tendsto_sup` / 定理 `tendsto_sup`

English:
theorem tendsto_sup
  given: {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β}
  proof: by
  simp only [Tendsto, map_sup, sup_le_iff]

中文:
定理 tendsto_sup
  条件: {f : α -> β} {x₁ x₂ : 滤子 α} {y : 滤子 β}
  证明: by
  simp only [Tendsto, map_sup, sup_le_iff]

Depends on / 依赖: Tendsto, map_sup, sup_le_iff
-/
theorem tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [Tendsto, map_sup, sup_le_iff]

/--
theorem `Tendsto.sup` / 定理 `Tendsto.sup`

English:
theorem Tendsto.sup
  given: {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β}
  proof: fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩

中文:
定理 收敛.上确界
  条件: {f : α -> β} {x₁ x₂ : 滤子 α} {y : 滤子 β}
  证明: fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩

Depends on / 依赖: tendsto_sup, tendsto_sup.mpr
-/
theorem Tendsto.sup {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y -> Tendsto f x₂ y -> Tendsto f (x₁ ⊔ x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩

/--
theorem `Tendsto.sup_sup` / 定理 `Tendsto.sup_sup`

English:
theorem Tendsto.sup_sup
  statement: {f : α -> β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β}
  proof: tendsto_sup.mpr ⟨h₁.mono_right le_sup_left, h₂.mono_right le_sup_right⟩

@[simp]

中文:
定理 收敛.sup_sup
  结论: {f : α -> β} {x₁ x₂ : 滤子 α} {y₁ y₂ : 滤子 β}
  证明: tendsto_sup.mpr ⟨h₁.mono_right le_sup_left, h₂.mono_right le_sup_right⟩

@[simp]

Depends on / 依赖: le_sup_left, le_sup_right, mono_right, tendsto_sup, tendsto_sup.mpr
-/
theorem Tendsto.sup_sup {f : α -> β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β}
    (h₁ : Tendsto f x₁ y₁) (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊔ x₂) (y₁ ⊔ y₂) :=
  tendsto_sup.mpr ⟨h₁.mono_right le_sup_left, h₂.mono_right le_sup_right⟩

@[simp]
/--
theorem `tendsto_iSup` / 定理 `tendsto_iSup`

English:
theorem tendsto_iSup
  given: {f : α -> β} {x : ι -> Filter α} {y : Filter β}
  proof: by simp only [Tendsto, map_iSup, iSup_le_iff]

中文:
定理 tendsto_iSup
  条件: {f : α -> β} {x : ι -> 滤子 α} {y : 滤子 β}
  证明: by simp only [Tendsto, map_iSup, iSup_le_iff]

Depends on / 依赖: Tendsto, iSup_le_iff, map_iSup
-/
theorem tendsto_iSup {f : α -> β} {x : ι -> Filter α} {y : Filter β} :
    Tendsto f (⨆ i, x i) y ↔ forall i, Tendsto f (x i) y := by simp only [Tendsto, map_iSup, iSup_le_iff]

/--
theorem `tendsto_iSup_iSup` / 定理 `tendsto_iSup_iSup`

English:
theorem tendsto_iSup_iSup
  statement: {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β}
  proof: tendsto_iSup.2 fun i => (h i).mono_right le_iSup _ _

中文:
定理 tendsto_iSup_iSup
  结论: {f : α -> β} {x : ι -> 滤子 α} {y : ι -> 滤子 β}
  证明: tendsto_iSup.2 fun i => (h i).mono_right le_iSup _ _

Depends on / 依赖: le_iSup, mono_right, tendsto_iSup
-/
theorem tendsto_iSup_iSup {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β}
    (h : forall i, Tendsto f (x i) (y i)) : Tendsto f (iSup x) (iSup y) :=
tendsto_iSup.2 fun i => (h i).mono_right le_iSup _ _

/--
theorem `tendsto_principal` / 定理 `tendsto_principal`

English:
theorem tendsto_principal
  given: {f : α -> β} {l : Filter α} {s : Set β}
  proof: by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]

中文:
定理 tendsto_principal
  条件: {f : α -> β} {l : 滤子 α} {s : 集合 β}
  证明: by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]
-/
@[simp] theorem tendsto_principal {f : α -> β} {l : Filter α} {s : Set β} :
    Tendsto f l (𝓟 s) ↔ forallᶠ a in l, f a in s := by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]

/--
theorem `tendsto_principal_principal` / 定理 `tendsto_principal_principal`

English:
theorem tendsto_principal_principal
  given: {f : α -> β} {s : Set α} {t : Set β}
  proof: by
  simp

中文:
定理 tendsto_principal_principal
  条件: {f : α -> β} {s : 集合 α} {t : 集合 β}
  证明: by
  simp
-/
theorem tendsto_principal_principal {f : α -> β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t := by
  simp

/--
theorem `tendsto_pure` / 定理 `tendsto_pure`

English:
theorem tendsto_pure
  given: {f : α -> β} {a : Filter α} {b : β}
  proof: by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]

中文:
定理 tendsto_pure
  条件: {f : α -> β} {a : 滤子 α} {b : β}
  证明: by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]
-/
@[simp] theorem tendsto_pure {f : α -> β} {a : Filter α} {b : β} :
    Tendsto f a (pure b) ↔ forallᶠ x in a, f x = b := by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]

/--
theorem `tendsto_pure_pure` / 定理 `tendsto_pure_pure`

English:
theorem tendsto_pure_pure
  given: (f : α -> β) (a : α)
  statement: Tendsto f (pure a) (pure (f a))
  proof: tendsto_pure.2 rfl

中文:
定理 tendsto_pure_pure
  条件: (f : α -> β) (a : α)
  结论: 收敛 f (pure a) (pure (f a))
  证明: tendsto_pure.2 rfl

Depends on / 依赖: tendsto_pure
-/
theorem tendsto_pure_pure (f : α -> β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl

/--
theorem `tendsto_const_pure` / 定理 `tendsto_const_pure`

English:
theorem tendsto_const_pure
  given: {a : Filter α} {b : β}
  statement: Tendsto (fun _ => b) a (pure b)
  proof: tendsto_pure.2 univ_mem' fun _ => rfl

中文:
定理 tendsto_const_pure
  条件: {a : 滤子 α} {b : β}
  结论: 收敛 (fun _ => b) a (pure b)
  证明: tendsto_pure.2 univ_mem' fun _ => rfl

Depends on / 依赖: tendsto_pure, univ_mem
-/
theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun _ => b) a (pure b) :=
tendsto_pure.2 univ_mem' fun _ => rfl

/--
theorem `pure_le_iff` / 定理 `pure_le_iff`

English:
theorem pure_le_iff
  given: {a : α} {l : Filter α}
  statement: pure a <= l ↔ forall s in l, a in s
  proof: Iff.rfl

中文:
定理 pure_le_iff
  条件: {a : α} {l : 滤子 α}
  结论: pure a <= l ↔ 对任意 s in l, a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem pure_le_iff {a : α} {l : Filter α} : pure a <= l ↔ forall s in l, a in s :=
  Iff.rfl

/--
theorem `tendsto_pure_left` / 定理 `tendsto_pure_left`

English:
theorem tendsto_pure_left
  given: {f : α -> β} {a : α} {l : Filter β}
  proof: Iff.rfl

@[simp]

中文:
定理 tendsto_pure_left
  条件: {f : α -> β} {a : α} {l : 滤子 β}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem tendsto_pure_left {f : α -> β} {a : α} {l : Filter β} :
    Tendsto f (pure a) l ↔ forall s in l, f a in s :=
  Iff.rfl

@[simp]
/--
theorem `map_inf_principal_preimage` / 定理 `map_inf_principal_preimage`

English:
theorem map_inf_principal_preimage
  given: {f : α -> β} {s : Set β} {l : Filter α}
  proof: Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_ofPred_eq, mem_preimage]

中文:
定理 map_inf_principal_preimage
  条件: {f : α -> β} {s : 集合 β} {l : 滤子 α}
  证明: Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_ofPred_eq, mem_preimage]

Depends on / 依赖: Filter, Filter.ext, mem_inf_principal, mem_map, mem_ofPred_eq, mem_preimage
-/
theorem map_inf_principal_preimage {f : α -> β} {s : Set β} {l : Filter α} :
    map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
  Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_ofPred_eq, mem_preimage]

/--
theorem `Tendsto.not_tendsto` / 定理 `Tendsto.not_tendsto`

English:
theorem Tendsto.not_tendsto
  statement: {f : α -> β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
  proof: fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot

中文:
定理 收敛.not_tendsto
  结论: {f : α -> β} {a : 滤子 α} {b₁ b₂ : 滤子 β} (hf : 收敛 f a b₁)
  证明: fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot
-/
theorem Tendsto.not_tendsto {f : α -> β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
    [NeBot a] (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot

/--
theorem `Tendsto.if` / 定理 `Tendsto.if`

English:
theorem Tendsto.if
  statement: {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β} {p : α -> Prop}
  proof: by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]

中文:
定理 收敛.if
  结论: {l₁ : 滤子 α} {l₂ : 滤子 β} {f g : α -> β} {p : α -> 命题}
  证明: by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]
-/
protected theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β} {p : α -> Prop}
    [forall x, Decidable (p x)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂)
    (h₁ : Tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂) :
    Tendsto (fun x => if p x then f x else g x) l₁ l₂ := by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]

/--
theorem `Tendsto.if'` / 定理 `Tendsto.if'`

English:
theorem Tendsto.if'
  statement: {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β}
  proof: (tendsto_inf_left hf).if (tendsto_inf_left hg)

中文:
定理 收敛.if'
  结论: {α β : 类型} {l₁ : 滤子 α} {l₂ : 滤子 β} {f g : α -> β}
  证明: (tendsto_inf_left hf).if (tendsto_inf_left hg)
-/
protected theorem Tendsto.if' {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β}
    {p : α -> Prop} [DecidablePred p] (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₁ l₂) :
    Tendsto (fun a => if p a then f a else g a) l₁ l₂ :=
  (tendsto_inf_left hf).if (tendsto_inf_left hg)

/--
theorem `Tendsto.piecewise` / 定理 `Tendsto.piecewise`

English:
theorem Tendsto.piecewise
  statement: {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β} {s : Set α}
  proof: Tendsto.if h₀ h₁

中文:
定理 收敛.piecewise
  结论: {l₁ : 滤子 α} {l₂ : 滤子 β} {f g : α -> β} {s : 集合 α}
  证明: Tendsto.if h₀ h₁
-/
protected theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α -> β} {s : Set α}
    [forall x, Decidable (x in s)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : Tendsto g (l₁ ⊓ 𝓟 sᶜ) l₂) :
    Tendsto (piecewise s f g) l₁ l₂ :=
  Tendsto.if h₀ h₁

end Filter

/--
theorem `Set.MapsTo.tendsto` / 定理 `Set.MapsTo.tendsto`

English:
theorem Set.MapsTo.tendsto
  given: {s : Set α} {t : Set β} {f : α -> β} (h : MapsTo f s t)
  proof: Filter.tendsto_principal_principal.2 h

中文:
定理 集合.映射到.tendsto
  条件: {s : 集合 α} {t : 集合 β} {f : α -> β} (h : 映射到 f s t)
  证明: Filter.tendsto_principal_principal.2 h

Depends on / 依赖: Filter, Filter.tendsto_principal_principal, tendsto_principal_principal
-/
theorem Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α -> β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h

/--
theorem `Filter.EventuallyEq.comp_tendsto` / 定理 `Filter.EventuallyEq.comp_tendsto`

English:
theorem Filter.EventuallyEq.comp_tendsto
  statement: {l : Filter α} {f : α -> β} {f' : α -> β}
  proof: hg.eventually H

中文:
定理 滤子.EventuallyEq.comp_tendsto
  结论: {l : 滤子 α} {f : α -> β} {f' : α -> β}
  证明: hg.eventually H

Depends on / 依赖: eventually, hg.eventually
-/
theorem Filter.EventuallyEq.comp_tendsto {l : Filter α} {f : α -> β} {f' : α -> β}
    (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter γ} (hg : Tendsto g lc l) :
    f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H

variable {F : Filter α} {G : Filter β}

/--
theorem `Filter.map_mapsTo_Iic_iff_tendsto` / 定理 `Filter.map_mapsTo_Iic_iff_tendsto`

English:
theorem Filter.map_mapsTo_Iic_iff_tendsto
  given: {m : α -> β}
  proof: ⟨fun hm => hm self_mem_Iic, fun hm _ => hm.mono_left⟩

alias ⟨_, Filter.Tendsto.map_mapsTo_Iic⟩ := Filter.map_mapsTo_Iic_iff_tendsto

中文:
定理 滤子.map_mapsTo_Iic_iff_tendsto
  条件: {m : α -> β}
  证明: ⟨fun hm => hm self_mem_Iic, fun hm _ => hm.mono_left⟩

alias ⟨_, Filter.Tendsto.map_mapsTo_Iic⟩ := Filter.map_mapsTo_Iic_iff_tendsto

Depends on / 依赖: algebraMap, c.mk, hm.mono_left, mono_left, self_mem_Iic
-/
theorem Filter.map_mapsTo_Iic_iff_tendsto {m : α -> β} :
    MapsTo (map m) (Iic F) (Iic G) ↔ Tendsto m F G :=
  ⟨fun hm => hm self_mem_Iic, fun hm _ => hm.mono_left⟩

alias ⟨_, Filter.Tendsto.map_mapsTo_Iic⟩ := Filter.map_mapsTo_Iic_iff_tendsto

/--
theorem `Filter.map_mapsTo_Iic_iff_mapsTo` / 定理 `Filter.map_mapsTo_Iic_iff_mapsTo`

English:
theorem Filter.map_mapsTo_Iic_iff_mapsTo
  given: {s : Set α} {t : Set β} {m : α -> β}
  proof: by
  rw [map_mapsTo_Iic_iff_tendsto]; rw [tendsto_principal_principal]; rw [MapsTo]

alias ⟨_, Set.MapsTo.filter_map_Iic⟩ := Filter.map_mapsTo_Iic_iff_mapsTo

中文:
定理 滤子.map_mapsTo_Iic_iff_mapsTo
  条件: {s : 集合 α} {t : 集合 β} {m : α -> β}
  证明: by
  rw [map_mapsTo_Iic_iff_tendsto]; rw [tendsto_principal_principal]; rw [MapsTo]

alias ⟨_, Set.MapsTo.filter_map_Iic⟩ := Filter.map_mapsTo_Iic_iff_mapsTo

Depends on / 依赖: MapsTo, map_mapsTo_Iic_iff_tendsto, tendsto_principal_principal
-/
theorem Filter.map_mapsTo_Iic_iff_mapsTo {s : Set α} {t : Set β} {m : α -> β} :
    MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ MapsTo m s t := by
  rw [map_mapsTo_Iic_iff_tendsto]; rw [tendsto_principal_principal]; rw [MapsTo]

alias ⟨_, Set.MapsTo.filter_map_Iic⟩ := Filter.map_mapsTo_Iic_iff_mapsTo
