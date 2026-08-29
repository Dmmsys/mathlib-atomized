/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Floris van Doorn
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Subsingleton
/-!
# Functions that are eventually constant along a filter

In this file we define a predicate `Filter.EventuallyConst f l` saying that a function `f : α → β`
is eventually equal to a constant along a filter `l`. We also prove some basic properties of these
functions.

## Implementation notes

A naive definition of `Filter.EventuallyConst f l` is `∃ y, ∀ᶠ x in l, f x = y`.
However, this proposition is false for empty `α`, `β`.
Instead, we say that `Filter.map f l` is supported on a subsingleton.
This allows us to drop `[Nonempty _]` assumptions here and there.
-/

@[expose] public section

open Set

variable {α β γ δ : Type*} {l : Filter α} {f : α -> β}

namespace Filter

/--
Definition of `EventuallyConst` / `EventuallyConst` 的定义

English:
definition EventuallyConst
  signature: (f : α -> β) (l : Filter α)
  body: (map f l).Subsingleton

中文:
定义 EventuallyConst
  签名: (f : α -> β) (l : 滤子 α)
  定义体: (map f l).Subsingleton

Depends on / 依赖: Subsingleton
-/
def EventuallyConst (f : α -> β) (l : Filter α) : Prop := (map f l).Subsingleton

/--
theorem `HasBasis.eventuallyConst_iff` / 定理 `HasBasis.eventuallyConst_iff`

English:
theorem HasBasis.eventuallyConst_iff
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α}
  proof: (h.map f).subsingleton_iff.trans by simp only [Set.Subsingleton, forall_mem_image]

中文:
定理 有基.eventuallyConst_iff
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 α}
  证明: (h.map f).subsingleton_iff.trans by simp only [Set.Subsingleton, forall_mem_image]

Depends on / 依赖: Set.Subsingleton, Subsingleton, forall_mem_image, h.map, subsingleton_iff, subsingleton_iff.trans
-/
theorem HasBasis.eventuallyConst_iff {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α}
    (h : l.HasBasis p s) : EventuallyConst f l ↔ exists i, p i ∧ forall x in s i, forall y in s i, f x = f y :=
(h.map f).subsingleton_iff.trans by simp only [Set.Subsingleton, forall_mem_image]

/--
theorem `HasBasis.eventuallyConst_iff'` / 定理 `HasBasis.eventuallyConst_iff'`

English:
theorem HasBasis.eventuallyConst_iff'
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α}
  proof: h.eventuallyConst_iff.trans exists_congr fun i => and_congr_right fun hi =>
    ⟨fun h => (h · · (x i) (hx i hi)), fun h a ha b hb => h a ha ▸ (h b hb).symm⟩

中文:
定理 有基.eventuallyConst_iff'
  结论: {ι : 类型层*} {p : ι -> 命题} {s : ι -> 集合 α}
  证明: h.eventuallyConst_iff.trans exists_congr fun i => and_congr_right fun hi =>
    ⟨fun h => (h · · (x i) (hx i hi)), fun h a ha b hb => h a ha ▸ (h b hb).symm⟩

Depends on / 依赖: and_congr_right, eventuallyConst_iff, exists_congr, h.eventuallyConst_iff.trans
-/
theorem HasBasis.eventuallyConst_iff' {ι : Sort*} {p : ι -> Prop} {s : ι -> Set α}
    {x : ι -> α} (h : l.HasBasis p s) (hx : forall i, p i -> x i in s i) :
    EventuallyConst f l ↔ exists i, p i ∧ forall y in s i, f y = f (x i) :=
h.eventuallyConst_iff.trans exists_congr fun i => and_congr_right fun hi =>
    ⟨fun h => (h · · (x i) (hx i hi)), fun h a ha b hb => h a ha ▸ (h b hb).symm⟩

/--
lemma `eventuallyConst_iff_tendsto` / 引理 `eventuallyConst_iff_tendsto`

English:
lemma eventuallyConst_iff_tendsto
  given: [Nonempty β]
  proof: subsingleton_iff_exists_le_pure

alias ⟨EventuallyConst.exists_tendsto, _⟩ := eventuallyConst_iff_tendsto

中文:
引理 eventuallyConst_iff_tendsto
  条件: [非空 β]
  证明: subsingleton_iff_exists_le_pure

alias ⟨EventuallyConst.exists_tendsto, _⟩ := eventuallyConst_iff_tendsto

Depends on / 依赖: subsingleton_iff_exists_le_pure
-/
lemma eventuallyConst_iff_tendsto [Nonempty β] :
    EventuallyConst f l ↔ exists x, Tendsto f l (pure x) :=
  subsingleton_iff_exists_le_pure

alias ⟨EventuallyConst.exists_tendsto, _⟩ := eventuallyConst_iff_tendsto

/--
theorem `EventuallyConst.of_tendsto` / 定理 `EventuallyConst.of_tendsto`

English:
theorem EventuallyConst.of_tendsto
  given: {x : β} (h : Tendsto f l (pure x))
  statement: EventuallyConst f l
  proof: have : Nonempty β := ⟨x⟩; eventuallyConst_iff_tendsto.2 ⟨x, h⟩

中文:
定理 EventuallyConst.of_tendsto
  条件: {x : β} (h : 收敛 f l (pure x))
  结论: EventuallyConst f l
  证明: have : Nonempty β := ⟨x⟩; eventuallyConst_iff_tendsto.2 ⟨x, h⟩

Depends on / 依赖: Nonempty, eventuallyConst_iff_tendsto
-/
theorem EventuallyConst.of_tendsto {x : β} (h : Tendsto f l (pure x)) : EventuallyConst f l :=
  have : Nonempty β := ⟨x⟩; eventuallyConst_iff_tendsto.2 ⟨x, h⟩

/--
theorem `eventuallyConst_iff_exists_eventuallyEq` / 定理 `eventuallyConst_iff_exists_eventuallyEq`

English:
theorem eventuallyConst_iff_exists_eventuallyEq
  given: [Nonempty β]
  proof: subsingleton_iff_exists_singleton_mem

alias ⟨EventuallyConst.eventuallyEq_const, _⟩ := eventuallyConst_iff_exists_eventuallyEq

中文:
定理 eventuallyConst_iff_存在_eventuallyEq
  条件: [非空 β]
  证明: subsingleton_iff_exists_singleton_mem

alias ⟨EventuallyConst.eventuallyEq_const, _⟩ := eventuallyConst_iff_exists_eventuallyEq

Depends on / 依赖: subsingleton_iff_exists_singleton_mem
-/
theorem eventuallyConst_iff_exists_eventuallyEq [Nonempty β] :
    EventuallyConst f l ↔ exists c, f =ᶠ[l] fun _ => c :=
  subsingleton_iff_exists_singleton_mem

alias ⟨EventuallyConst.eventuallyEq_const, _⟩ := eventuallyConst_iff_exists_eventuallyEq

/--
theorem `eventuallyConst_pred'` / 定理 `eventuallyConst_pred'`

English:
theorem eventuallyConst_pred'
  given: {p : α -> Prop}
  proof: by
  simp only [eventuallyConst_iff_exists_eventuallyEq, Prop.exists_iff]

中文:
定理 eventuallyConst_pred'
  条件: {p : α -> 命题}
  证明: by
  simp only [eventuallyConst_iff_exists_eventuallyEq, Prop.exists_iff]

Depends on / 依赖: Prop.exists_iff, eventuallyConst_iff_exists_eventuallyEq, exists_iff
-/
theorem eventuallyConst_pred' {p : α -> Prop} :
    EventuallyConst p l ↔ (p =ᶠ[l] fun _ => False) ∨ (p =ᶠ[l] fun _ => True) := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, Prop.exists_iff]

/--
theorem `eventuallyConst_pred` / 定理 `eventuallyConst_pred`

English:
theorem eventuallyConst_pred
  given: {p : α -> Prop}
  proof: by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]

中文:
定理 eventuallyConst_pred
  条件: {p : α -> 命题}
  证明: by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]

Depends on / 依赖: EventuallyEq, eventuallyConst_pred, or_comm
-/
theorem eventuallyConst_pred {p : α -> Prop} :
    EventuallyConst p l ↔ (forallᶠ x in l, p x) ∨ (forallᶠ x in l, ¬p x) := by
  simp [eventuallyConst_pred', or_comm, EventuallyEq]

/--
theorem `eventuallyConst_set'` / 定理 `eventuallyConst_set'`

English:
theorem eventuallyConst_set'
  given: {s : Set α}
  proof: eventuallyConst_pred'

中文:
定理 eventuallyConst_set'
  条件: {s : 集合 α}
  证明: eventuallyConst_pred'

Depends on / 依赖: eventuallyConst_pred
-/
theorem eventuallyConst_set' {s : Set α} :
    EventuallyConst s l ↔ (s =ᶠ[l] (∅ : Set α)) ∨ s =ᶠ[l] univ :=
  eventuallyConst_pred'

/--
theorem `eventuallyConst_set` / 定理 `eventuallyConst_set`

English:
theorem eventuallyConst_set
  given: {s : Set α}
  proof: eventuallyConst_pred

中文:
定理 eventuallyConst_set
  条件: {s : 集合 α}
  证明: eventuallyConst_pred

Depends on / 依赖: IsHausdorff, Subsingleton, eventuallyConst_pred, of_subsingleton
-/
theorem eventuallyConst_set {s : Set α} :
    EventuallyConst s l ↔ (forallᶠ x in l, x in s) ∨ (forallᶠ x in l, x ∉ s) :=
  eventuallyConst_pred

/--
theorem `eventuallyConst_preimage` / 定理 `eventuallyConst_preimage`

English:
theorem eventuallyConst_preimage
  given: {s : Set β} {f : α -> β}
  proof: .rfl

中文:
定理 eventuallyConst_preimage
  条件: {s : 集合 β} {f : α -> β}
  证明: .rfl
-/
theorem eventuallyConst_preimage {s : Set β} {f : α -> β} :
    EventuallyConst (f ⁻¹' s) l ↔ EventuallyConst s (map f l) :=
  .rfl

/--
theorem `EventuallyEq.eventuallyConst_iff` / 定理 `EventuallyEq.eventuallyConst_iff`

English:
theorem EventuallyEq.eventuallyConst_iff
  given: {g : α -> β} (h : f =ᶠ[l] g)
  proof: by
  simp only [EventuallyConst, map_congr h]

中文:
定理 EventuallyEq.eventuallyConst_iff
  条件: {g : α -> β} (h : f =ᶠ[l] g)
  证明: by
  simp only [EventuallyConst, map_congr h]

Depends on / 依赖: EventuallyConst, map_congr
-/
theorem EventuallyEq.eventuallyConst_iff {g : α -> β} (h : f =ᶠ[l] g) :
    EventuallyConst f l ↔ EventuallyConst g l := by
  simp only [EventuallyConst, map_congr h]

/--
theorem `eventuallyConst_id` / 定理 `eventuallyConst_id`

English:
theorem eventuallyConst_id
  statement: EventuallyConst id l ↔ l.Subsingleton
  proof: Iff.rfl

中文:
定理 eventuallyConst_id
  结论: EventuallyConst id l ↔ l.子单例
  证明: Iff.rfl
-/
@[simp] theorem eventuallyConst_id : EventuallyConst id l ↔ l.Subsingleton := Iff.rfl

namespace EventuallyConst

/--
lemma `bot` / 引理 `bot`

English:
lemma bot
  statement: EventuallyConst f ⊥
  proof: subsingleton_bot

@[simp]

中文:
引理 bot
  结论: EventuallyConst f ⊥
  证明: subsingleton_bot

@[simp]
-/
@[simp] protected lemma bot : EventuallyConst f ⊥ := subsingleton_bot

@[simp]
/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (c : β)
  statement: EventuallyConst (fun _ => c) l
  proof: .of_tendsto tendsto_const_pure

中文:
引理 const
  条件: (c : β)
  结论: EventuallyConst (fun _ => c) l
  证明: .of_tendsto tendsto_const_pure
-/
protected lemma const (c : β) : EventuallyConst (fun _ => c) l :=
  .of_tendsto tendsto_const_pure

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {g} (h : EventuallyConst f l) (hg : f =ᶠ[l] g)
  statement: EventuallyConst g l
  proof: hg.eventuallyConst_iff.1 h

@[nontriviality]

中文:
引理 congr
  条件: {g} (h : EventuallyConst f l) (hg : f =ᶠ[l] g)
  结论: EventuallyConst g l
  证明: hg.eventuallyConst_iff.1 h

@[nontriviality]
-/
protected lemma congr {g} (h : EventuallyConst f l) (hg : f =ᶠ[l] g) : EventuallyConst g l :=
  hg.eventuallyConst_iff.1 h

@[nontriviality]
/--
lemma `of_subsingleton_right` / 引理 `of_subsingleton_right`

English:
lemma of_subsingleton_right
  given: [Subsingleton β]
  statement: EventuallyConst f l
  proof: .of_subsingleton

nonrec lemma anti {l'} (h : EventuallyConst f l) (hl' : l' <= l) : EventuallyConst f l' :=
  h.anti (map_mono hl')

@[nontriviality]

中文:
引理 of_subsingleton_right
  条件: [子单例 β]
  结论: EventuallyConst f l
  证明: .of_subsingleton

nonrec lemma anti {l'} (h : EventuallyConst f l) (hl' : l' <= l) : EventuallyConst f l' :=
  h.anti (map_mono hl')

@[nontriviality]

Depends on / 依赖: of_subsingleton
-/
lemma of_subsingleton_right [Subsingleton β] : EventuallyConst f l := .of_subsingleton

nonrec lemma anti {l'} (h : EventuallyConst f l) (hl' : l' <= l) : EventuallyConst f l' :=
  h.anti (map_mono hl')

@[nontriviality]
/--
lemma `of_subsingleton_left` / 引理 `of_subsingleton_left`

English:
lemma of_subsingleton_left
  given: [Subsingleton α]
  statement: EventuallyConst f l
  proof: .map .of_subsingleton f

中文:
引理 of_subsingleton_left
  条件: [子单例 α]
  结论: EventuallyConst f l
  证明: .map .of_subsingleton f

Depends on / 依赖: of_subsingleton
-/
lemma of_subsingleton_left [Subsingleton α] : EventuallyConst f l :=
  .map .of_subsingleton f

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: (h : EventuallyConst f l) (g : β -> γ)
  statement: EventuallyConst (g ∘ f) l
  proof: h.map g

@[to_additive]

中文:
引理 comp
  条件: (h : EventuallyConst f l) (g : β -> γ)
  结论: EventuallyConst (g ∘ f) l
  证明: h.map g

@[to_additive]

Depends on / 依赖: h.map
-/
lemma comp (h : EventuallyConst f l) (g : β -> γ) : EventuallyConst (g ∘ f) l := h.map g

@[to_additive]
/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: [Inv β] (h : EventuallyConst f l)
  statement: EventuallyConst (f⁻¹) l
  proof: h.comp Inv.inv

中文:
引理 inv
  条件: [取逆 β] (h : EventuallyConst f l)
  结论: EventuallyConst (f⁻¹) l
  证明: h.comp Inv.inv
-/
protected lemma inv [Inv β] (h : EventuallyConst f l) : EventuallyConst (f⁻¹) l := h.comp Inv.inv

/--
lemma `comp_tendsto` / 引理 `comp_tendsto`

English:
lemma comp_tendsto
  statement: {lb : Filter β} {g : β -> γ} (hg : EventuallyConst g lb)
  proof: hg.anti hf

中文:
引理 comp_tendsto
  结论: {lb : 滤子 β} {g : β -> γ} (hg : EventuallyConst g lb)
  证明: hg.anti hf

Depends on / 依赖: IsPrecomplete, Subsingleton, hg.anti, of_subsingleton
-/
lemma comp_tendsto {lb : Filter β} {g : β -> γ} (hg : EventuallyConst g lb)
    (hf : Tendsto f l lb) : EventuallyConst (g ∘ f) l :=
  hg.anti hf

/--
lemma `apply` / 引理 `apply`

English:
lemma apply
  statement: {ι : Type*} {p : ι -> Type*} {g : α -> forall x, p x}
  proof: h.comp Function.eval i

中文:
引理 apply
  结论: {ι : 类型} {p : ι -> 类型} {g : α -> 对任意 x, p x}
  证明: h.comp Function.eval i

Depends on / 依赖: Function, Function.eval, h.comp
-/
lemma apply {ι : Type*} {p : ι -> Type*} {g : α -> forall x, p x}
    (h : EventuallyConst g l) (i : ι) : EventuallyConst (g · i) l :=
h.comp Function.eval i

/--
lemma `comp₂` / 引理 `comp₂`

English:
lemma comp₂
  given: {g : α -> γ} (hf : EventuallyConst f l) (op : β -> γ -> δ) (hg : EventuallyConst g l)
  proof: ((hf.prod hg).map op.uncurry).anti
    (tendsto_map (f := op.uncurry)).comp (tendsto_map.prodMk tendsto_map)

中文:
引理 comp₂
  条件: {g : α -> γ} (hf : EventuallyConst f l) (op : β -> γ -> δ) (hg : EventuallyConst g l)
  证明: ((hf.prod hg).map op.uncurry).anti
    (tendsto_map (f := op.uncurry)).comp (tendsto_map.prodMk tendsto_map)

Depends on / 依赖: hf.prod, op.uncurry, prodMk, tendsto_map, tendsto_map.prodMk, uncurry
-/
lemma comp₂ {g : α -> γ} (hf : EventuallyConst f l) (op : β -> γ -> δ) (hg : EventuallyConst g l) :
    EventuallyConst (fun x => op (f x) (g x)) l :=
((hf.prod hg).map op.uncurry).anti
    (tendsto_map (f := op.uncurry)).comp (tendsto_map.prodMk tendsto_map)

/--
lemma `prodMk` / 引理 `prodMk`

English:
lemma prodMk
  given: {g : α -> γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l)
  proof: hf.comp₂ Prod.mk hg

@[to_additive]

中文:
引理 prodMk
  条件: {g : α -> γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l)
  证明: hf.comp₂ Prod.mk hg

@[to_additive]

Depends on / 依赖: Prod.mk, hf.comp
-/
lemma prodMk {g : α -> γ} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (fun x => (f x, g x)) l :=
  hf.comp₂ Prod.mk hg

@[to_additive]
/--
lemma `mul` / 引理 `mul`

English:
lemma mul
  given: [Mul β] {g : α -> β} (hf : EventuallyConst f l) (hg : EventuallyConst g l)
  proof: hf.comp₂ (· * ·) hg

中文:
引理 mul
  条件: [乘法 β] {g : α -> β} (hf : EventuallyConst f l) (hg : EventuallyConst g l)
  证明: hf.comp₂ (· * ·) hg

Depends on / 依赖: hf.comp
-/
lemma mul [Mul β] {g : α -> β} (hf : EventuallyConst f l) (hg : EventuallyConst g l) :
    EventuallyConst (f * g) l :=
  hf.comp₂ (· * ·) hg

variable [One β] {s : Set α} {c : β}

@[to_additive]
/--
lemma `of_mulIndicator_const` / 引理 `of_mulIndicator_const`

English:
lemma of_mulIndicator_const
  given: (h : EventuallyConst (s.mulIndicator fun _ => c) l) (hc : c != 1)
  proof: by
  simpa [Function.comp_def, hc, imp_false] using! h.comp (· = c)

@[to_additive]

中文:
引理 of_mulIndicator_const
  条件: (h : EventuallyConst (s.mulIndicator fun _ => c) l) (hc : c != 1)
  证明: by
  simpa [Function.comp_def, hc, imp_false] using! h.comp (· = c)

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, h.comp, imp_false
-/
lemma of_mulIndicator_const (h : EventuallyConst (s.mulIndicator fun _ => c) l) (hc : c != 1) :
    EventuallyConst s l := by
  simpa [Function.comp_def, hc, imp_false] using! h.comp (· = c)

@[to_additive]
/--
theorem `mulIndicator_const` / 定理 `mulIndicator_const`

English:
theorem mulIndicator_const
  given: (h : EventuallyConst s l) (c : β)
  proof: by
  classical exact h.comp (if · then c else 1)

@[to_additive]

中文:
定理 mulIndicator_const
  条件: (h : EventuallyConst s l) (c : β)
  证明: by
  classical exact h.comp (if · then c else 1)

@[to_additive]

Depends on / 依赖: classical, h.comp
-/
theorem mulIndicator_const (h : EventuallyConst s l) (c : β) :
    EventuallyConst (s.mulIndicator fun _ => c) l := by
  classical exact h.comp (if · then c else 1)

@[to_additive]
/--
theorem `mulIndicator_const_iff_of_ne` / 定理 `mulIndicator_const_iff_of_ne`

English:
theorem mulIndicator_const_iff_of_ne
  given: (hc : c != 1)
  proof: ⟨(of_mulIndicator_const · hc), (mulIndicator_const · c)⟩

@[to_additive (attr := simp)]

中文:
定理 mulIndicator_const_iff_of_ne
  条件: (hc : c != 1)
  证明: ⟨(of_mulIndicator_const · hc), (mulIndicator_const · c)⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator_const, of_mulIndicator_const
-/
theorem mulIndicator_const_iff_of_ne (hc : c != 1) :
    EventuallyConst (s.mulIndicator fun _ => c) l ↔ EventuallyConst s l :=
  ⟨(of_mulIndicator_const · hc), (mulIndicator_const · c)⟩

@[to_additive (attr := simp)]
/--
theorem `mulIndicator_const_iff` / 定理 `mulIndicator_const_iff`

English:
theorem mulIndicator_const_iff
  proof: by
  rcases eq_or_ne c 1 with rfl | hc <;> simp [mulIndicator_const_iff_of_ne, *]

中文:
定理 mulIndicator_const_iff
  证明: by
  rcases eq_or_ne c 1 with rfl | hc <;> simp [mulIndicator_const_iff_of_ne, *]

Depends on / 依赖: eq_or_ne, mulIndicator_const_iff_of_ne
-/
theorem mulIndicator_const_iff :
    EventuallyConst (s.mulIndicator fun _ => c) l ↔ c = 1 ∨ EventuallyConst s l := by
  rcases eq_or_ne c 1 with rfl | hc <;> simp [mulIndicator_const_iff_of_ne, *]

end EventuallyConst

/--
lemma `eventuallyConst_atTop` / 引理 `eventuallyConst_atTop`

English:
lemma eventuallyConst_atTop
  given: [SemilatticeSup α] [Nonempty α]
  proof: (atTop_basis.eventuallyConst_iff' fun _ _ => self_mem_Ici).trans by
    simp only [true_and, mem_Ici]

中文:
引理 eventuallyConst_atTop
  条件: [SemilatticeSup α] [非空 α]
  证明: (atTop_basis.eventuallyConst_iff' fun _ _ => self_mem_Ici).trans by
    simp only [true_and, mem_Ici]

Depends on / 依赖: atTop_basis, atTop_basis.eventuallyConst_iff, eventuallyConst_iff, mem_Ici, self_mem_Ici, true_and
-/
lemma eventuallyConst_atTop [SemilatticeSup α] [Nonempty α] :
    EventuallyConst f atTop ↔ (exists i, forall j, i <= j -> f j = f i) :=
(atTop_basis.eventuallyConst_iff' fun _ _ => self_mem_Ici).trans by
    simp only [true_and, mem_Ici]

/--
lemma `eventuallyConst_atTop_nat` / 引理 `eventuallyConst_atTop_nat`

English:
lemma eventuallyConst_atTop_nat
  given: {f : Nat -> α}
  proof: by
  rw [eventuallyConst_atTop]
  refine exists_congr fun n => ⟨fun h m hm => ?_, fun h m hm => ?_⟩
  · exact (h (m + 1) (hm.trans m.le_succ)).trans (h m hm).symm
  · induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ihm => exact (h m hm).trans ihm

中文:
引理 eventuallyConst_atTop_nat
  条件: {f : 自然数 -> α}
  证明: by
  rw [eventuallyConst_atTop]
  refine exists_congr fun n => ⟨fun h m hm => ?_, fun h m hm => ?_⟩
  · exact (h (m + 1) (hm.trans m.le_succ)).trans (h m hm).symm
  · induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ihm => exact (h m hm).trans ihm

Depends on / 依赖: Nat.le_induction, eventuallyConst_atTop, exists_congr, hm.trans, le_induction, le_succ, m.le_succ
-/
lemma eventuallyConst_atTop_nat {f : Nat -> α} :
    EventuallyConst f atTop ↔ exists n, forall m, n <= m -> f (m + 1) = f m := by
  rw [eventuallyConst_atTop]
  refine exists_congr fun n => ⟨fun h m hm => ?_, fun h m hm => ?_⟩
  · exact (h (m + 1) (hm.trans m.le_succ)).trans (h m hm).symm
  · induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ihm => exact (h m hm).trans ihm

end Filter
