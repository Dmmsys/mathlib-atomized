/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Tendsto

/-!
# Indicator function and filters

Properties of additive and multiplicative indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/

public section

variable {α β M E : Type*}

open Set Filter

section One

variable [One M] {s t : Set α} {f g : α -> M} {a : α} {l : Filter α}

@[to_additive]
/--
theorem `mulIndicator_eventuallyEq` / 定理 `mulIndicator_eventuallyEq`

English:
theorem mulIndicator_eventuallyEq
  given: (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t)
  proof: (eventually_inf_principal.1 hf).mp hs.mem_iff.mono fun x hst hfg =>
    by_cases
      (fun hxs : x in s => by simp only [*, hst.1 hxs, mulIndicator_of_mem])
      (fun hxs => by simp only [mulIndicator_of_notMem, hxs, mt hst.2 hxs, not_false_eq_true])

中文:
定理 mulIndicator_eventuallyEq
  条件: (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t)
  证明: (eventually_inf_principal.1 hf).mp hs.mem_iff.mono fun x hst hfg =>
    by_cases
      (fun hxs : x in s => by simp only [*, hst.1 hxs, mulIndicator_of_mem])
      (fun hxs => by simp only [mulIndicator_of_notMem, hxs, mt hst.2 hxs, not_false_eq_true])

Depends on / 依赖: eventually_inf_principal, hs.mem_iff.mono, mem_iff, mulIndicator_of_mem, mulIndicator_of_notMem, not_false_eq_true
-/
theorem mulIndicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) :
    mulIndicator s f =ᶠ[l] mulIndicator t g :=
(eventually_inf_principal.1 hf).mp hs.mem_iff.mono fun x hst hfg =>
    by_cases
      (fun hxs : x in s => by simp only [*, hst.1 hxs, mulIndicator_of_mem])
      (fun hxs => by simp only [mulIndicator_of_notMem, hxs, mt hst.2 hxs, not_false_eq_true])

end One

section Monoid

variable [Monoid M] {s t : Set α} {f g : α -> M} {a : α} {l : Filter α}

@[to_additive]
/--
theorem `mulIndicator_union_eventuallyEq` / 定理 `mulIndicator_union_eventuallyEq`

English:
theorem mulIndicator_union_eventuallyEq
  given: (h : forallᶠ a in l, a ∉ s inter t)
  proof: h.mono fun _a ha => mulIndicator_union_of_notMem_inter ha _

中文:
定理 mulIndicator_union_eventuallyEq
  条件: (h : 对任意ᶠ a in l, a ∉ s inter t)
  证明: h.mono fun _a ha => mulIndicator_union_of_notMem_inter ha _

Depends on / 依赖: h.mono, mulIndicator_union_of_notMem_inter
-/
theorem mulIndicator_union_eventuallyEq (h : forallᶠ a in l, a ∉ s inter t) :
    mulIndicator (s union t) f =ᶠ[l] mulIndicator s f * mulIndicator t f :=
  h.mono fun _a ha => mulIndicator_union_of_notMem_inter ha _

end Monoid

section Order

variable [One β] [Preorder β] {s t : Set α} {f g : α -> β} {a : α} {l : Filter α}

@[to_additive]
/--
theorem `mulIndicator_eventuallyLE_mulIndicator` / 定理 `mulIndicator_eventuallyLE_mulIndicator`

English:
theorem mulIndicator_eventuallyLE_mulIndicator
  given: (h : f <=ᶠ[l ⊓ 𝓟 s] g)
  proof: (eventually_inf_principal.1 h).mono fun _ => mulIndicator_rel_mulIndicator le_rfl

中文:
定理 mulIndicator_eventuallyLE_mulIndicator
  条件: (h : f <=ᶠ[l ⊓ 𝓟 s] g)
  证明: (eventually_inf_principal.1 h).mono fun _ => mulIndicator_rel_mulIndicator le_rfl

Depends on / 依赖: eventually_inf_principal, le_rfl, mulIndicator_rel_mulIndicator
-/
theorem mulIndicator_eventuallyLE_mulIndicator (h : f <=ᶠ[l ⊓ 𝓟 s] g) :
    mulIndicator s f <=ᶠ[l] mulIndicator s g :=
  (eventually_inf_principal.1 h).mono fun _ => mulIndicator_rel_mulIndicator le_rfl

end Order

@[to_additive]
/--
theorem `Monotone.mulIndicator_eventuallyEq_iUnion` / 定理 `Monotone.mulIndicator_eventuallyEq_iUnion`

English:
theorem Monotone.mulIndicator_eventuallyEq_iUnion
  statement: {ι} [Preorder ι] [One β] (s : ι -> Set α)
  proof: by
  classical exact hs.piecewise_eventually_eq_iUnion f 1 a

@[to_additive]

中文:
定理 Monotone.mulIndicator_eventuallyEq_iUnion
  结论: {ι} [Preorder ι] [One β] (s : ι -> Set α)
  证明: by
  classical exact hs.piecewise_eventually_eq_iUnion f 1 a

@[to_additive]

Depends on / 依赖: classical, hs.piecewise_eventually_eq_iUnion, piecewise_eventually_eq_iUnion
-/
theorem Monotone.mulIndicator_eventuallyEq_iUnion {ι} [Preorder ι] [One β] (s : ι -> Set α)
    (hs : Monotone s) (f : α -> β) (a : α) :
    (fun i => mulIndicator (s i) f a) =ᶠ[atTop] fun _ => mulIndicator (⋃ i, s i) f a := by
  classical exact hs.piecewise_eventually_eq_iUnion f 1 a

@[to_additive]
/--
theorem `Monotone.tendsto_mulIndicator` / 定理 `Monotone.tendsto_mulIndicator`

English:
theorem Monotone.tendsto_mulIndicator
  statement: {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Monotone s)
  proof: tendsto_pure.2 hs.mulIndicator_eventuallyEq_iUnion s f a

@[to_additive]

中文:
定理 Monotone.tendsto_mulIndicator
  结论: {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Monotone s)
  证明: tendsto_pure.2 hs.mulIndicator_eventuallyEq_iUnion s f a

@[to_additive]

Depends on / 依赖: hs.mulIndicator_eventuallyEq_iUnion, mulIndicator_eventuallyEq_iUnion, tendsto_pure
-/
theorem Monotone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Monotone s)
    (f : α -> β) (a : α) :
    Tendsto (fun i => mulIndicator (s i) f a) atTop (pure <| mulIndicator (⋃ i, s i) f a) :=
tendsto_pure.2 hs.mulIndicator_eventuallyEq_iUnion s f a

@[to_additive]
/--
theorem `Antitone.mulIndicator_eventuallyEq_iInter` / 定理 `Antitone.mulIndicator_eventuallyEq_iInter`

English:
theorem Antitone.mulIndicator_eventuallyEq_iInter
  statement: {ι} [Preorder ι] [One β] (s : ι -> Set α)
  proof: by
  classical exact hs.piecewise_eventually_eq_iInter f 1 a

@[to_additive]

中文:
定理 Antitone.mulIndicator_eventuallyEq_iInter
  结论: {ι} [Preorder ι] [One β] (s : ι -> Set α)
  证明: by
  classical exact hs.piecewise_eventually_eq_iInter f 1 a

@[to_additive]

Depends on / 依赖: classical, hs.piecewise_eventually_eq_iInter, piecewise_eventually_eq_iInter
-/
theorem Antitone.mulIndicator_eventuallyEq_iInter {ι} [Preorder ι] [One β] (s : ι -> Set α)
    (hs : Antitone s) (f : α -> β) (a : α) :
    (fun i => mulIndicator (s i) f a) =ᶠ[atTop] fun _ => mulIndicator (⋂ i, s i) f a := by
  classical exact hs.piecewise_eventually_eq_iInter f 1 a

@[to_additive]
/--
theorem `Antitone.tendsto_mulIndicator` / 定理 `Antitone.tendsto_mulIndicator`

English:
theorem Antitone.tendsto_mulIndicator
  statement: {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Antitone s)
  proof: tendsto_pure.2 hs.mulIndicator_eventuallyEq_iInter s f a

@[to_additive]

中文:
定理 Antitone.tendsto_mulIndicator
  结论: {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Antitone s)
  证明: tendsto_pure.2 hs.mulIndicator_eventuallyEq_iInter s f a

@[to_additive]

Depends on / 依赖: hs.mulIndicator_eventuallyEq_iInter, mulIndicator_eventuallyEq_iInter, tendsto_pure
-/
theorem Antitone.tendsto_mulIndicator {ι} [Preorder ι] [One β] (s : ι -> Set α) (hs : Antitone s)
    (f : α -> β) (a : α) :
    Tendsto (fun i => mulIndicator (s i) f a) atTop (pure <| mulIndicator (⋂ i, s i) f a) :=
tendsto_pure.2 hs.mulIndicator_eventuallyEq_iInter s f a

@[to_additive]
/--
theorem `mulIndicator_biUnion_finset_eventuallyEq` / 定理 `mulIndicator_biUnion_finset_eventuallyEq`

English:
theorem mulIndicator_biUnion_finset_eventuallyEq
  given: {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α)
  proof: by
  rw [iUnion_eq_iUnion_finset s]
  apply Monotone.mulIndicator_eventuallyEq_iUnion
  exact fun _ _ => biUnion_subset_biUnion_left

@[to_additive]

中文:
定理 mulIndicator_biUnion_finset_eventuallyEq
  条件: {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α)
  证明: by
  rw [iUnion_eq_iUnion_finset s]
  apply Monotone.mulIndicator_eventuallyEq_iUnion
  exact fun _ _ => biUnion_subset_biUnion_left

@[to_additive]

Depends on / 依赖: Monotone, Monotone.mulIndicator_eventuallyEq_iUnion, biUnion_subset_biUnion_left, iUnion_eq_iUnion_finset, mulIndicator_eventuallyEq_iUnion
-/
theorem mulIndicator_biUnion_finset_eventuallyEq {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α) :
    (fun n : Finset ι => mulIndicator (⋃ i in n, s i) f a) =ᶠ[atTop]
      fun _ => mulIndicator (iUnion s) f a := by
  rw [iUnion_eq_iUnion_finset s]
  apply Monotone.mulIndicator_eventuallyEq_iUnion
  exact fun _ _ => biUnion_subset_biUnion_left

@[to_additive]
/--
theorem `tendsto_mulIndicator_biUnion_finset` / 定理 `tendsto_mulIndicator_biUnion_finset`

English:
theorem tendsto_mulIndicator_biUnion_finset
  given: {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α)
  proof: tendsto_pure.2 mulIndicator_biUnion_finset_eventuallyEq s f a

@[to_additive]

中文:
定理 tendsto_mulIndicator_biUnion_finset
  条件: {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α)
  证明: tendsto_pure.2 mulIndicator_biUnion_finset_eventuallyEq s f a

@[to_additive]

Depends on / 依赖: mulIndicator_biUnion_finset_eventuallyEq, tendsto_pure
-/
theorem tendsto_mulIndicator_biUnion_finset {ι} [One β] (s : ι -> Set α) (f : α -> β) (a : α) :
    Tendsto (fun n : Finset ι => mulIndicator (⋃ i in n, s i) f a) atTop
      (pure <| mulIndicator (iUnion s) f a) :=
tendsto_pure.2 mulIndicator_biUnion_finset_eventuallyEq s f a

@[to_additive]
/--
theorem `Filter.EventuallyEq.mulSupport` / 定理 `Filter.EventuallyEq.mulSupport`

English:
theorem Filter.EventuallyEq.mulSupport
  statement: [One β] {f g : α -> β} {l : Filter α}
  proof: h.preimage ({1}ᶜ : Set β)

@[to_additive]

中文:
定理 Filter.EventuallyEq.mulSupport
  结论: [One β] {f g : α -> β} {l : Filter α}
  证明: h.preimage ({1}ᶜ : Set β)

@[to_additive]
-/
protected theorem Filter.EventuallyEq.mulSupport [One β] {f g : α -> β} {l : Filter α}
    (h : f =ᶠ[l] g) :
    Function.mulSupport f =ᶠ[l] Function.mulSupport g :=
  h.preimage ({1}ᶜ : Set β)

@[to_additive]
/--
theorem `Filter.EventuallyEq.mulIndicator` / 定理 `Filter.EventuallyEq.mulIndicator`

English:
theorem Filter.EventuallyEq.mulIndicator
  statement: [One β] {l : Filter α} {f g : α -> β} {s : Set α}
  proof: mulIndicator_eventuallyEq (hfg.filter_mono inf_le_left) EventuallyEq.rfl

@[to_additive]

中文:
定理 Filter.EventuallyEq.mulIndicator
  结论: [One β] {l : Filter α} {f g : α -> β} {s : Set α}
  证明: mulIndicator_eventuallyEq (hfg.filter_mono inf_le_left) EventuallyEq.rfl

@[to_additive]
-/
protected theorem Filter.EventuallyEq.mulIndicator [One β] {l : Filter α} {f g : α -> β} {s : Set α}
    (hfg : f =ᶠ[l] g) : s.mulIndicator f =ᶠ[l] s.mulIndicator g :=
  mulIndicator_eventuallyEq (hfg.filter_mono inf_le_left) EventuallyEq.rfl

@[to_additive]
/--
theorem `Filter.EventuallyEq.mulIndicator_one` / 定理 `Filter.EventuallyEq.mulIndicator_one`

English:
theorem Filter.EventuallyEq.mulIndicator_one
  statement: [One β] {l : Filter α} {f : α -> β} {s : Set α}
  proof: hf.mulIndicator.trans by rw [mulIndicator_one']

@[to_additive]

中文:
定理 Filter.EventuallyEq.mulIndicator_one
  结论: [One β] {l : Filter α} {f : α -> β} {s : Set α}
  证明: hf.mulIndicator.trans by rw [mulIndicator_one']

@[to_additive]

Depends on / 依赖: hf.mulIndicator.trans, mulIndicator, mulIndicator_one
-/
theorem Filter.EventuallyEq.mulIndicator_one [One β] {l : Filter α} {f : α -> β} {s : Set α}
    (hf : f =ᶠ[l] 1) : s.mulIndicator f =ᶠ[l] 1 :=
hf.mulIndicator.trans by rw [mulIndicator_one']

@[to_additive]
/--
theorem `Filter.EventuallyEq.of_mulIndicator` / 定理 `Filter.EventuallyEq.of_mulIndicator`

English:
theorem Filter.EventuallyEq.of_mulIndicator
  statement: [One β] {l : Filter α} {f : α -> β}
  proof: by
  have : forall {s : Set α}, Function.mulSupport (s.mulIndicator f) =ᶠ[l] s := fun {s} => by
    rw [mulSupport_mulIndicator]
    exact (hf.mono fun x hx => and_iff_left hx).set_eq
exact this.symm.trans h.mulSupport.trans this

@[to_additive]

中文:
定理 Filter.EventuallyEq.of_mulIndicator
  结论: [One β] {l : Filter α} {f : α -> β}
  证明: by
  have : forall {s : Set α}, Function.mulSupport (s.mulIndicator f) =ᶠ[l] s := fun {s} => by
    rw [mulSupport_mulIndicator]
    exact (hf.mono fun x hx => and_iff_left hx).set_eq
exact this.symm.trans h.mulSupport.trans this

@[to_additive]

Depends on / 依赖: Function, Function.mulSupport, and_iff_left, h.mulSupport.trans, hf.mono, mulIndicator, mulSupport, mulSupport_mulIndicator, s.mulIndicator, set_eq, this.symm.trans
-/
theorem Filter.EventuallyEq.of_mulIndicator [One β] {l : Filter α} {f : α -> β}
    (hf : forallᶠ x in l, f x != 1) {s t : Set α} (h : s.mulIndicator f =ᶠ[l] t.mulIndicator f) :
    s =ᶠ[l] t := by
  have : forall {s : Set α}, Function.mulSupport (s.mulIndicator f) =ᶠ[l] s := fun {s} => by
    rw [mulSupport_mulIndicator]
    exact (hf.mono fun x hx => and_iff_left hx).set_eq
exact this.symm.trans h.mulSupport.trans this

@[to_additive]
/--
theorem `Filter.EventuallyEq.of_mulIndicator_const` / 定理 `Filter.EventuallyEq.of_mulIndicator_const`

English:
theorem Filter.EventuallyEq.of_mulIndicator_const
  statement: [One β] {l : Filter α} {c : β} (hc : c != 1)
  proof: .of_mulIndicator (Eventually.of_forall fun _ => hc) h

@[to_additive]

中文:
定理 Filter.EventuallyEq.of_mulIndicator_const
  结论: [One β] {l : Filter α} {c : β} (hc : c != 1)
  证明: .of_mulIndicator (Eventually.of_forall fun _ => hc) h

@[to_additive]

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall, of_mulIndicator
-/
theorem Filter.EventuallyEq.of_mulIndicator_const [One β] {l : Filter α} {c : β} (hc : c != 1)
    {s t : Set α} (h : s.mulIndicator (fun _ => c) =ᶠ[l] t.mulIndicator fun _ => c) : s =ᶠ[l] t :=
  .of_mulIndicator (Eventually.of_forall fun _ => hc) h

@[to_additive]
/--
theorem `Filter.mulIndicator_const_eventuallyEq` / 定理 `Filter.mulIndicator_const_eventuallyEq`

English:
theorem Filter.mulIndicator_const_eventuallyEq
  statement: [One β] {l : Filter α} {c : β} (hc : c != 1)
  proof: ⟨.of_mulIndicator_const hc, mulIndicator_eventuallyEq .rfl⟩

中文:
定理 Filter.mulIndicator_const_eventuallyEq
  结论: [One β] {l : Filter α} {c : β} (hc : c != 1)
  证明: ⟨.of_mulIndicator_const hc, mulIndicator_eventuallyEq .rfl⟩

Depends on / 依赖: mulIndicator_eventuallyEq, of_mulIndicator_const
-/
theorem Filter.mulIndicator_const_eventuallyEq [One β] {l : Filter α} {c : β} (hc : c != 1)
    {s t : Set α} : s.mulIndicator (fun _ => c) =ᶠ[l] t.mulIndicator (fun _ => c) ↔ s =ᶠ[l] t :=
  ⟨.of_mulIndicator_const hc, mulIndicator_eventuallyEq .rfl⟩
