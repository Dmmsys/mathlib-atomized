/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Support of a function in an order

This file relates the support of a function to order constructions.
-/

public section

assert_not_exists MonoidWithZero

open Set

variable {ι : Sort*} {α M : Type*}

namespace Function
variable [One M]

@[to_additive]
/--
lemma `mulSupport_sup` / 引理 `mulSupport_sup`

English:
lemma mulSupport_sup
  given: [SemilatticeSup M] (f g : α -> M)
  proof: mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g

@[to_additive]

中文:
引理 mulSupport_sup
  条件: [SemilatticeSup M] (f g : α -> M)
  证明: mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g

@[to_additive]

Depends on / 依赖: mulSupport_binop_subset, sup_idem
-/
lemma mulSupport_sup [SemilatticeSup M] (f g : α -> M) :
    mulSupport (fun x => f x ⊔ g x) subseteq mulSupport f union mulSupport g :=
  mulSupport_binop_subset (· ⊔ ·) (sup_idem _) f g

@[to_additive]
/--
lemma `mulSupport_inf` / 引理 `mulSupport_inf`

English:
lemma mulSupport_inf
  given: [SemilatticeInf M] (f g : α -> M)
  proof: mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[to_additive]

中文:
引理 mulSupport_inf
  条件: [SemilatticeInf M] (f g : α -> M)
  证明: mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[to_additive]

Depends on / 依赖: inf_idem, mulSupport_binop_subset
-/
lemma mulSupport_inf [SemilatticeInf M] (f g : α -> M) :
    mulSupport (fun x => f x ⊓ g x) subseteq mulSupport f union mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[to_additive]
/--
lemma `mulSupport_max` / 引理 `mulSupport_max`

English:
lemma mulSupport_max
  given: [LinearOrder M] (f g : α -> M)
  proof: mulSupport_sup f g

@[to_additive]

中文:
引理 mulSupport_max
  条件: [线性序 M] (f g : α -> M)
  证明: mulSupport_sup f g

@[to_additive]

Depends on / 依赖: mulSupport_sup
-/
lemma mulSupport_max [LinearOrder M] (f g : α -> M) :
    mulSupport (fun x => max (f x) (g x)) subseteq mulSupport f union mulSupport g := mulSupport_sup f g

@[to_additive]
/--
lemma `mulSupport_min` / 引理 `mulSupport_min`

English:
lemma mulSupport_min
  given: [LinearOrder M] (f g : α -> M)
  proof: mulSupport_inf f g

@[to_additive]

中文:
引理 mulSupport_min
  条件: [线性序 M] (f g : α -> M)
  证明: mulSupport_inf f g

@[to_additive]

Depends on / 依赖: mulSupport_inf
-/
lemma mulSupport_min [LinearOrder M] (f g : α -> M) :
    mulSupport (fun x => min (f x) (g x)) subseteq mulSupport f union mulSupport g := mulSupport_inf f g

@[to_additive]
/--
lemma `mulSupport_iSup` / 引理 `mulSupport_iSup`

English:
lemma mulSupport_iSup
  given: [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α -> M)
  proof: by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]

中文:
引理 mulSupport_iSup
  条件: [条件完备格 M] [非空 ι] (f : ι -> α -> M)
  证明: by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]

Depends on / 依赖: ciSup_const, mem_iUnion, mulSupport_subset_iff, notMem_mulSupport, not_exists
-/
lemma mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α -> M) :
    mulSupport (fun x => ⨆ i, f i x) subseteq ⋃ i, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', mem_iUnion, not_exists, notMem_mulSupport]
  intro x hx
  simp only [hx, ciSup_const]

@[to_additive]
/--
lemma `mulSupport_iInf` / 引理 `mulSupport_iInf`

English:
lemma mulSupport_iInf
  given: [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α -> M)
  proof: mulSupport_iSup (M := Mᵒᵈ) f

中文:
引理 mulSupport_iInf
  条件: [条件完备格 M] [非空 ι] (f : ι -> α -> M)
  证明: mulSupport_iSup (M := Mᵒᵈ) f

Depends on / 依赖: mulSupport_iSup
-/
lemma mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι -> α -> M) :
    mulSupport (fun x => ⨅ i, f i x) subseteq ⋃ i, mulSupport (f i) := mulSupport_iSup (M := Mᵒᵈ) f

end Function

namespace Set

section LE
variable [LE M] [One M] {s : Set α} {f g : α -> M} {a : α} {y : M}

@[to_additive]
/--
lemma `mulIndicator_apply_le'` / 引理 `mulIndicator_apply_le'`

English:
lemma mulIndicator_apply_le'
  given: (hfg : a in s -> f a <= y) (hg : a ∉ s -> 1 <= y)
  proof: by
  by_cases ha : a in s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]

中文:
引理 mulIndicator_apply_le'
  条件: (hfg : a in s -> f a <= y) (hg : a ∉ s -> 1 <= y)
  证明: by
  by_cases ha : a in s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]
-/
lemma mulIndicator_apply_le' (hfg : a in s -> f a <= y) (hg : a ∉ s -> 1 <= y) :
    mulIndicator s f a <= y := by
  by_cases ha : a in s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]
/--
lemma `mulIndicator_le'` / 引理 `mulIndicator_le'`

English:
lemma mulIndicator_le'
  given: (hfg : forall a in s, f a <= g a) (hg : forall a, a ∉ s -> 1 <= g a)
  proof: fun _ => mulIndicator_apply_le' (hfg _) (hg _)

@[to_additive]

中文:
引理 mulIndicator_le'
  条件: (hfg : 对任意 a in s, f a <= g a) (hg : 对任意 a, a ∉ s -> 1 <= g a)
  证明: fun _ => mulIndicator_apply_le' (hfg _) (hg _)

@[to_additive]

Depends on / 依赖: mulIndicator_apply_le
-/
lemma mulIndicator_le' (hfg : forall a in s, f a <= g a) (hg : forall a, a ∉ s -> 1 <= g a) :
    mulIndicator s f <= g := fun _ => mulIndicator_apply_le' (hfg _) (hg _)

@[to_additive]
/--
lemma `le_mulIndicator_apply` / 引理 `le_mulIndicator_apply`

English:
lemma le_mulIndicator_apply
  given: (hfg : a in s -> y <= g a) (hf : a ∉ s -> y <= 1)
  proof: mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

@[to_additive]

中文:
引理 le_mulIndicator_apply
  条件: (hfg : a in s -> y <= g a) (hf : a ∉ s -> y <= 1)
  证明: mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

@[to_additive]

Depends on / 依赖: mulIndicator_apply_le
-/
lemma le_mulIndicator_apply (hfg : a in s -> y <= g a) (hf : a ∉ s -> y <= 1) :
    y <= mulIndicator s g a := mulIndicator_apply_le' (M := Mᵒᵈ) hfg hf

@[to_additive]
/--
lemma `le_mulIndicator` / 引理 `le_mulIndicator`

English:
lemma le_mulIndicator
  given: (hfg : forall a in s, f a <= g a) (hf : forall a ∉ s, f a <= 1)
  proof: fun _ => le_mulIndicator_apply (hfg _) (hf _)

中文:
引理 le_mulIndicator
  条件: (hfg : 对任意 a in s, f a <= g a) (hf : 对任意 a ∉ s, f a <= 1)
  证明: fun _ => le_mulIndicator_apply (hfg _) (hf _)

Depends on / 依赖: le_mulIndicator_apply
-/
lemma le_mulIndicator (hfg : forall a in s, f a <= g a) (hf : forall a ∉ s, f a <= 1) :
    f <= mulIndicator s g := fun _ => le_mulIndicator_apply (hfg _) (hf _)

end LE

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α -> M} {a : α}

@[to_additive indicator_apply_nonneg]
/--
lemma `one_le_mulIndicator_apply` / 引理 `one_le_mulIndicator_apply`

English:
lemma one_le_mulIndicator_apply
  given: (h : a in s -> 1 <= f a)
  statement: 1 <= mulIndicator s f a
  proof: le_mulIndicator_apply h fun _ => le_rfl

@[to_additive indicator_nonneg]

中文:
引理 one_le_mulIndicator_apply
  条件: (h : a in s -> 1 <= f a)
  结论: 1 <= mulIndicator s f a
  证明: le_mulIndicator_apply h fun _ => le_rfl

@[to_additive indicator_nonneg]

Depends on / 依赖: le_mulIndicator_apply, le_rfl
-/
lemma one_le_mulIndicator_apply (h : a in s -> 1 <= f a) : 1 <= mulIndicator s f a :=
  le_mulIndicator_apply h fun _ => le_rfl

@[to_additive indicator_nonneg]
/--
lemma `one_le_mulIndicator` / 引理 `one_le_mulIndicator`

English:
lemma one_le_mulIndicator
  given: (h : forall a in s, 1 <= f a) (a : α)
  statement: 1 <= mulIndicator s f a
  proof: one_le_mulIndicator_apply (h a)

@[to_additive]

中文:
引理 one_le_mulIndicator
  条件: (h : 对任意 a in s, 1 <= f a) (a : α)
  结论: 1 <= mulIndicator s f a
  证明: one_le_mulIndicator_apply (h a)

@[to_additive]

Depends on / 依赖: one_le_mulIndicator_apply
-/
lemma one_le_mulIndicator (h : forall a in s, 1 <= f a) (a : α) : 1 <= mulIndicator s f a :=
  one_le_mulIndicator_apply (h a)

@[to_additive]
/--
lemma `mulIndicator_apply_le_one` / 引理 `mulIndicator_apply_le_one`

English:
lemma mulIndicator_apply_le_one
  given: (h : a in s -> f a <= 1)
  statement: mulIndicator s f a <= 1
  proof: mulIndicator_apply_le' h fun _ => le_rfl

@[to_additive]

中文:
引理 mulIndicator_apply_le_one
  条件: (h : a in s -> f a <= 1)
  结论: mulIndicator s f a <= 1
  证明: mulIndicator_apply_le' h fun _ => le_rfl

@[to_additive]

Depends on / 依赖: le_rfl, mulIndicator_apply_le
-/
lemma mulIndicator_apply_le_one (h : a in s -> f a <= 1) : mulIndicator s f a <= 1 :=
  mulIndicator_apply_le' h fun _ => le_rfl

@[to_additive]
/--
lemma `mulIndicator_le_one` / 引理 `mulIndicator_le_one`

English:
lemma mulIndicator_le_one
  given: (h : forall a in s, f a <= 1) (a : α)
  statement: mulIndicator s f a <= 1
  proof: mulIndicator_apply_le_one (h a)

@[to_additive]

中文:
引理 mulIndicator_le_one
  条件: (h : 对任意 a in s, f a <= 1) (a : α)
  结论: mulIndicator s f a <= 1
  证明: mulIndicator_apply_le_one (h a)

@[to_additive]

Depends on / 依赖: mulIndicator_apply_le_one
-/
lemma mulIndicator_le_one (h : forall a in s, f a <= 1) (a : α) : mulIndicator s f a <= 1 :=
  mulIndicator_apply_le_one (h a)

@[to_additive]
/--
lemma `mulIndicator_le_mulIndicator'` / 引理 `mulIndicator_le_mulIndicator'`

English:
lemma mulIndicator_le_mulIndicator'
  given: (h : a in s -> f a <= g a)
  proof: mulIndicator_rel_mulIndicator le_rfl h

@[to_additive (attr := mono, gcongr only)]

中文:
引理 mulIndicator_le_mulIndicator'
  条件: (h : a in s -> f a <= g a)
  证明: mulIndicator_rel_mulIndicator le_rfl h

@[to_additive (attr := mono, gcongr only)]

Depends on / 依赖: le_rfl, mulIndicator_rel_mulIndicator
-/
lemma mulIndicator_le_mulIndicator' (h : a in s -> f a <= g a) :
    mulIndicator s f a <= mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl h

@[to_additive (attr := mono, gcongr only)]
/--
lemma `mulIndicator_le_mulIndicator` / 引理 `mulIndicator_le_mulIndicator`

English:
lemma mulIndicator_le_mulIndicator
  given: (h : f a <= g a)
  statement: mulIndicator s f a <= mulIndicator s g a
  proof: mulIndicator_rel_mulIndicator le_rfl fun _ => h

@[to_additive (attr := gcongr)]

中文:
引理 mulIndicator_le_mulIndicator
  条件: (h : f a <= g a)
  结论: mulIndicator s f a <= mulIndicator s g a
  证明: mulIndicator_rel_mulIndicator le_rfl fun _ => h

@[to_additive (attr := gcongr)]

Depends on / 依赖: le_rfl, mulIndicator_rel_mulIndicator
-/
lemma mulIndicator_le_mulIndicator (h : f a <= g a) : mulIndicator s f a <= mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl fun _ => h

@[to_additive (attr := gcongr)]
/--
lemma `mulIndicator_mono` / 引理 `mulIndicator_mono`

English:
lemma mulIndicator_mono
  given: (h : f <= g)
  statement: s.mulIndicator f <= s.mulIndicator g
  proof: fun _ => mulIndicator_le_mulIndicator (h _)

@[to_additive (attr := gcongr)]

中文:
引理 mulIndicator_mono
  条件: (h : f <= g)
  结论: s.mulIndicator f <= s.mulIndicator g
  证明: fun _ => mulIndicator_le_mulIndicator (h _)

@[to_additive (attr := gcongr)]

Depends on / 依赖: mulIndicator_le_mulIndicator
-/
lemma mulIndicator_mono (h : f <= g) : s.mulIndicator f <= s.mulIndicator g :=
  fun _ => mulIndicator_le_mulIndicator (h _)

@[to_additive (attr := gcongr)]
/--
lemma `mulIndicator_le_mulIndicator_apply_of_subset` / 引理 `mulIndicator_le_mulIndicator_apply_of_subset`

English:
lemma mulIndicator_le_mulIndicator_apply_of_subset
  given: (h : s subseteq t) (hf : 1 <= f a)
  proof: mulIndicator_apply_le'
    (fun ha => le_mulIndicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun _ =>
    one_le_mulIndicator_apply fun _ => hf

@[to_additive (attr := gcongr)]

中文:
引理 mulIndicator_le_mulIndicator_apply_of_subset
  条件: (h : s subseteq t) (hf : 1 <= f a)
  证明: mulIndicator_apply_le'
    (fun ha => le_mulIndicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun _ =>
    one_le_mulIndicator_apply fun _ => hf

@[to_additive (attr := gcongr)]

Depends on / 依赖: le_mulIndicator_apply, le_rfl, mulIndicator_apply_le, one_le_mulIndicator_apply
-/
lemma mulIndicator_le_mulIndicator_apply_of_subset (h : s subseteq t) (hf : 1 <= f a) :
    mulIndicator s f a <= mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha => le_mulIndicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun _ =>
    one_le_mulIndicator_apply fun _ => hf

@[to_additive (attr := gcongr)]
/--
lemma `mulIndicator_le_mulIndicator_of_subset` / 引理 `mulIndicator_le_mulIndicator_of_subset`

English:
lemma mulIndicator_le_mulIndicator_of_subset
  given: (h : s subseteq t) (hf : 1 <= f)
  proof: fun _ => mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

@[to_additive]

中文:
引理 mulIndicator_le_mulIndicator_of_subset
  条件: (h : s subseteq t) (hf : 1 <= f)
  证明: fun _ => mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

@[to_additive]

Depends on / 依赖: mulIndicator_le_mulIndicator_apply_of_subset
-/
lemma mulIndicator_le_mulIndicator_of_subset (h : s subseteq t) (hf : 1 <= f) :
    mulIndicator s f <= mulIndicator t f :=
  fun _ => mulIndicator_le_mulIndicator_apply_of_subset h (hf _)

@[to_additive]
/--
lemma `mulIndicator_le_self'` / 引理 `mulIndicator_le_self'`

English:
lemma mulIndicator_le_self'
  given: (hf : forall x ∉ s, 1 <= f x)
  statement: mulIndicator s f <= f
  proof: mulIndicator_le' (fun _ _ => le_rfl) hf

中文:
引理 mulIndicator_le_self'
  条件: (hf : 对任意 x ∉ s, 1 <= f x)
  结论: mulIndicator s f <= f
  证明: mulIndicator_le' (fun _ _ => le_rfl) hf

Depends on / 依赖: le_rfl, mulIndicator_le
-/
lemma mulIndicator_le_self' (hf : forall x ∉ s, 1 <= f x) : mulIndicator s f <= f :=
  mulIndicator_le' (fun _ _ => le_rfl) hf

end Preorder

section LinearOrder
variable [Zero M] [LinearOrder M]

/--
lemma `indicator_le_indicator_nonneg` / 引理 `indicator_le_indicator_nonneg`

English:
lemma indicator_le_indicator_nonneg
  given: (s : Set α) (f : α -> M)
  proof: by
  intro a
  classical
  simp_rw [indicator_apply]
  split_ifs
  exacts [le_rfl, (not_le.1 ‹_›).le, ‹_›, le_rfl]

中文:
引理 indicator_le_indicator_nonneg
  条件: (s : 集合 α) (f : α -> M)
  证明: by
  intro a
  classical
  simp_rw [indicator_apply]
  split_ifs
  exacts [le_rfl, (not_le.1 ‹_›).le, ‹_›, le_rfl]

Depends on / 依赖: classical, exacts, indicator_apply, le_rfl, not_le, simp_rw, split_ifs
-/
lemma indicator_le_indicator_nonneg (s : Set α) (f : α -> M) :
    s.indicator f <= {a | 0 <= f a}.indicator f := by
  intro a
  classical
  simp_rw [indicator_apply]
  split_ifs
  exacts [le_rfl, (not_le.1 ‹_›).le, ‹_›, le_rfl]

/--
lemma `indicator_nonpos_le_indicator` / 引理 `indicator_nonpos_le_indicator`

English:
lemma indicator_nonpos_le_indicator
  given: (s : Set α) (f : α -> M)
  proof: indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

中文:
引理 indicator_nonpos_le_indicator
  条件: (s : 集合 α) (f : α -> M)
  证明: indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

Depends on / 依赖: indicator_le_indicator_nonneg
-/
lemma indicator_nonpos_le_indicator (s : Set α) (f : α -> M) :
    {a | f a <= 0}.indicator f <= s.indicator f :=
  indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

end LinearOrder

section CompleteLattice
variable [CompleteLattice M] [One M]

@[to_additive]
/--
lemma `mulIndicator_iUnion_apply` / 引理 `mulIndicator_iUnion_apply`

English:
lemma mulIndicator_iUnion_apply
  given: (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M) (x : α)
  proof: by
  by_cases hx : x in ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i => mulIndicator_le_self' (fun x _ => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of

中文:
引理 mulIndicator_iUnion_apply
  条件: (h1 : (⊥ : M) = 1) (s : ι -> 集合 α) (f : α -> M) (x : α)
  证明: by
  by_cases hx : x in ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i => mulIndicator_le_self' (fun x _ => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of

Depends on / 依赖: bot_le, ge_of_eq, iSup_le, le_antisymm, le_iSup_of_le, mem_iUnion, mulIndicator_le_self, mulIndicator_of_mem, mulIndicator_of_notMem, not_exists
-/
lemma mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases hx : x in ⋃ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iUnion] at hx
    refine le_antisymm ?_ (iSup_le fun i => mulIndicator_le_self' (fun x _ => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_iSup_of_le i (ge_of_eq <| mulIndicator_of_mem hi _)
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iUnion, not_exists] at hx
    simp [hx, ← h1]

variable [Nonempty ι]

@[to_additive]
/--
lemma `mulIndicator_iInter_apply` / 引理 `mulIndicator_iInter_apply`

English:
lemma mulIndicator_iInter_apply
  given: (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M) (x : α)
  proof: by
  by_cases hx : x in ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i => (

中文:
引理 mulIndicator_i整数er_apply
  条件: (h1 : (⊥ : M) = 1) (s : ι -> 集合 α) (f : α -> M) (x : α)
  证明: by
  by_cases hx : x in ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i => (

Depends on / 依赖: bot_le, forall_const, iInf_le, le_antisymm, le_iInf_iff, mem_iInter, mulIndicator, mulIndicator_of_notMem, not_forall
-/
lemma mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι -> Set α) (f : α -> M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x in ⋂ i, s i
  · simp_all
  · rw [mulIndicator_of_notMem hx]
    simp only [mem_iInter, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm (by simp only [← h1, le_iInf_iff, bot_le, forall_const]) ?_
    simpa [mulIndicator_of_notMem hj] using (iInf_le (fun i => (s i).mulIndicator f) j) x

@[to_additive]
/--
lemma `iSup_mulIndicator` / 引理 `iSup_mulIndicator`

English:
lemma iSup_mulIndicator
  statement: {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f : ι -> α -> M}
  proof: by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i => ?_, fun a => ?_⟩
  · grw [← le_iSup f i, ← subset_iUnion s i]
    intro; simp [← h1]
  by_cases ha : a in ⋃ i, s i
  · obtain ⟨i, hi⟩ : exists i, a in s i := by simpa using ha
    rw [mulIndicator_of_mem ha]; rw [iSup_apply]; rw [iSup_

中文:
引理 iSup_mulIndicator
  结论: {ι : 类型} [预序 ι] [IsDirectedOrder ι] {f : ι -> α -> M}
  证明: by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i => ?_, fun a => ?_⟩
  · grw [← le_iSup f i, ← subset_iUnion s i]
    intro; simp [← h1]
  by_cases ha : a in ⋃ i, s i
  · obtain ⟨i, hi⟩ : exists i, a in s i := by simpa using ha
    rw [mulIndicator_of_mem ha]; rw [iSup_apply]; rw [iSup_

Depends on / 依赖: bot_le, exists_ge_ge, iSup_apply, iSup_le, iSup_le_iff, le_antisymm_iff, le_iSup, le_iSup_of_le, mulIndicator_of_mem, mulIndicator_of_notMem, subset_iUnion, trans_eq
-/
lemma iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f : ι -> α -> M}
    {s : ι -> Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by
  simp only [le_antisymm_iff, iSup_le_iff]
  refine ⟨fun i => ?_, fun a => ?_⟩
  · grw [← le_iSup f i, ← subset_iUnion s i]
    intro; simp [← h1]
  by_cases ha : a in ⋃ i, s i
  · obtain ⟨i, hi⟩ : exists i, a in s i := by simpa using ha
    rw [mulIndicator_of_mem ha]; rw [iSup_apply]; rw [iSup_apply]
    refine iSup_le fun j => ?_
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
refine le_iSup_of_le k (hf hjk _).trans_eq ?_
    rw [mulIndicator_of_mem (hs hik hi)]
  · rw [mulIndicator_of_notMem ha, ← h1]
    exact bot_le

end CompleteLattice

section CanonicallyOrderedMul

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

@[to_additive]
/--
lemma `mulIndicator_le_self` / 引理 `mulIndicator_le_self`

English:
lemma mulIndicator_le_self
  given: (s : Set α) (f : α -> M)
  statement: mulIndicator s f <= f
  proof: mulIndicator_le_self' fun _ _ => one_le

@[to_additive]

中文:
引理 mulIndicator_le_self
  条件: (s : 集合 α) (f : α -> M)
  结论: mulIndicator s f <= f
  证明: mulIndicator_le_self' fun _ _ => one_le

@[to_additive]

Depends on / 依赖: mulIndicator_le_self, one_le
-/
lemma mulIndicator_le_self (s : Set α) (f : α -> M) : mulIndicator s f <= f :=
  mulIndicator_le_self' fun _ _ => one_le

@[to_additive]
/--
lemma `mulIndicator_apply_le` / 引理 `mulIndicator_apply_le`

English:
lemma mulIndicator_apply_le
  given: {a : α} {s : Set α} {f g : α -> M} (hfg : a in s -> f a <= g a)
  proof: mulIndicator_apply_le' hfg fun _ => one_le

@[to_additive]

中文:
引理 mulIndicator_apply_le
  条件: {a : α} {s : 集合 α} {f g : α -> M} (hfg : a in s -> f a <= g a)
  证明: mulIndicator_apply_le' hfg fun _ => one_le

@[to_additive]

Depends on / 依赖: mulIndicator_apply_le, one_le
-/
lemma mulIndicator_apply_le {a : α} {s : Set α} {f g : α -> M} (hfg : a in s -> f a <= g a) :
    mulIndicator s f a <= g a :=
  mulIndicator_apply_le' hfg fun _ => one_le

@[to_additive]
/--
lemma `mulIndicator_le` / 引理 `mulIndicator_le`

English:
lemma mulIndicator_le
  given: {s : Set α} {f g : α -> M} (hfg : forall a in s, f a <= g a)
  proof: mulIndicator_le' hfg fun _ _ => one_le

中文:
引理 mulIndicator_le
  条件: {s : 集合 α} {f g : α -> M} (hfg : 对任意 a in s, f a <= g a)
  证明: mulIndicator_le' hfg fun _ _ => one_le

Depends on / 依赖: mulIndicator_le, one_le
-/
lemma mulIndicator_le {s : Set α} {f g : α -> M} (hfg : forall a in s, f a <= g a) :
    mulIndicator s f <= g :=
  mulIndicator_le' hfg fun _ _ => one_le

end CanonicallyOrderedMul

section LatticeOrderedCommGroup
variable [CommGroup M] [Lattice M]

open scoped symmDiff

@[to_additive]
/--
lemma `mabs_mulIndicator_symmDiff` / 引理 `mabs_mulIndicator_symmDiff`

English:
lemma mabs_mulIndicator_symmDiff
  given: (s t : Set α) (f : α -> M) (x : α)
  proof: apply_mulIndicator_symmDiff mabs_inv s t f x

中文:
引理 mabs_mulIndicator_symmDiff
  条件: (s t : 集合 α) (f : α -> M) (x : α)
  证明: apply_mulIndicator_symmDiff mabs_inv s t f x

Depends on / 依赖: apply_mulIndicator_symmDiff, mabs_inv
-/
lemma mabs_mulIndicator_symmDiff (s t : Set α) (f : α -> M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ :=
  apply_mulIndicator_symmDiff mabs_inv s t f x

end LatticeOrderedCommGroup
end Set
