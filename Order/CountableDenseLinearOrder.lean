/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Data.Finset.Max

/-!
# The back and forth method and countable dense linear orders

## Results

Suppose `α β` are linear orders, with `α` countable and `β` dense, nontrivial. Then there is an
order embedding `α ↪ β`. If in addition `α` is dense, nonempty, without endpoints and `β` is
countable, without endpoints, then we can upgrade this to an order isomorphism `α ≃ β`.

The idea for both results is to consider "partial isomorphisms", which identify a finite subset of
`α` with a finite subset of `β`, and prove that for any such partial isomorphism `f` and `a : α`, we
can extend `f` to include `a` in its domain.

## References

https://en.wikipedia.org/wiki/Back-and-forth_method

## Tags

back and forth, dense, countable, order
-/

@[expose] public section


noncomputable section

namespace Order

variable {α β : Type*} [LinearOrder α] [LinearOrder β]
/--
theorem `exists_between_finsets` / 定理 `exists_between_finsets`

English:
theorem exists_between_finsets
  statement: [DenselyOrdered α] [NoMinOrder α]
  proof: if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use `DenselyOrdered`
        Exists.elim
        (exists_between (lo_lt_hi _ (Finset.max'_mem _ nlo) _ (Finset.min'_mem _ nhi))) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm.1, fun y hy =>
          lt_of_lt_of_le hm.2 (Finset.min'_le hi y hy)⟩
    else -- upper set is empty, use `NoMaxOrder`
        Exists.elim
        (exists_gt (Finset.max' lo nlo)) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm, fun y hy => (nhi ⟨y, hy⟩).elim⟩
  else
    if nhi : hi.Nonempty then
      -- lower set is empty, use `NoMinOrder`
        Exists.elim
        (exists_lt (Finset.min' hi nhi)) fun m hm =>
        ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => lt_of_lt_of_le hm (Finset.min'_le hi y hy)⟩
    else -- both sets are empty, use `Nonempty`
          nonem.elim
        fun m => ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => (nhi ⟨y, hy⟩).elim⟩

中文:
定理 存在_between_finsets
  结论: [稠密序 α] [NoMin序 α]
  证明: if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use `DenselyOrdered`
        Exists.elim
        (exists_between (lo_lt_hi _ (Finset.max'_mem _ nlo) _ (Finset.min'_mem _ nhi))) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm.1, fun y hy =>
          lt_of_lt_of_le hm.2 (Finset.min'_le hi y hy)⟩
    else -- upper set is empty, use `NoMaxOrder`
        Exists.elim
        (exists_gt (Finset.max' lo nlo)) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm, fun y hy => (nhi ⟨y, hy⟩).elim⟩
  else
    if nhi : hi.Nonempty then
      -- lower set is empty, use `NoMinOrder`
        Exists.elim
        (exists_lt (Finset.min' hi nhi)) fun m hm =>
        ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => lt_of_lt_of_le hm (Finset.min'_le hi y hy)⟩
    else -- both sets are empty, use `Nonempty`
          nonem.elim
        fun m => ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => (nhi ⟨y, hy⟩).elim⟩

Depends on / 依赖: Nonempty, hi.Nonempty, lo.Nonempty
-/
theorem exists_between_finsets [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [nonem : Nonempty α] (lo hi : Finset α) (lo_lt_hi : forall x in lo, forall y in hi, x < y) :
    exists m : α, (forall x in lo, x < m) ∧ forall y in hi, m < y :=
  if nlo : lo.Nonempty then
    if nhi : hi.Nonempty then
      -- both sets are nonempty, use `DenselyOrdered`
        Exists.elim
        (exists_between (lo_lt_hi _ (Finset.max'_mem _ nlo) _ (Finset.min'_mem _ nhi))) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm.1, fun y hy =>
          lt_of_lt_of_le hm.2 (Finset.min'_le hi y hy)⟩
    else -- upper set is empty, use `NoMaxOrder`
        Exists.elim
        (exists_gt (Finset.max' lo nlo)) fun m hm =>
        ⟨m, fun x hx => lt_of_le_of_lt (Finset.le_max' lo x hx) hm, fun y hy => (nhi ⟨y, hy⟩).elim⟩
  else
    if nhi : hi.Nonempty then
      -- lower set is empty, use `NoMinOrder`
        Exists.elim
        (exists_lt (Finset.min' hi nhi)) fun m hm =>
        ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => lt_of_lt_of_le hm (Finset.min'_le hi y hy)⟩
    else -- both sets are empty, use `Nonempty`
          nonem.elim
        fun m => ⟨m, fun x hx => (nlo ⟨x, hx⟩).elim, fun y hy => (nhi ⟨y, hy⟩).elim⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_orderEmbedding_insert` / 引理 `exists_orderEmbedding_insert`

English:
lemma exists_orderEmbedding_insert
  statement: [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β]
  proof: by
  let Slt := {x in S.attach | x.val < a}.image f
  let Sgt := {x in S.attach | a < x.val}.image f
  obtain ⟨b, hb, hb'⟩ := Order.exists_between_finsets Slt Sgt (fun x hx y hy => by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, Slt, Sgt] at hx hy
    obtain ⟨_, hx, _, rfl⟩ := hx
    obtain ⟨_, hy, _, rfl⟩ := hy
    exact f.strictMono (hx.trans hy))
  refine ⟨OrderEmbedding.ofStrictMono
    (fun (x : (insert a S : Finset α)) => if hx : x.1 in S then f ⟨x.1, hx⟩ else b) ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    if hxS : x in S
    then if hyS : y in S
      then simpa only [hxS, hyS, ↓reduceDIte, OrderEmbedding.lt_iff_lt, Subtype.mk_lt_mk]
      else
        obtain rfl := Finset.eq_of_mem_insert_of_notMem hy hyS
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
    else
      obtain rfl := Finset.eq_of_mem_insert_of_notMem hx hxS
      if hyS : y in S
      then
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb' _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
      else simp only [Finset.eq_of_mem_insert_of_notMem hy hyS, lt_self_iff_false] at hxy
  · ext x
    simp only [OrderEmbedding.coe_ofStrictMono,
      Function.comp_apply, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta]

中文:
引理 存在_orderEmbedding_insert
  结论: [稠密序 β] [NoMin序 β] [NoMax序 β]
  证明: by
  let Slt := {x in S.attach | x.val < a}.image f
  let Sgt := {x in S.attach | a < x.val}.image f
  obtain ⟨b, hb, hb'⟩ := Order.exists_between_finsets Slt Sgt (fun x hx y hy => by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, Slt, Sgt] at hx hy
    obtain ⟨_, hx, _, rfl⟩ := hx
    obtain ⟨_, hy, _, rfl⟩ := hy
    exact f.strictMono (hx.trans hy))
  refine ⟨OrderEmbedding.ofStrictMono
    (fun (x : (insert a S : Finset α)) => if hx : x.1 in S then f ⟨x.1, hx⟩ else b) ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    if hxS : x in S
    then if hyS : y in S
      then simpa only [hxS, hyS, ↓reduceDIte, OrderEmbedding.lt_iff_lt, Subtype.mk_lt_mk]
      else
        obtain rfl := Finset.eq_of_mem_insert_of_notMem hy hyS
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
    else
      obtain rfl := Finset.eq_of_mem_insert_of_notMem hx hxS
      if hyS : y in S
      then
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb' _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
      else simp only [Finset.eq_of_mem_insert_of_notMem hy hyS, lt_self_iff_false] at hxy
  · ext x
    simp only [OrderEmbedding.coe_ofStrictMono,
      Function.comp_apply, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta]

Depends on / 依赖: Finset, Finset.mem_attach, Finset.mem_filter, Finset.mem_image, Order.exists_between_finsets, OrderEmbedding, OrderEmbedding.ofStrictMono, S.attach, Subtype, Subtype.exists, attach, exists_and_left, exists_between_finsets, f.strictMono, hx.trans, insert, mem_attach, mem_filter, mem_image, ofStrictMono
-/
lemma exists_orderEmbedding_insert [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β]
    [nonem : Nonempty β] (S : Finset α) (f : S ↪o β) (a : α) :
    exists (g : (insert a S : Finset α) ↪o β),
      g ∘ (Set.inclusion ((S.subset_insert a) : ↑S subseteq ↑(insert a S))) = f := by
  let Slt := {x in S.attach | x.val < a}.image f
  let Sgt := {x in S.attach | a < x.val}.image f
  obtain ⟨b, hb, hb'⟩ := Order.exists_between_finsets Slt Sgt (fun x hx y hy => by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and, Subtype.exists,
      exists_and_left, Slt, Sgt] at hx hy
    obtain ⟨_, hx, _, rfl⟩ := hx
    obtain ⟨_, hy, _, rfl⟩ := hy
    exact f.strictMono (hx.trans hy))
  refine ⟨OrderEmbedding.ofStrictMono
    (fun (x : (insert a S : Finset α)) => if hx : x.1 in S then f ⟨x.1, hx⟩ else b) ?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    if hxS : x in S
    then if hyS : y in S
      then simpa only [hxS, hyS, ↓reduceDIte, OrderEmbedding.lt_iff_lt, Subtype.mk_lt_mk]
      else
        obtain rfl := Finset.eq_of_mem_insert_of_notMem hy hyS
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
    else
      obtain rfl := Finset.eq_of_mem_insert_of_notMem hx hxS
      if hyS : y in S
      then
        simp only [hxS, hyS, ↓reduceDIte]
        exact hb' _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hxy⟩))
      else simp only [Finset.eq_of_mem_insert_of_notMem hy hyS, lt_self_iff_false] at hxy
  · ext x
    simp only [OrderEmbedding.coe_ofStrictMono,
      Function.comp_apply, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta]

variable (α β)

/--
Definition of `PartialIso` / `PartialIso` 的定义

English:
definition PartialIso
  signature: : Type _
  body: { f : Finset (α × β) //
    forall p in f, forall q in f,
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }
deriving Preorder

中文:
定义 PartialIso
  签名: : 类型 _
  定义体: { f : Finset (α × β) //
    forall p in f, forall q in f,
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }
deriving Preorder

Depends on / 依赖: Finset, Prod.fst, Prod.snd
-/
def PartialIso : Type _ :=
  { f : Finset (α × β) //
    forall p in f, forall q in f,
      cmp (Prod.fst p) (Prod.fst q) = cmp (Prod.snd p) (Prod.snd q) }
deriving Preorder

namespace PartialIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (PartialIso α β)
  body: ⟨⟨∅, fun _p h _q => (Finset.notMem_empty _ h).elim⟩⟩

中文:
实例 :
  签名: 可居 (PartialIso α β)
  定义体: ⟨⟨∅, fun _p h _q => (Finset.notMem_empty _ h).elim⟩⟩

Depends on / 依赖: Finset, Finset.notMem_empty, notMem_empty
-/
instance : Inhabited (PartialIso α β) := ⟨⟨∅, fun _p h _q => (Finset.notMem_empty _ h).elim⟩⟩

variable {α β}

/--
theorem `exists_across` / 定理 `exists_across`

English:
theorem exists_across
  statement: [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
  proof: by
  by_cases h : exists b, (a, b) in f.val
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, fun p hp => f.prop _ hp _ hb⟩
  have :
    forall x in {p in f.val | p.fst < a}.image Prod.snd,
      forall y in {p in f.val | a < p.fst}.image Prod.snd, x < y := by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  obtain ⟨b, hb⟩ := exists_between_finsets _ _ this
  use b
  rintro ⟨p1, p2⟩ hp
  have : p1 != a := fun he => h ⟨p2, he ▸ hp⟩
  rcases lt_or_gt_of_ne this with hl | hr
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff] at this
    exact this.1.trans this.2.symm
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff]; rw [← cmp_eq_gt_iff] at this
    exact this.1.trans this.2.symm

中文:
定理 存在_across
  结论: [稠密序 β] [NoMin序 β] [NoMax序 β] [非空 β]
  证明: by
  by_cases h : exists b, (a, b) in f.val
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, fun p hp => f.prop _ hp _ hb⟩
  have :
    forall x in {p in f.val | p.fst < a}.image Prod.snd,
      forall y in {p in f.val | a < p.fst}.image Prod.snd, x < y := by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  obtain ⟨b, hb⟩ := exists_between_finsets _ _ this
  use b
  rintro ⟨p1, p2⟩ hp
  have : p1 != a := fun he => h ⟨p2, he ▸ hp⟩
  rcases lt_or_gt_of_ne this with hl | hr
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff] at this
    exact this.1.trans this.2.symm
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff]; rw [← cmp_eq_gt_iff] at this
    exact this.1.trans this.2.symm

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_image, Prod.snd, exists_between_finsets, f.prop, f.val, hp1.right, hq1.right, lt_iff_lt_of_cmp_eq_cmp, lt_trans, mem_filter, mem_image, p.fst
-/
theorem exists_across [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β]
    (f : PartialIso α β) (a : α) :
    exists b : β, forall p in f.val, cmp (Prod.fst p) a = cmp (Prod.snd p) b := by
  by_cases h : exists b, (a, b) in f.val
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, fun p hp => f.prop _ hp _ hb⟩
  have :
    forall x in {p in f.val | p.fst < a}.image Prod.snd,
      forall y in {p in f.val | a < p.fst}.image Prod.snd, x < y := by
    intro x hx y hy
    rw [Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp1, rfl⟩
    rcases hy with ⟨q, hq1, rfl⟩
    rw [Finset.mem_filter] at hp1 hq1
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp1.1 _ hq1.1)]
    exact lt_trans hp1.right hq1.right
  obtain ⟨b, hb⟩ := exists_between_finsets _ _ this
  use b
  rintro ⟨p1, p2⟩ hp
  have : p1 != a := fun he => h ⟨p2, he ▸ hp⟩
  rcases lt_or_gt_of_ne this with hl | hr
  · have : p1 < a ∧ p2 < b :=
      ⟨hl, hb.1 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hl⟩, rfl⟩)⟩
    rw [← cmp_eq_lt_iff]; rw [← cmp_eq_lt_iff] at this
    exact this.1.trans this.2.symm
  · have : a < p1 ∧ b < p2 :=
      ⟨hr, hb.2 _ (Finset.mem_image.mpr ⟨(p1, p2), Finset.mem_filter.mpr ⟨hp, hr⟩, rfl⟩)⟩
    rw [← cmp_eq_gt_iff]; rw [← cmp_eq_gt_iff] at this
    exact this.1.trans this.2.symm

/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : PartialIso α β -> PartialIso β α
  body: Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq =>
Eq.symm
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hp
          rwa [← Finset.mem_coe])
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hq
          rwa [← Finset.mem_coe])

中文:
定义 comm
  签名: : PartialIso α β -> PartialIso β α
  定义体: Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq =>
Eq.symm
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hp
          rwa [← Finset.mem_coe])
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hq
          rwa [← Finset.mem_coe])
-/
protected def comm : PartialIso α β -> PartialIso β α :=
  Subtype.map (Finset.image (Equiv.prodComm _ _)) fun f hf p hp q hq =>
Eq.symm
      hf ((Equiv.prodComm α β).symm p)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hp
          rwa [← Finset.mem_coe])
        ((Equiv.prodComm α β).symm q)
        (by
          rw [← Finset.mem_coe]; rw [Finset.coe_image]; rw [Equiv.image_eq_preimage_symm] at hq
          rwa [← Finset.mem_coe])

variable (β)

/--
Definition of `definedAtLeft` / `definedAtLeft` 的定义

English:
definition definedAtLeft
  signature: [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
  body: {f | exists b : β, (a, b) in f.val}
  isCofinal f := by
    obtain ⟨b, a_b⟩ := exists_across f a
    refine
      ⟨⟨insert (a, b) f.val, fun p hp q hq => ?_⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact a_b _ qf
    · exact a_b _ pf
    · exact f.prop _ pf _ qf

中文:
定义 definedAtLeft
  签名: [稠密序 β] [NoMin序 β] [NoMax序 β] [非空 β] (a : α)
  定义体: {f | exists b : β, (a, b) in f.val}
  isCofinal f := by
    obtain ⟨b, a_b⟩ := exists_across f a
    refine
      ⟨⟨insert (a, b) f.val, fun p hp q hq => ?_⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact a_b _ qf
    · exact a_b _ pf
    · exact f.prop _ pf _ qf

Depends on / 依赖: f.val
-/
def definedAtLeft [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α) :
    Cofinal (PartialIso α β) where
  carrier := {f | exists b : β, (a, b) in f.val}
  isCofinal f := by
    obtain ⟨b, a_b⟩ := exists_across f a
    refine
      ⟨⟨insert (a, b) f.val, fun p hp q hq => ?_⟩, ⟨b, Finset.mem_insert_self _ _⟩,
        Finset.subset_insert _ _⟩
    rw [Finset.mem_insert] at hp hq
    rcases hp with (rfl | pf) <;> rcases hq with (rfl | qf)
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact a_b _ qf
    · exact a_b _ pf
    · exact f.prop _ pf _ qf

variable (α) {β}

/--
Definition of `definedAtRight` / `definedAtRight` 的定义

English:
definition definedAtRight
  signature: [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
  body: {f | exists a, (a, b) in f.val}
  isCofinal f := by
    rcases (definedAtLeft α b).isCofinal f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    refine ⟨f'.comm, ⟨a, ?_⟩, ?_⟩
    · change (a, b) in f'.val.image _
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage_symm]
    · change _ subseteq f'.val.image _
      rwa [← Finset.coe_subset, Finset.coe_image, ← Equiv.symm_image_subset, ← Finset.coe_image,
        Finset.coe_subset]

中文:
定义 definedAtRight
  签名: [稠密序 α] [NoMin序 α] [NoMax序 α] [非空 α] (b : β)
  定义体: {f | exists a, (a, b) in f.val}
  isCofinal f := by
    rcases (definedAtLeft α b).isCofinal f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    refine ⟨f'.comm, ⟨a, ?_⟩, ?_⟩
    · change (a, b) in f'.val.image _
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage_symm]
    · change _ subseteq f'.val.image _
      rwa [← Finset.coe_subset, Finset.coe_image, ← Equiv.symm_image_subset, ← Finset.coe_image,
        Finset.coe_subset]

Depends on / 依赖: f.val
-/
def definedAtRight [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β) :
    Cofinal (PartialIso α β) where
  carrier := {f | exists a, (a, b) in f.val}
  isCofinal f := by
    rcases (definedAtLeft α b).isCofinal f.comm with ⟨f', ⟨a, ha⟩, hl⟩
    refine ⟨f'.comm, ⟨a, ?_⟩, ?_⟩
    · change (a, b) in f'.val.image _
      rwa [← Finset.mem_coe, Finset.coe_image, Equiv.image_eq_preimage_symm]
    · change _ subseteq f'.val.image _
      rwa [← Finset.coe_subset, Finset.coe_image, ← Equiv.symm_image_subset, ← Finset.coe_image,
        Finset.coe_subset]

variable {α}

/--
Definition of `funOfIdeal` / `funOfIdeal` 的定义

English:
definition funOfIdeal
  signature: [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
  body: Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ => ⟨b, f, hf, hb⟩

中文:
定义 funOfIdeal
  签名: [稠密序 β] [NoMin序 β] [NoMax序 β] [非空 β] (a : α)
  定义体: Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ => ⟨b, f, hf, hb⟩

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription
-/
def funOfIdeal [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] (a : α)
    (I : Ideal (PartialIso α β)) :
    (exists f, f in definedAtLeft β a ∧ f in I) -> { b // exists f in I, (a, b) in Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨b, hb⟩, hf⟩ => ⟨b, f, hf, hb⟩

/--
Definition of `invOfIdeal` / `invOfIdeal` 的定义

English:
definition invOfIdeal
  signature: [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
  body: Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ => ⟨a, f, hf, ha⟩

中文:
定义 invOfIdeal
  签名: [稠密序 α] [NoMin序 α] [NoMax序 α] [非空 α] (b : β)
  定义体: Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ => ⟨a, f, hf, ha⟩

Depends on / 依赖: Classical, Classical.indefiniteDescription, indefiniteDescription
-/
def invOfIdeal [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α] (b : β)
    (I : Ideal (PartialIso α β)) :
    (exists f, f in definedAtRight α b ∧ f in I) -> { a // exists f in I, (a, b) in Subtype.val f } :=
  Classical.indefiniteDescription _ ∘ fun ⟨f, ⟨a, ha⟩, hf⟩ => ⟨a, f, hf, ha⟩

end PartialIso

open PartialIso

-- variable (α β)

/--
theorem `embedding_from_countable_to_dense` / 定理 `embedding_from_countable_to_dense`

English:
theorem embedding_from_countable_to_dense
  given: [Countable α] [DenselyOrdered β] [Nontrivial β]
  proof: by
  cases nonempty_encodable α
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  obtain ⟨a, ha⟩ := exists_between hxy
  have : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  let our_ideal : Ideal (PartialIso α _) :=
    idealOfCofinals default (definedAtLeft (Set.Ioo x y))
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ _ a)
  refine
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a => (F a).val) fun a₁ a₂ => ?_)
        (OrderEmbedding.subtype _)⟩
  rcases (F a₁).prop with ⟨f, hf, ha₁⟩
  rcases (F a₂).prop with ⟨g, hg, ha₂⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, _hm, fm, gm⟩
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp

中文:
定理 embedding_from_countable_to_dense
  条件: [可数 α] [稠密序 β] [非平凡 β]
  证明: by
  cases nonempty_encodable α
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  obtain ⟨a, ha⟩ := exists_between hxy
  have : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  let our_ideal : Ideal (PartialIso α _) :=
    idealOfCofinals default (definedAtLeft (Set.Ioo x y))
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ _ a)
  refine
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a => (F a).val) fun a₁ a₂ => ?_)
        (OrderEmbedding.subtype _)⟩
  rcases (F a₁).prop with ⟨f, hf, ha₁⟩
  rcases (F a₂).prop with ⟨g, hg, ha₂⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, _hm, fm, gm⟩
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp

Depends on / 依赖: Nonempty, OrderEmbedding, OrderEmbedding.ofStrictMono, OrderEmbedding.subtype, PartialIso, RelEmbedding, RelEmbedding.trans, Set.Ioo, cofinal_meets_idealOfCofinals, definedAtLeft, exists_between, exists_pair_lt, funOfIdeal, idealOfCofinals, nonempty_encodable, ofStrictMono, our_ideal, subtype
-/
theorem embedding_from_countable_to_dense [Countable α] [DenselyOrdered β] [Nontrivial β] :
    Nonempty (α ↪o β) := by
  cases nonempty_encodable α
  rcases exists_pair_lt β with ⟨x, y, hxy⟩
  obtain ⟨a, ha⟩ := exists_between hxy
  have : Nonempty (Set.Ioo x y) := ⟨⟨a, ha⟩⟩
  let our_ideal : Ideal (PartialIso α _) :=
    idealOfCofinals default (definedAtLeft (Set.Ioo x y))
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ _ a)
  refine
    ⟨RelEmbedding.trans (OrderEmbedding.ofStrictMono (fun a => (F a).val) fun a₁ a₂ => ?_)
        (OrderEmbedding.subtype _)⟩
  rcases (F a₁).prop with ⟨f, hf, ha₁⟩
  rcases (F a₂).prop with ⟨g, hg, ha₂⟩
  rcases our_ideal.directed _ hf _ hg with ⟨m, _hm, fm, gm⟩
  exact (lt_iff_lt_of_cmp_eq_cmp <| m.prop (a₁, _) (fm ha₁) (a₂, _) (gm ha₂)).mp

/--
theorem `iso_of_countable_dense` / 定理 `iso_of_countable_dense`

English:
theorem iso_of_countable_dense
  statement: [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
  proof: by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let to_cofinal : α oplus β -> Cofinal (PartialIso α β) := fun p =>
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  exact ⟨OrderIso.ofCmpEqCmp (fun a => (F a).val) (fun b => (G b).val) fun a b => by
      rcases (F a).prop with ⟨f, hf, ha⟩
      rcases (G b).prop with ⟨g, hg, hb⟩
      rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩

中文:
定理 iso_of_countable_dense
  结论: [可数 α] [稠密序 α] [NoMin序 α] [NoMax序 α]
  证明: by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let to_cofinal : α oplus β -> Cofinal (PartialIso α β) := fun p =>
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  exact ⟨OrderIso.ofCmpEqCmp (fun a => (F a).val) (fun b => (G b).val) fun a b => by
      rcases (F a).prop with ⟨f, hf, ha⟩
      rcases (G b).prop with ⟨g, hg, hb⟩
      rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩

Depends on / 依赖: Cofinal, OrderIso, OrderIso.ofCmpEqCmp, PartialIso, Sum.inl, Sum.inr, Sum.recOn, cofinal_meets_idealOfCofinals, definedAtLeft, definedAtRight, funOfIdeal, idealOfCofinals, invOfIdeal, nonempty_encodable, ofCmpEqCmp, our_ideal, to_cofinal
-/
theorem iso_of_countable_dense [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let to_cofinal : α oplus β -> Cofinal (PartialIso α β) := fun p =>
    Sum.recOn p (definedAtLeft β) (definedAtRight α)
  let our_ideal : Ideal (PartialIso α β) := idealOfCofinals default to_cofinal
  let F a := funOfIdeal a our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inl a))
  let G b := invOfIdeal b our_ideal (cofinal_meets_idealOfCofinals _ to_cofinal (Sum.inr b))
  exact ⟨OrderIso.ofCmpEqCmp (fun a => (F a).val) (fun b => (G b).val) fun a b => by
      rcases (F a).prop with ⟨f, hf, ha⟩
      rcases (G b).prop with ⟨g, hg, hb⟩
      rcases our_ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
      exact m.prop (a, _) (fm ha) (_, b) (gm hb)⟩

end Order
