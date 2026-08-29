/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Order.SetNotation

/-!
# Unions of finite sets

This file defines the union of a family `t : α → Finset β` of finsets bounded by a finset
`s : Finset α`.

## Main declarations

* `Finset.disjUnion`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disjUnion t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.
* `Finset.biUnion`: Finite unions of finsets; given an indexing function `f : α → Finset β` and an
  `s : Finset α`, `s.biUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.

## TODO

Remove `Finset.biUnion` in favour of `Finset.sup`.
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

variable {α β γ : Type*} {s s₁ s₂ : Finset α} {t t₁ t₂ : α -> Finset β}

namespace Finset
section DisjiUnion

/--
Definition of `disjiUnion` / `disjiUnion` 的定义

English:
definition disjiUnion
  signature: (s : Finset α) (t : α -> Finset β) (hf : (s : Set α).PairwiseDisjoint t)
  body: ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
⟨fun a _ => (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab => disjoint_val.2 hf ha hb hab⟩⟩

@[simp]

中文:
定义 disjiUnion
  签名: (s : 有限集 α) (t : α -> 有限集 β) (hf : (s : 集合 α).PairwiseDisjoint t)
  定义体: ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
⟨fun a _ => (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab => disjoint_val.2 hf ha hb hab⟩⟩

@[simp]

Depends on / 依赖: Finset, Finset.val, Multiset, Multiset.nodup_bind, disjoint_val, nodup_bind, pairwise, s.nodup.pairwise, s.val.bind
-/
def disjiUnion (s : Finset α) (t : α -> Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
⟨fun a _ => (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab => disjoint_val.2 hf ha hb hab⟩⟩

@[simp]
/--
lemma `disjiUnion_val` / 引理 `disjiUnion_val`

English:
lemma disjiUnion_val
  given: (s : Finset α) (t : α -> Finset β) (h)
  proof: rfl

中文:
引理 disjiUnion_val
  条件: (s : 有限集 α) (t : α -> 有限集 β) (h)
  证明: rfl
-/
lemma disjiUnion_val (s : Finset α) (t : α -> Finset β) (h) :
    (s.disjiUnion t h).1 = s.1.bind fun a => (t a).1 := rfl

/--
lemma `disjiUnion_empty` / 引理 `disjiUnion_empty`

English:
lemma disjiUnion_empty
  given: (t : α -> Finset β)
  statement: disjiUnion ∅ t (by simp) = ∅
  proof: rfl

中文:
引理 disjiUnion_empty
  条件: (t : α -> 有限集 β)
  结论: disjiUnion ∅ t (by simp) = ∅
  证明: rfl
-/
@[simp] lemma disjiUnion_empty (t : α -> Finset β) : disjiUnion ∅ t (by simp) = ∅ := rfl

/--
lemma `mem_disjiUnion` / 引理 `mem_disjiUnion`

English:
lemma mem_disjiUnion
  given: {b : β} {h}
  statement: b in s.disjiUnion t h ↔ exists a in s, b in t a
  proof: by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind]

@[simp, norm_cast]

中文:
引理 mem_disjiUnion
  条件: {b : β} {h}
  结论: b in s.disjiUnion t h ↔ 存在 a in s, b in t a
  证明: by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind]

@[simp, norm_cast]
-/
@[simp, grind =] lemma mem_disjiUnion {b : β} {h} : b in s.disjiUnion t h ↔ exists a in s, b in t a := by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind]

@[simp, norm_cast]
/--
lemma `coe_disjiUnion` / 引理 `coe_disjiUnion`

English:
lemma coe_disjiUnion
  given: {h}
  statement: (s.disjiUnion t h : Set β) = ⋃ x in (s : Set α), t x
  proof: by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion]

中文:
引理 coe_disjiUnion
  条件: {h}
  结论: (s.disjiUnion t h : 集合 β) = ⋃ x in (s : 集合 α), t x
  证明: by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion]

Depends on / 依赖: Set.ext_iff, Set.mem_iUnion, ext_iff, mem_disjiUnion, mem_iUnion
-/
lemma coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x in (s : Set α), t x := by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion]

/--
lemma `disjiUnion_cons` / 引理 `disjiUnion_cons`

English:
lemma disjiUnion_cons
  given: (a : α) (s : Finset α) (ha : a ∉ s) (f : α -> Finset β) (H)
  proof: eq_of_veq Multiset.cons_bind _ _ _

中文:
引理 disjiUnion_cons
  条件: (a : α) (s : 有限集 α) (ha : a ∉ s) (f : α -> 有限集 β) (H)
  证明: eq_of_veq Multiset.cons_bind _ _ _
-/
@[simp] lemma disjiUnion_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α -> Finset β) (H) :
    disjiUnion (cons a s ha) f H =
    (f a).disjUnion ((s.disjiUnion f) fun _ hb _ hc => H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
      (disjoint_left.2 fun _ hb h =>
        let ⟨_, hc, h⟩ := mem_disjiUnion.mp h
        disjoint_left.mp
          (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
eq_of_veq Multiset.cons_bind _ _ _

/--
lemma `singleton_disjiUnion` / 引理 `singleton_disjiUnion`

English:
lemma singleton_disjiUnion
  given: (a : α) {h}
  statement: Finset.disjiUnion {a} t h = t a
  proof: eq_of_veq Multiset.singleton_bind _ _

中文:
引理 singleton_disjiUnion
  条件: (a : α) {h}
  结论: 有限集.disjiUnion {a} t h = t a
  证明: eq_of_veq Multiset.singleton_bind _ _
-/
@[simp] lemma singleton_disjiUnion (a : α) {h} : Finset.disjiUnion {a} t h = t a :=
eq_of_veq Multiset.singleton_bind _ _

/--
lemma `disjiUnion_disjiUnion` / 引理 `disjiUnion_disjiUnion`

English:
lemma disjiUnion_disjiUnion
  given: (s : Finset α) (f : α -> Finset β) (g : β -> Finset γ) (h1 h2)
  proof: mem_disjiUnion.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          refine disjoint_left.mp
            (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) ?_) hga
            hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
eq_of_veq Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm

中文:
引理 disjiUnion_disjiUnion
  条件: (s : 有限集 α) (f : α -> 有限集 β) (g : β -> 有限集 γ) (h1 h2)
  证明: mem_disjiUnion.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          refine disjoint_left.mp
            (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) ?_) hga
            hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
eq_of_veq Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm

Depends on / 依赖: mem_disjiUnion, mem_disjiUnion.mp
-/
lemma disjiUnion_disjiUnion (s : Finset α) (f : α -> Finset β) (g : β -> Finset γ) (h1 h2) :
    (s.disjiUnion f h1).disjiUnion g h2 =
      s.attach.disjiUnion
        (fun a => ((f a).disjiUnion g) fun _ hb _ hc =>
            h2 (mem_disjiUnion.mpr ⟨_, a.prop, hb⟩) (mem_disjiUnion.mpr ⟨_, a.prop, hc⟩))
        fun a _ b _ hab =>
        disjoint_left.mpr fun x hxa hxb => by
          obtain ⟨xa, hfa, hga⟩ := mem_disjiUnion.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          refine disjoint_left.mp
            (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) ?_) hga
            hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
eq_of_veq Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm

/--
lemma `sUnion_disjiUnion` / 引理 `sUnion_disjiUnion`

English:
lemma sUnion_disjiUnion
  statement: {f : α -> Finset (Set β)} (I : Finset α)
  proof: by
  ext
  simp only [coe_disjiUnion, Set.mem_sUnion, Set.mem_iUnion, mem_coe, exists_prop]
  tauto

中文:
引理 sUnion_disjiUnion
  结论: {f : α -> 有限集 (集合 β)} (I : 有限集 α)
  证明: by
  ext
  simp only [coe_disjiUnion, Set.mem_sUnion, Set.mem_iUnion, mem_coe, exists_prop]
  tauto

Depends on / 依赖: Set.mem_iUnion, Set.mem_sUnion, coe_disjiUnion, exists_prop, mem_coe, mem_iUnion, mem_sUnion
-/
lemma sUnion_disjiUnion {f : α -> Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a in I, ⋃₀ ↑(f a) := by
  ext
  simp only [coe_disjiUnion, Set.mem_sUnion, Set.mem_iUnion, mem_coe, exists_prop]
  tauto

section DecidableEq

variable [DecidableEq β] {s : Finset α} {t : Finset β} {f : α -> β}

set_option backward.privateInPublic true in
/--
lemma `pairwiseDisjoint_fibers` / 引理 `pairwiseDisjoint_fibers`

English:
lemma pairwiseDisjoint_fibers
  statement: Set.PairwiseDisjoint ↑t fun a => s.filter (f · = a)
  proof: fun x' hx y' hy hne => by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

中文:
引理 pairwiseDisjoint_fibers
  结论: 集合.PairwiseDisjoint ↑t fun a => s.filter (f · = a)
  证明: fun x' hx y' hy hne => by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl
-/
private lemma pairwiseDisjoint_fibers : Set.PairwiseDisjoint ↑t fun a => s.filter (f · = a) :=
  fun x' hx y' hy hne => by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `disjiUnion_filter_eq` / 引理 `disjiUnion_filter_eq`

English:
lemma disjiUnion_filter_eq
  given: (s : Finset α) (t : Finset β) (f : α -> β)
  proof: ext fun b => by simpa using and_comm

中文:
引理 disjiUnion_filter_eq
  条件: (s : 有限集 α) (t : 有限集 β) (f : α -> β)
  证明: ext fun b => by simpa using and_comm
-/
@[simp] lemma disjiUnion_filter_eq (s : Finset α) (t : Finset β) (f : α -> β) :
    t.disjiUnion (fun a => s.filter (f · = a)) pairwiseDisjoint_fibers =
      s.filter fun c => f c in t :=
  ext fun b => by simpa using and_comm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `disjiUnion_filter_eq_of_maps_to` / 引理 `disjiUnion_filter_eq_of_maps_to`

English:
lemma disjiUnion_filter_eq_of_maps_to
  given: (h : forall x in s, f x in t)
  proof: by
  simpa [filter_eq_self]

中文:
引理 disjiUnion_filter_eq_of_maps_to
  条件: (h : 对任意 x in s, f x in t)
  证明: by
  simpa [filter_eq_self]

Depends on / 依赖: filter_eq_self
-/
lemma disjiUnion_filter_eq_of_maps_to (h : forall x in s, f x in t) :
    t.disjiUnion (fun a => s.filter (f · = a)) pairwiseDisjoint_fibers = s := by
  simpa [filter_eq_self]

end DecidableEq

/--
theorem `map_disjiUnion` / 定理 `map_disjiUnion`

English:
theorem map_disjiUnion
  given: {f : α ↪ β} {s : Finset α} {t : β -> Finset γ} {h}
  proof: eq_of_veq Multiset.bind_map _ _ _

中文:
定理 map_disjiUnion
  条件: {f : α ↪ β} {s : 有限集 α} {t : β -> 有限集 γ} {h}
  证明: eq_of_veq Multiset.bind_map _ _ _

Depends on / 依赖: Multiset, Multiset.bind_map, bind_map, eq_of_veq
-/
theorem map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β -> Finset γ} {h} :
    (s.map f).disjiUnion t h =
      s.disjiUnion (fun a => t (f a)) fun _ ha _ hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab) :=
eq_of_veq Multiset.bind_map _ _ _

/--
theorem `disjiUnion_map` / 定理 `disjiUnion_map`

English:
theorem disjiUnion_map
  given: {s : Finset α} {t : α -> Finset β} {f : β ↪ γ} {h}
  proof: eq_of_veq Multiset.map_bind _ _ _

@[simp]

中文:
定理 disjiUnion_map
  条件: {s : 有限集 α} {t : α -> 有限集 β} {f : β ↪ γ} {h}
  证明: eq_of_veq Multiset.map_bind _ _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.map_bind, eq_of_veq, map_bind
-/
theorem disjiUnion_map {s : Finset α} {t : α -> Finset β} {f : β ↪ γ} {h} :
    (s.disjiUnion t h).map f =
      s.disjiUnion (fun a => (t a).map f) (h.mono' fun _ _ => (disjoint_map _).2) :=
eq_of_veq Multiset.map_bind _ _ _

@[simp]
/--
theorem `disjiUnion_singleton_eq_self` / 定理 `disjiUnion_singleton_eq_self`

English:
theorem disjiUnion_singleton_eq_self
  given: (s : Finset α)
  proof: by
  grind

中文:
定理 disjiUnion_singleton_eq_self
  条件: (s : 有限集 α)
  证明: by
  grind
-/
theorem disjiUnion_singleton_eq_self (s : Finset α) :
    s.disjiUnion singleton (fun _ _ => by simp) = s := by
  grind

variable {f : α -> β} {op : β -> β -> β} [hc : Std.Commutative op] [ha : Std.Associative op]

/--
theorem `fold_disjiUnion` / 定理 `fold_disjiUnion`

English:
theorem fold_disjiUnion
  given: {ι : Type*} {s : Finset ι} {t : ι -> Finset α} {b : ι -> β} {b₀ : β} (h)
  proof: (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)

中文:
定理 fold_disjiUnion
  条件: {ι : 类型} {s : 有限集 ι} {t : ι -> 有限集 α} {b : ι -> β} {b₀ : β} (h)
  证明: (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)

Depends on / 依赖: Multiset, Multiset.fold_bind, Multiset.map_bind, congr_arg, fold_bind, map_bind
-/
theorem fold_disjiUnion {ι : Type*} {s : Finset ι} {t : ι -> Finset α} {b : ι -> β} {b₀ : β} (h) :
    (s.disjiUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fun i => (t i).fold op (b i) f :=
  (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)

/--
lemma `pairwiseDisjoint_filter` / 引理 `pairwiseDisjoint_filter`

English:
lemma pairwiseDisjoint_filter
  statement: {f : α -> Finset β} (h : Set.PairwiseDisjoint ↑s f)
  proof: fun _ h₁ _ h₂ hne => Finset.disjoint_filter_filter (h h₁ h₂ hne)

中文:
引理 pairwiseDisjoint_filter
  结论: {f : α -> 有限集 β} (h : 集合.PairwiseDisjoint ↑s f)
  证明: fun _ h₁ _ h₂ hne => Finset.disjoint_filter_filter (h h₁ h₂ hne)

Depends on / 依赖: Finset, Finset.disjoint_filter_filter, disjoint_filter_filter
-/
lemma pairwiseDisjoint_filter {f : α -> Finset β} (h : Set.PairwiseDisjoint ↑s f)
    (p : β -> Prop) [DecidablePred p] : Set.PairwiseDisjoint ↑s fun a => (f a).filter p :=
  fun _ h₁ _ h₂ hne => Finset.disjoint_filter_filter (h h₁ h₂ hne)

/--
theorem `filter_disjiUnion` / 定理 `filter_disjiUnion`

English:
theorem filter_disjiUnion
  given: (s : Finset α) (f : α -> Finset β) (h) (p : β -> Prop) [DecidablePred p]
  proof: by grind

中文:
定理 filter_disjiUnion
  条件: (s : 有限集 α) (f : α -> 有限集 β) (h) (p : β -> 命题) [DecidablePred p]
  证明: by grind
-/
theorem filter_disjiUnion (s : Finset α) (f : α -> Finset β) (h) (p : β -> Prop) [DecidablePred p] :
    (s.disjiUnion f h).filter p
      = s.disjiUnion (fun a => (f a).filter p) (pairwiseDisjoint_filter h p) := by grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `disjiUnion_singleton` / 定理 `disjiUnion_singleton`

English:
theorem disjiUnion_singleton
  given: {f : α -> β} (hf : f.Injective)
  proof: by
  ext; simp [eq_comm]

中文:
定理 disjiUnion_singleton
  条件: {f : α -> β} (hf : f.单射)
  证明: by
  ext; simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem disjiUnion_singleton {f : α -> β} (hf : f.Injective) :
    s.disjiUnion (fun a => {f a}) (fun _ _ _ _ => disjoint_singleton.mpr ∘ hf.ne) =
      s.map ⟨f, hf⟩ := by
  ext; simp [eq_comm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `disjoint_disjiUnion_left` / 引理 `disjoint_disjiUnion_left`

English:
lemma disjoint_disjiUnion_left
  proof: by
  induction s using Finset.cons_induction <;> simp_all

中文:
引理 disjoint_disjiUnion_left
  证明: by
  induction s using Finset.cons_induction <;> simp_all

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma disjoint_disjiUnion_left
    (s : Finset α) (f : α -> Finset β) (hf : Set.PairwiseDisjoint s f) (t : Finset β) :
    Disjoint (s.disjiUnion f hf) t ↔ forall i in s, Disjoint (f i) t := by
  induction s using Finset.cons_induction <;> simp_all

/--
lemma `disjoint_disjiUnion_right` / 引理 `disjoint_disjiUnion_right`

English:
lemma disjoint_disjiUnion_right
  proof: by
  simpa only [_root_.disjoint_comm] using disjoint_disjiUnion_left t f hf s

中文:
引理 disjoint_disjiUnion_right
  证明: by
  simpa only [_root_.disjoint_comm] using disjoint_disjiUnion_left t f hf s

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, disjoint_disjiUnion_left
-/
lemma disjoint_disjiUnion_right
    (s : Finset β) (t : Finset α) (f : α -> Finset β) (hf : Set.PairwiseDisjoint t f) :
    Disjoint s (t.disjiUnion f hf) ↔ forall i in t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_disjiUnion_left t f hf s

/--
theorem `pairwiseDisjoint_disjUnion` / 定理 `pairwiseDisjoint_disjUnion`

English:
theorem pairwiseDisjoint_disjUnion
  statement: {f g : α -> Finset β}
  proof: by
  intros i hi j hj hij
  simp [hf hi hj hij, hg hi hj hij, hfg' hi hj hij, (hfg' hj hi hij.symm).symm]

中文:
定理 pairwiseDisjoint_disjUnion
  结论: {f g : α -> 有限集 β}
  证明: by
  intros i hi j hj hij
  simp [hf hi hj hij, hg hi hj hij, hfg' hi hj hij, (hfg' hj hi hij.symm).symm]

Depends on / 依赖: hij.symm, intros
-/
theorem pairwiseDisjoint_disjUnion {f g : α -> Finset β}
    (hfg : forall a, Disjoint (f a) (g a))
    (hfg' : Set.Pairwise s fun a₁ a₂ => Disjoint (f a₁) (g a₂))
    (hf : Set.PairwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) :
    Set.PairwiseDisjoint s (fun a => (f a).disjUnion (g a) (hfg a)) := by
  intros i hi j hj hij
  simp [hf hi hj hij, hg hi hj hij, hfg' hi hj hij, (hfg' hj hi hij.symm).symm]

/--
theorem `disjiUnion_disjUnion` / 定理 `disjiUnion_disjUnion`

English:
theorem disjiUnion_disjUnion
  statement: {f g : α -> Finset β} (hfg : forall a, Disjoint (f a) (g a))
  proof: by
  grind

中文:
定理 disjiUnion_disjUnion
  结论: {f g : α -> 有限集 β} (hfg : 对任意 a, Disjoint (f a) (g a))
  证明: by
  grind
-/
theorem disjiUnion_disjUnion {f g : α -> Finset β} (hfg : forall a, Disjoint (f a) (g a))
    (hfg' : Set.Pairwise s fun a₁ a₂ => Disjoint (f a₁) (g a₂))
    (hf : Set.PairwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) :
    s.disjiUnion (fun a => (f a).disjUnion (g a) (hfg a))
        (pairwiseDisjoint_disjUnion hfg hfg' hf hg) =
      (s.disjiUnion f hf).disjUnion (s.disjiUnion g hg) (by
        simp_rw [disjoint_disjiUnion_left, disjoint_disjiUnion_right]
        intros i hi j hj
        specialize hfg' hi hj
        grind) := by
  grind

end DisjiUnion

section BUnion
variable [DecidableEq β]

/--
Definition of `biUnion` / `biUnion` 的定义

English:
definition biUnion
  signature: (s : Finset α) (t : α -> Finset β)
  body: (s.1.bind fun a => (t a).1).toFinset

中文:
定义 biUnion
  签名: (s : 有限集 α) (t : α -> 有限集 β)
  定义体: (s.1.bind fun a => (t a).1).toFinset

Depends on / 依赖: wRec_eq
-/
protected def biUnion (s : Finset α) (t : α -> Finset β) : Finset β :=
  (s.1.bind fun a => (t a).1).toFinset

/--
lemma `biUnion_val` / 引理 `biUnion_val`

English:
lemma biUnion_val
  given: (s : Finset α) (t : α -> Finset β)
  proof: rfl

中文:
引理 biUnion_val
  条件: (s : 有限集 α) (t : α -> 有限集 β)
  证明: rfl

Depends on / 依赖: _wMk, split_dropFun_lastFun
-/
@[simp] lemma biUnion_val (s : Finset α) (t : α -> Finset β) :
    (s.biUnion t).1 = (s.1.bind fun a => (t a).1).dedup := rfl

/--
lemma `biUnion_empty` / 引理 `biUnion_empty`

English:
lemma biUnion_empty
  statement: Finset.biUnion ∅ t = ∅
  proof: rfl

中文:
引理 biUnion_empty
  结论: 有限集.biUnion ∅ t = ∅
  证明: rfl
-/
@[simp] lemma biUnion_empty : Finset.biUnion ∅ t = ∅ := rfl

/--
lemma `mem_biUnion` / 引理 `mem_biUnion`

English:
lemma mem_biUnion
  given: {b : β}
  statement: b in s.biUnion t ↔ exists a in s, b in t a
  proof: by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind]

@[simp, norm_cast]

中文:
引理 mem_biUnion
  条件: {b : β}
  结论: b in s.biUnion t ↔ 存在 a in s, b in t a
  证明: by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind]

@[simp, norm_cast]
-/
@[simp, grind =] lemma mem_biUnion {b : β} : b in s.biUnion t ↔ exists a in s, b in t a := by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind]

@[simp, norm_cast]
/--
lemma `coe_biUnion` / 引理 `coe_biUnion`

English:
lemma coe_biUnion
  statement: (s.biUnion t : Set β) = ⋃ x in (s : Set α), t x
  proof: by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion]

@[simp]

中文:
引理 coe_biUnion
  结论: (s.biUnion t : 集合 β) = ⋃ x in (s : 集合 α), t x
  证明: by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion]

@[simp]

Depends on / 依赖: Set.ext_iff, Set.mem_iUnion, ext_iff, mem_biUnion, mem_iUnion
-/
lemma coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Set α), t x := by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion]

@[simp]
/--
lemma `biUnion_insert` / 引理 `biUnion_insert`

English:
lemma biUnion_insert
  given: [DecidableEq α] {a : α}
  statement: (insert a s).biUnion t = t a union s.biUnion t
  proof: by
  aesop

中文:
引理 biUnion_insert
  条件: [DecidableEq α] {a : α}
  结论: (insert a s).biUnion t = t a union s.biUnion t
  证明: by
  aesop
-/
lemma biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a union s.biUnion t := by
  aesop

/--
lemma `biUnion_congr` / 引理 `biUnion_congr`

English:
lemma biUnion_congr
  given: (hs : s₁ = s₂) (ht : forall a in s₁, t₁ a = t₂ a)
  proof: by
  grind

@[simp]

中文:
引理 biUnion_congr
  条件: (hs : s₁ = s₂) (ht : 对任意 a in s₁, t₁ a = t₂ a)
  证明: by
  grind

@[simp]
-/
lemma biUnion_congr (hs : s₁ = s₂) (ht : forall a in s₁, t₁ a = t₂ a) :
    s₁.biUnion t₁ = s₂.biUnion t₂ := by
  grind

@[simp]
/--
lemma `disjiUnion_eq_biUnion` / 引理 `disjiUnion_eq_biUnion`

English:
lemma disjiUnion_eq_biUnion
  given: (s : Finset α) (f : α -> Finset β) (hf)
  proof: eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm

中文:
引理 disjiUnion_eq_biUnion
  条件: (s : 有限集 α) (f : α -> 有限集 β) (hf)
  证明: eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm

Depends on / 依赖: disjiUnion, eq_of_veq, nodup.dedup.symm, s.disjiUnion
-/
lemma disjiUnion_eq_biUnion (s : Finset α) (f : α -> Finset β) (hf) :
    s.disjiUnion f hf = s.biUnion f := eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm

/--
lemma `biUnion_subset` / 引理 `biUnion_subset`

English:
lemma biUnion_subset
  given: {s' : Finset β}
  statement: s.biUnion t subseteq s' ↔ forall x in s, t x subseteq s'
  proof: by grind

@[simp]

中文:
引理 biUnion_subset
  条件: {s' : 有限集 β}
  结论: s.biUnion t subseteq s' ↔ 对任意 x in s, t x subseteq s'
  证明: by grind

@[simp]
-/
lemma biUnion_subset {s' : Finset β} : s.biUnion t subseteq s' ↔ forall x in s, t x subseteq s' := by grind

@[simp]
/--
lemma `singleton_biUnion` / 引理 `singleton_biUnion`

English:
lemma singleton_biUnion
  given: {a : α}
  statement: Finset.biUnion {a} t = t a
  proof: by grind

中文:
引理 singleton_biUnion
  条件: {a : α}
  结论: 有限集.biUnion {a} t = t a
  证明: by grind
-/
lemma singleton_biUnion {a : α} : Finset.biUnion {a} t = t a := by grind

/--
lemma `biUnion_inter` / 引理 `biUnion_inter`

English:
lemma biUnion_inter
  given: (s : Finset α) (f : α -> Finset β) (t : Finset β)
  proof: by grind

中文:
引理 biUnion_inter
  条件: (s : 有限集 α) (f : α -> 有限集 β) (t : 有限集 β)
  证明: by grind
-/
lemma biUnion_inter (s : Finset α) (f : α -> Finset β) (t : Finset β) :
    s.biUnion f inter t = s.biUnion fun x => f x inter t := by grind

/--
lemma `inter_biUnion` / 引理 `inter_biUnion`

English:
lemma inter_biUnion
  given: (t : Finset β) (s : Finset α) (f : α -> Finset β)
  proof: by grind

中文:
引理 inter_biUnion
  条件: (t : 有限集 β) (s : 有限集 α) (f : α -> 有限集 β)
  证明: by grind
-/
lemma inter_biUnion (t : Finset β) (s : Finset α) (f : α -> Finset β) :
    t inter s.biUnion f = s.biUnion fun x => t inter f x := by grind

/--
lemma `biUnion_biUnion` / 引理 `biUnion_biUnion`

English:
lemma biUnion_biUnion
  given: [DecidableEq γ] (s : Finset α) (f : α -> Finset β) (g : β -> Finset γ)
  proof: by grind

中文:
引理 biUnion_biUnion
  条件: [DecidableEq γ] (s : 有限集 α) (f : α -> 有限集 β) (g : β -> 有限集 γ)
  证明: by grind
-/
lemma biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α -> Finset β) (g : β -> Finset γ) :
    (s.biUnion f).biUnion g = s.biUnion fun a => (f a).biUnion g := by grind

/--
lemma `bind_toFinset` / 引理 `bind_toFinset`

English:
lemma bind_toFinset
  given: [DecidableEq α] (s : Multiset α) (t : α -> Multiset β)
  proof: ext fun x => by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind]

中文:
引理 bind_toFinset
  条件: [DecidableEq α] (s : Multiset α) (t : α -> Multiset β)
  证明: ext fun x => by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind]

Depends on / 依赖: Multiset, Multiset.mem_bind, Multiset.mem_toFinset, mem_biUnion, mem_bind, mem_toFinset
-/
lemma bind_toFinset [DecidableEq α] (s : Multiset α) (t : α -> Multiset β) :
    (s.bind t).toFinset = s.toFinset.biUnion fun a => (t a).toFinset :=
  ext fun x => by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind]

/--
lemma `biUnion_mono` / 引理 `biUnion_mono`

English:
lemma biUnion_mono
  given: (h : forall a in s, t₁ a subseteq t₂ a)
  statement: s.biUnion t₁ subseteq s.biUnion t₂
  proof: by grind

@[gcongr]

中文:
引理 biUnion_mono
  条件: (h : 对任意 a in s, t₁ a subseteq t₂ a)
  结论: s.biUnion t₁ subseteq s.biUnion t₂
  证明: by grind

@[gcongr]
-/
lemma biUnion_mono (h : forall a in s, t₁ a subseteq t₂ a) : s.biUnion t₁ subseteq s.biUnion t₂ := by grind

@[gcongr]
/--
lemma `biUnion_subset_biUnion_of_subset_left` / 引理 `biUnion_subset_biUnion_of_subset_left`

English:
lemma biUnion_subset_biUnion_of_subset_left
  given: (t : α -> Finset β) (h : s₁ subseteq s₂)
  proof: by grind

中文:
引理 biUnion_subset_biUnion_of_subset_left
  条件: (t : α -> 有限集 β) (h : s₁ subseteq s₂)
  证明: by grind
-/
lemma biUnion_subset_biUnion_of_subset_left (t : α -> Finset β) (h : s₁ subseteq s₂) :
    s₁.biUnion t subseteq s₂.biUnion t := by grind

/--
lemma `subset_biUnion_of_mem` / 引理 `subset_biUnion_of_mem`

English:
lemma subset_biUnion_of_mem
  given: (u : α -> Finset β) {x : α} (xs : x in s)
  statement: u x subseteq s.biUnion u
  proof: by grind

@[simp]

中文:
引理 subset_biUnion_of_mem
  条件: (u : α -> 有限集 β) {x : α} (xs : x in s)
  结论: u x subseteq s.biUnion u
  证明: by grind

@[simp]
-/
lemma subset_biUnion_of_mem (u : α -> Finset β) {x : α} (xs : x in s) : u x subseteq s.biUnion u := by grind

@[simp]
/--
lemma `biUnion_subset_iff_forall_subset` / 引理 `biUnion_subset_iff_forall_subset`

English:
lemma biUnion_subset_iff_forall_subset
  statement: {α β : Type*} [DecidableEq β] {s : Finset α}
  proof: by grind

@[simp]

中文:
引理 biUnion_subset_iff_对任意_subset
  结论: {α β : 类型} [DecidableEq β] {s : 有限集 α}
  证明: by grind

@[simp]
-/
lemma biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α -> Finset β} : s.biUnion f subseteq t ↔ forall x in s, f x subseteq t := by grind

@[simp]
/--
lemma `biUnion_singleton_eq_self` / 引理 `biUnion_singleton_eq_self`

English:
lemma biUnion_singleton_eq_self
  given: [DecidableEq α]
  statement: s.biUnion (singleton : α -> Finset α) = s
  proof: by
  grind

中文:
引理 biUnion_singleton_eq_self
  条件: [DecidableEq α]
  结论: s.biUnion (singleton : α -> 有限集 α) = s
  证明: by
  grind
-/
lemma biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α -> Finset α) = s := by
  grind

/--
lemma `filter_biUnion` / 引理 `filter_biUnion`

English:
lemma filter_biUnion
  given: (s : Finset α) (f : α -> Finset β) (p : β -> Prop) [DecidablePred p]
  proof: by grind

中文:
引理 filter_biUnion
  条件: (s : 有限集 α) (f : α -> 有限集 β) (p : β -> 命题) [DecidablePred p]
  证明: by grind

Depends on / 依赖: Sigma.fst
-/
lemma filter_biUnion (s : Finset α) (f : α -> Finset β) (p : β -> Prop) [DecidablePred p] :
    (s.biUnion f).filter p = s.biUnion fun a => (f a).filter p := by grind

/--
lemma `biUnion_filter_eq_of_maps_to` / 引理 `biUnion_filter_eq_of_maps_to`

English:
lemma biUnion_filter_eq_of_maps_to
  statement: [DecidableEq α] {s : Finset α} {t : Finset β} {f : α -> β}
  proof: by grind

中文:
引理 biUnion_filter_eq_of_maps_to
  结论: [DecidableEq α] {s : 有限集 α} {t : 有限集 β} {f : α -> β}
  证明: by grind
-/
lemma biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α -> β}
    (h : forall x in s, f x in t) : (t.biUnion fun a => s.filter fun c => f c = a) = s := by grind

/--
lemma `erase_biUnion` / 引理 `erase_biUnion`

English:
lemma erase_biUnion
  given: (f : α -> Finset β) (s : Finset α) (b : β)
  proof: by grind

@[simp]

中文:
引理 erase_biUnion
  条件: (f : α -> 有限集 β) (s : 有限集 α) (b : β)
  证明: by grind

@[simp]
-/
lemma erase_biUnion (f : α -> Finset β) (s : Finset α) (b : β) :
    (s.biUnion f).erase b = s.biUnion fun x => (f x).erase b := by grind

@[simp]
/--
lemma `biUnion_nonempty` / 引理 `biUnion_nonempty`

English:
lemma biUnion_nonempty
  statement: (s.biUnion t).Nonempty ↔ exists x in s, (t x).Nonempty
  proof: by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_comm]
  simp [exists_and_left]

中文:
引理 biUnion_nonempty
  结论: (s.biUnion t).非空 ↔ 存在 x in s, (t x).非空
  证明: by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_comm]
  simp [exists_and_left]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, exists_and_left, exists_comm, mem_biUnion
-/
lemma biUnion_nonempty : (s.biUnion t).Nonempty ↔ exists x in s, (t x).Nonempty := by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_comm]
  simp [exists_and_left]

/--
lemma `Nonempty.biUnion` / 引理 `Nonempty.biUnion`

English:
lemma Nonempty.biUnion
  given: (hs : s.Nonempty) (ht : forall x in s, (t x).Nonempty)
  proof: biUnion_nonempty.2 hs.imp fun x hx => ⟨hx, ht x hx⟩

中文:
引理 非空.biUnion
  条件: (hs : s.非空) (ht : 对任意 x in s, (t x).非空)
  证明: biUnion_nonempty.2 hs.imp fun x hx => ⟨hx, ht x hx⟩

Depends on / 依赖: biUnion_nonempty, hs.imp
-/
lemma Nonempty.biUnion (hs : s.Nonempty) (ht : forall x in s, (t x).Nonempty) :
(s.biUnion t).Nonempty := biUnion_nonempty.2 hs.imp fun x hx => ⟨hx, ht x hx⟩

/--
lemma `disjoint_biUnion_left` / 引理 `disjoint_biUnion_left`

English:
lemma disjoint_biUnion_left
  given: (s : Finset α) (f : α -> Finset β) (t : Finset β)
  proof: by
  classical
  refine s.induction ?_ ?_
  · simp
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, forall_mem_insert, ih]

中文:
引理 disjoint_biUnion_left
  条件: (s : 有限集 α) (f : α -> 有限集 β) (t : 有限集 β)
  证明: by
  classical
  refine s.induction ?_ ?_
  · simp
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, forall_mem_insert, ih]

Depends on / 依赖: biUnion_insert, classical, disjoint_union_left, forall_mem_insert, s.induction
-/
lemma disjoint_biUnion_left (s : Finset α) (f : α -> Finset β) (t : Finset β) :
    Disjoint (s.biUnion f) t ↔ forall i in s, Disjoint (f i) t := by
  classical
  refine s.induction ?_ ?_
  · simp
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, forall_mem_insert, ih]

/--
lemma `disjoint_biUnion_right` / 引理 `disjoint_biUnion_right`

English:
lemma disjoint_biUnion_right
  given: (s : Finset β) (t : Finset α) (f : α -> Finset β)
  proof: by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s

中文:
引理 disjoint_biUnion_right
  条件: (s : 有限集 β) (t : 有限集 α) (f : α -> 有限集 β)
  证明: by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_biUnion_left, disjoint_comm
-/
lemma disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α -> Finset β) :
    Disjoint s (t.biUnion f) ↔ forall i in t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s

/--
theorem `image_biUnion` / 定理 `image_biUnion`

English:
theorem image_biUnion
  given: [DecidableEq γ] {f : α -> β} {s : Finset α} {t : β -> Finset γ}
  proof: haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]

中文:
定理 image_biUnion
  条件: [DecidableEq γ] {f : α -> β} {s : 有限集 α} {t : β -> 有限集 γ}
  证明: haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, biUnion_insert, image_insert, induction_on
-/
theorem image_biUnion [DecidableEq γ] {f : α -> β} {s : Finset α} {t : β -> Finset γ} :
    (s.image f).biUnion t = s.biUnion fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]

/--
theorem `biUnion_image` / 定理 `biUnion_image`

English:
theorem biUnion_image
  given: [DecidableEq γ] {s : Finset α} {t : α -> Finset β} {f : β -> γ}
  proof: haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]

中文:
定理 biUnion_image
  条件: [DecidableEq γ] {s : 有限集 α} {t : α -> 有限集 β} {f : β -> γ}
  证明: haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, biUnion_insert, image_union, induction_on
-/
theorem biUnion_image [DecidableEq γ] {s : Finset α} {t : α -> Finset β} {f : β -> γ} :
    (s.biUnion t).image f = s.biUnion fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]

/--
theorem `image_biUnion_filter_eq` / 定理 `image_biUnion_filter_eq`

English:
theorem image_biUnion_filter_eq
  given: [DecidableEq α] (s : Finset β) (g : β -> α)
  proof: biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g

中文:
定理 image_biUnion_filter_eq
  条件: [DecidableEq α] (s : 有限集 β) (g : β -> α)
  证明: biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g

Depends on / 依赖: biUnion_filter_eq_of_maps_to, mem_image_of_mem
-/
theorem image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β -> α) :
    ((s.image g).biUnion fun a => s.filter fun c => g c = a) = s :=
  biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g

/--
lemma `union_biUnion` / 引理 `union_biUnion`

English:
lemma union_biUnion
  given: [DecidableEq α]
  statement: (s₁ union s₂).biUnion t = s₁.biUnion t union s₂.biUnion t
  proof: by
  grind

中文:
引理 union_biUnion
  条件: [DecidableEq α]
  结论: (s₁ union s₂).biUnion t = s₁.biUnion t union s₂.biUnion t
  证明: by
  grind
-/
lemma union_biUnion [DecidableEq α] : (s₁ union s₂).biUnion t = s₁.biUnion t union s₂.biUnion t := by
  grind

/--
lemma `biUnion_union` / 引理 `biUnion_union`

English:
lemma biUnion_union
  statement: s.biUnion (fun x => t₁ x union t₂ x) = s.biUnion t₁ union s.biUnion t₂
  proof: by grind

中文:
引理 biUnion_union
  结论: s.biUnion (fun x => t₁ x union t₂ x) = s.biUnion t₁ union s.biUnion t₂
  证明: by grind
-/
lemma biUnion_union : s.biUnion (fun x => t₁ x union t₂ x) = s.biUnion t₁ union s.biUnion t₂ := by grind

/--
theorem `biUnion_singleton` / 定理 `biUnion_singleton`

English:
theorem biUnion_singleton
  given: {f : α -> β}
  statement: (s.biUnion fun a => {f a}) = s.image f
  proof: by grind

中文:
定理 biUnion_singleton
  条件: {f : α -> β}
  结论: (s.biUnion fun a => {f a}) = s.像 f
  证明: by grind
-/
theorem biUnion_singleton {f : α -> β} : (s.biUnion fun a => {f a}) = s.image f := by grind

/--
lemma `attach_biUnion` / 引理 `attach_biUnion`

English:
lemma attach_biUnion
  given: {f : α -> Finset β}
  statement: s.attach.biUnion (f ·) = s.biUnion f
  proof: by aesop

中文:
引理 attach_biUnion
  条件: {f : α -> 有限集 β}
  结论: s.attach.biUnion (f ·) = s.biUnion f
  证明: by aesop
-/
lemma attach_biUnion {f : α -> Finset β} : s.attach.biUnion (f ·) = s.biUnion f := by aesop

/--
lemma `attach_biUnion'` / 引理 `attach_biUnion'`

English:
lemma attach_biUnion'
  given: [DecidableEq α] {f : s -> Finset β}
  proof: by aesop

中文:
引理 attach_biUnion'
  条件: [DecidableEq α] {f : s -> 有限集 β}
  证明: by aesop
-/
lemma attach_biUnion' [DecidableEq α] {f : s -> Finset β} :
    s.attach.biUnion f = s.biUnion fun a => if h : a in s then f ⟨a, h⟩ else ∅ := by aesop

end BUnion
end Finset
