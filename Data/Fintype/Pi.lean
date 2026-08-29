/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Fintype instances for pi types
-/

@[expose] public section

assert_not_exists IsOrderedRing MonoidWithZero

open Finset Function

variable {α β : Type*}

namespace Fintype

variable [DecidableEq α] [Fintype α] {γ δ : α -> Type*} {s : forall a, Finset (γ a)}

/--
Definition of `piFinset` / `piFinset` 的定义

English:
definition piFinset
  signature: (t : forall a, Finset (δ a))
  body: (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp, grind =]

中文:
定义 piFinset
  签名: (t : 对任意 a, Finset (δ a))
  定义体: (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp, grind =]

Depends on / 依赖: Finset, Finset.univ.pi, contextual, funext_iff, mem_univ
-/
def piFinset (t : forall a, Finset (δ a)) : Finset (forall a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp, grind =]
/--
theorem `mem_piFinset` / 定理 `mem_piFinset`

English:
theorem mem_piFinset
  given: {t : forall a, Finset (δ a)} {f : forall a, δ a}
  statement: f in piFinset t ↔ forall a, f a in t a
  proof: by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

@[simp]

中文:
定理 mem_piFinset
  条件: {t : 对任意 a, Finset (δ a)} {f : 对任意 a, δ a}
  结论: f in piFinset t ↔ 对任意 a, f a in t a
  证明: by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

@[simp]

Depends on / 依赖: and_imp, exists_imp, forall_prop_of_true, mem_map, mem_pi, mem_univ, piFinset
-/
theorem mem_piFinset {t : forall a, Finset (δ a)} {f : forall a, δ a} : f in piFinset t ↔ forall a, f a in t a := by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

@[simp]
/--
theorem `coe_piFinset` / 定理 `coe_piFinset`

English:
theorem coe_piFinset
  given: (t : forall a, Finset (δ a))
  proof: Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset

中文:
定理 coe_piFinset
  条件: (t : 对任意 a, Finset (δ a))
  证明: Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset

Depends on / 依赖: Fintype, Fintype.mem_piFinset, Set.ext, Set.mem_univ_pi, mem_piFinset, mem_univ_pi
-/
theorem coe_piFinset (t : forall a, Finset (δ a)) :
    (piFinset t : Set (forall a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset

/--
theorem `piFinset_subset` / 定理 `piFinset_subset`

English:
theorem piFinset_subset
  given: (t₁ t₂ : forall a, Finset (δ a)) (h : forall a, t₁ a subseteq t₂ a)
  proof: fun _ hg => mem_piFinset.2 fun a => h a mem_piFinset.1 hg a

@[simp]

中文:
定理 piFinset_subset
  条件: (t₁ t₂ : 对任意 a, Finset (δ a)) (h : 对任意 a, t₁ a subseteq t₂ a)
  证明: fun _ hg => mem_piFinset.2 fun a => h a mem_piFinset.1 hg a

@[simp]

Depends on / 依赖: mem_piFinset
-/
theorem piFinset_subset (t₁ t₂ : forall a, Finset (δ a)) (h : forall a, t₁ a subseteq t₂ a) :
piFinset t₁ subseteq piFinset t₂ := fun _ hg => mem_piFinset.2 fun a => h a mem_piFinset.1 hg a

@[simp]
/--
theorem `piFinset_eq_empty` / 定理 `piFinset_eq_empty`

English:
theorem piFinset_eq_empty
  statement: piFinset s = ∅ ↔ exists i, s i = ∅
  proof: by simp [piFinset]

@[simp]

中文:
定理 piFinset_eq_empty
  结论: piFinset s = ∅ ↔ 存在 i, s i = ∅
  证明: by simp [piFinset]

@[simp]

Depends on / 依赖: piFinset
-/
theorem piFinset_eq_empty : piFinset s = ∅ ↔ exists i, s i = ∅ := by simp [piFinset]

@[simp]
/--
theorem `piFinset_empty` / 定理 `piFinset_empty`

English:
theorem piFinset_empty
  given: [Nonempty α]
  statement: piFinset (fun _ => ∅ : forall i, Finset (δ i)) = ∅
  proof: by simp

@[simp]

中文:
定理 piFinset_empty
  条件: [Nonempty α]
  结论: piFinset (fun _ => ∅ : 对任意 i, Finset (δ i)) = ∅
  证明: by simp

@[simp]
-/
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : forall i, Finset (δ i)) = ∅ := by simp

@[simp]
/--
lemma `piFinset_nonempty` / 引理 `piFinset_nonempty`

English:
lemma piFinset_nonempty
  statement: (piFinset s).Nonempty ↔ forall a, (s a).Nonempty
  proof: by simp [piFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.piFinset_nonempty_of_forall_nonempty⟩ := piFinset_nonempty

中文:
引理 piFinset_nonempty
  结论: (piFinset s).Nonempty ↔ 对任意 a, (s a).Nonempty
  证明: by simp [piFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.piFinset_nonempty_of_forall_nonempty⟩ := piFinset_nonempty

Depends on / 依赖: piFinset
-/
lemma piFinset_nonempty : (piFinset s).Nonempty ↔ forall a, (s a).Nonempty := by simp [piFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.piFinset_nonempty_of_forall_nonempty⟩ := piFinset_nonempty

/--
lemma `_root_.Finset.Nonempty.piFinset_const` / 引理 `_root_.Finset.Nonempty.piFinset_const`

English:
lemma _root_.Finset.Nonempty.piFinset_const
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Finset β}
  proof: piFinset_nonempty.2 fun _ => hs

@[simp]

中文:
引理 _root_.Finset.Nonempty.piFinset_const
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι] {s : Finset β}
  证明: piFinset_nonempty.2 fun _ => hs

@[simp]

Depends on / 依赖: piFinset_nonempty
-/
lemma _root_.Finset.Nonempty.piFinset_const {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Finset β}
    (hs : s.Nonempty) : (piFinset fun _ : ι => s).Nonempty := piFinset_nonempty.2 fun _ => hs

@[simp]
/--
lemma `piFinset_of_isEmpty` / 引理 `piFinset_of_isEmpty`

English:
lemma piFinset_of_isEmpty
  given: [IsEmpty α] (s : forall a, Finset (γ a))
  statement: piFinset s = univ
  proof: eq_univ_of_forall fun _ => by simp

@[simp]

中文:
引理 piFinset_of_isEmpty
  条件: [IsEmpty α] (s : 对任意 a, Finset (γ a))
  结论: piFinset s = univ
  证明: eq_univ_of_forall fun _ => by simp

@[simp]

Depends on / 依赖: eq_univ_of_forall
-/
lemma piFinset_of_isEmpty [IsEmpty α] (s : forall a, Finset (γ a)) : piFinset s = univ :=
  eq_univ_of_forall fun _ => by simp

@[simp]
/--
theorem `piFinset_singleton` / 定理 `piFinset_singleton`

English:
theorem piFinset_singleton
  given: (f : forall i, δ i)
  statement: piFinset (fun i => {f i} : forall i, Finset (δ i)) = {f}
  proof: ext fun _ => by grind

中文:
定理 piFinset_singleton
  条件: (f : 对任意 i, δ i)
  结论: piFinset (fun i => {f i} : 对任意 i, Finset (δ i)) = {f}
  证明: ext fun _ => by grind
-/
theorem piFinset_singleton (f : forall i, δ i) : piFinset (fun i => {f i} : forall i, Finset (δ i)) = {f} :=
  ext fun _ => by grind

/--
theorem `piFinset_subsingleton` / 定理 `piFinset_subsingleton`

English:
theorem piFinset_subsingleton
  given: {f : forall i, Finset (δ i)} (hf : forall i, (f i : Set (δ i)).Subsingleton)
  proof: fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)

中文:
定理 piFinset_subsingleton
  条件: {f : 对任意 i, Finset (δ i)} (hf : 对任意 i, (f i : Set (δ i)).Subsingleton)
  证明: fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)
-/
theorem piFinset_subsingleton {f : forall i, Finset (δ i)} (hf : forall i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (forall i, δ i)).Subsingleton := fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)

/--
theorem `piFinset_disjoint_of_disjoint` / 定理 `piFinset_disjoint_of_disjoint`

English:
theorem piFinset_disjoint_of_disjoint
  statement: (t₁ t₂ : forall a, Finset (δ a)) {a : α}
  proof: disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)

中文:
定理 piFinset_disjoint_of_disjoint
  结论: (t₁ t₂ : 对任意 a, Finset (δ a)) {a : α}
  证明: disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)

Depends on / 依赖: congr_fun, disjoint_iff_ne, mem_piFinset
-/
theorem piFinset_disjoint_of_disjoint (t₁ t₂ : forall a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)

/--
lemma `piFinset_image` / 引理 `piFinset_image`

English:
lemma piFinset_image
  given: [forall a, DecidableEq (δ a)] (f : forall a, γ a -> δ a) (s : forall a, Finset (γ a))
  proof: by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, funext_iff]

中文:
引理 piFinset_image
  条件: [对任意 a, DecidableEq (δ a)] (f : 对任意 a, γ a -> δ a) (s : 对任意 a, Finset (γ a))
  证明: by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, funext_iff]

Depends on / 依赖: Classical, Classical.skolem, forall_and, funext_iff, mem_image, mem_piFinset, skolem
-/
lemma piFinset_image [forall a, DecidableEq (δ a)] (f : forall a, γ a -> δ a) (s : forall a, Finset (γ a)) :
    piFinset (fun a => (s a).image (f a)) = (piFinset s).image fun b a => f _ (b a) := by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, funext_iff]

/--
lemma `eval_image_piFinset_subset` / 引理 `eval_image_piFinset_subset`

English:
lemma eval_image_piFinset_subset
  given: (t : forall a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
  proof: image_subset_iff.2 fun _x hx => mem_piFinset.1 hx _

中文:
引理 eval_image_piFinset_subset
  条件: (t : 对任意 a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
  证明: image_subset_iff.2 fun _x hx => mem_piFinset.1 hx _

Depends on / 依赖: Function, Function.update, h_if, image_subset_iff, mem_piFinset, split_ifs, update
-/
lemma eval_image_piFinset_subset (t : forall a, Finset (δ a)) (a : α) [DecidableEq (δ a)] :
    ((piFinset t).image fun f => f a) subseteq t a := image_subset_iff.2 fun _x hx => mem_piFinset.1 hx _

/--
lemma `eval_image_piFinset` / 引理 `eval_image_piFinset`

English:
lemma eval_image_piFinset
  statement: (t : forall a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
  proof: by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h => mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b => if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩

中文:
引理 eval_image_piFinset
  结论: (t : 对任意 a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
  证明: by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h => mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b => if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩

Depends on / 依赖: antisymm, eval_image_piFinset_subset, mem_image
-/
lemma eval_image_piFinset (t : forall a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : forall b, a != b -> (t b).Nonempty) : ((piFinset t).image fun f => f a) = t a := by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h => mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b => if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩

/--
lemma `eval_image_piFinset_const` / 引理 `eval_image_piFinset_const`

English:
lemma eval_image_piFinset_const
  given: {β} [DecidableEq β] (t : Finset β) (a : α)
  proof: by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · have : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ => t) a fun _ _ => ht

中文:
引理 eval_image_piFinset_const
  条件: {β} [DecidableEq β] (t : Finset β) (a : α)
  证明: by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · have : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ => t) a fun _ _ => ht

Depends on / 依赖: Nonempty, eq_empty_or_nonempty, eval_image_piFinset, t.eq_empty_or_nonempty
-/
lemma eval_image_piFinset_const {β} [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset fun _i : α => t).image fun f => f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · have : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ => t) a fun _ _ => ht

variable [forall a, DecidableEq (δ a)]

/--
lemma `piFinset_inter` / 引理 `piFinset_inter`

English:
lemma piFinset_inter
  given: (s t : forall a, Finset (δ a))
  proof: by
  grind

中文:
引理 piFinset_inter
  条件: (s t : 对任意 a, Finset (δ a))
  证明: by
  grind
-/
lemma piFinset_inter (s t : forall a, Finset (δ a)) :
    piFinset (fun i => s i inter t i) = piFinset s inter piFinset t := by
  grind

/--
lemma `filter_piFinset_of_notMem` / 引理 `filter_piFinset_of_notMem`

English:
lemma filter_piFinset_of_notMem
  given: (t : forall a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a)
  proof: by
  grind

中文:
引理 filter_piFinset_of_notMem
  条件: (t : 对任意 a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a)
  证明: by
  grind
-/
lemma filter_piFinset_of_notMem (t : forall a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) :
    {f in piFinset t | f a = x} = ∅ := by
  grind

/--
lemma `piFinset_update_eq_filter_piFinset_mem` / 引理 `piFinset_update_eq_filter_piFinset_mem`

English:
lemma piFinset_update_eq_filter_piFinset_mem
  statement: (s : forall i, Finset (δ i)) (i : α) {t : Finset (δ i)}
  proof: by
  grind

中文:
引理 piFinset_update_eq_filter_piFinset_mem
  结论: (s : 对任意 i, Finset (δ i)) (i : α) {t : Finset (δ i)}
  证明: by
  grind
-/
lemma piFinset_update_eq_filter_piFinset_mem (s : forall i, Finset (δ i)) (i : α) {t : Finset (δ i)}
    (hts : t subseteq s i) : piFinset (Function.update s i t) = {f in piFinset s | f i in t} := by
  grind

/--
lemma `piFinset_update_singleton_eq_filter_piFinset_eq` / 引理 `piFinset_update_singleton_eq_filter_piFinset_eq`

English:
lemma piFinset_update_singleton_eq_filter_piFinset_eq
  statement: (s : forall i, Finset (δ i)) (i : α) {a : δ i}
  proof: by
  grind

中文:
引理 piFinset_update_singleton_eq_filter_piFinset_eq
  结论: (s : 对任意 i, Finset (δ i)) (i : α) {a : δ i}
  证明: by
  grind
-/
lemma piFinset_update_singleton_eq_filter_piFinset_eq (s : forall i, Finset (δ i)) (i : α) {a : δ i}
    (ha : a in s i) :
    piFinset (Function.update s i {a}) = {f in piFinset s | f i = a} := by
  grind

end Fintype

/-! ### pi -/

/--
Instance `Pi.instFintype` / 实例 `Pi.instFintype`

English:
instance Pi.instFintype
  signature: {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
  body: ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]

中文:
实例 Pi.instFintype
  签名: {α : 类型} {β : α -> 类型} [DecidableEq α] [Fintype α]
  定义体: ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]

Depends on / 依赖: Fintype, Fintype.piFinset, Option.ne_none_iff_exists, h_not_terminated, ne_none_iff_exists, piFinset, update
-/
instance Pi.instFintype {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
    [forall a, Fintype (β a)] : Fintype (forall a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]
/--
theorem `Fintype.piFinset_univ` / 定理 `Fintype.piFinset_univ`

English:
theorem Fintype.piFinset_univ
  statement: {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
  proof: rfl

中文:
定理 Fintype.piFinset_univ
  结论: {α : 类型} {β : α -> 类型} [DecidableEq α] [Fintype α]
  证明: rfl

Depends on / 依赖: _update, h_terminated
-/
theorem Fintype.piFinset_univ {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
    [forall a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (forall a, β a)) :=
  rfl

/--
Instance `_root_.Function.Embedding.fintype` / 实例 `_root_.Function.Embedding.fintype`

English:
instance _root_.Function.Embedding.fintype
  signature: {α β} [Fintype α] [Fintype β]
  body: by
  classical exact Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)

中文:
实例 _root_.Function.Embedding.fintype
  签名: {α β} [Fintype α] [Fintype β]
  定义体: by
  classical exact Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)

Depends on / 依赖: Equiv.subtypeInjectiveEquivEmbedding, Fintype, Fintype.ofEquiv, _update, classical, ofEquiv, subtypeInjectiveEquivEmbedding
-/
noncomputable instance _root_.Function.Embedding.fintype {α β} [Fintype α] [Fintype β] :
    Fintype (α ↪ β) := by
  classical exact Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)

/--
Instance `RelHom.instFintype` / 实例 `RelHom.instFintype`

English:
instance RelHom.instFintype
  signature: {α β} [Fintype α] [Fintype β] [DecidableEq α] {r : α -> α -> Prop}
  body: Fintype.ofEquiv {f : α -> β // forall {x y}, r x y -> s (f x) (f y)} Equiv.mk
    (fun f => ⟨f.1, f.2⟩) (fun f => ⟨f.1, f.2⟩) (fun _ => rfl) (fun _ => rfl)

中文:
实例 RelHom.instFintype
  签名: {α β} [Fintype α] [Fintype β] [DecidableEq α] {r : α -> α -> 命题}
  定义体: Fintype.ofEquiv {f : α -> β // forall {x y}, r x y -> s (f x) (f y)} Equiv.mk
    (fun f => ⟨f.1, f.2⟩) (fun f => ⟨f.1, f.2⟩) (fun _ => rfl) (fun _ => rfl)

Depends on / 依赖: Equiv.mk, Fintype, Fintype.ofEquiv, ofEquiv
-/
instance RelHom.instFintype {α β} [Fintype α] [Fintype β] [DecidableEq α] {r : α -> α -> Prop}
    {s : β -> β -> Prop} [DecidableRel r] [DecidableRel s] : Fintype (r ->r s) :=
Fintype.ofEquiv {f : α -> β // forall {x y}, r x y -> s (f x) (f y)} Equiv.mk
    (fun f => ⟨f.1, f.2⟩) (fun f => ⟨f.1, f.2⟩) (fun _ => rfl) (fun _ => rfl)

/--
Instance `RelEmbedding.instFintype` / 实例 `RelEmbedding.instFintype`

English:
instance RelEmbedding.instFintype
  signature: {α β} [Fintype α] [Fintype β]
  body: Fintype.ofInjective _ RelEmbedding.toEmbedding_injective

@[simp]

中文:
实例 RelEmbedding.instFintype
  签名: {α β} [Fintype α] [Fintype β]
  定义体: Fintype.ofInjective _ RelEmbedding.toEmbedding_injective

@[simp]

Depends on / 依赖: Fintype, Fintype.ofInjective, RelEmbedding, RelEmbedding.toEmbedding_injective, ofInjective, toEmbedding_injective
-/
noncomputable instance RelEmbedding.instFintype {α β} [Fintype α] [Fintype β]
    {r : α -> α -> Prop} {s : β -> β -> Prop} : Fintype (r ↪r s) :=
  Fintype.ofInjective _ RelEmbedding.toEmbedding_injective

@[simp]
/--
theorem `Finset.univ_pi_univ` / 定理 `Finset.univ_pi_univ`

English:
theorem Finset.univ_pi_univ
  statement: {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
  proof: by
  ext; simp

中文:
定理 Finset.univ_pi_univ
  结论: {α : 类型} {β : α -> 类型} [DecidableEq α] [Fintype α]
  证明: by
  ext; simp
-/
theorem Finset.univ_pi_univ {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α]
    [forall a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by
  ext; simp

/-! ### Diagonal -/

namespace Finset
variable {ι : Type*} [DecidableEq (ι -> α)] {s : Finset α} {f : ι -> α}

/--
lemma `piFinset_filter_const` / 引理 `piFinset_filter_const`

English:
lemma piFinset_filter_const
  given: [DecidableEq ι] [Fintype ι]
  proof: by aesop

中文:
引理 piFinset_filter_const
  条件: [DecidableEq ι] [Fintype ι]
  证明: by aesop
-/
lemma piFinset_filter_const [DecidableEq ι] [Fintype ι] :
    {f in Fintype.piFinset fun _ : ι => s | exists a in s, const ι a = f} = s.piDiag ι := by aesop

/--
lemma `piDiag_subset_piFinset` / 引理 `piDiag_subset_piFinset`

English:
lemma piDiag_subset_piFinset
  given: [DecidableEq ι] [Fintype ι]
  proof: by simp [← piFinset_filter_const]

中文:
引理 piDiag_subset_piFinset
  条件: [DecidableEq ι] [Fintype ι]
  证明: by simp [← piFinset_filter_const]

Depends on / 依赖: piFinset_filter_const
-/
lemma piDiag_subset_piFinset [DecidableEq ι] [Fintype ι] :
    s.piDiag ι subseteq Fintype.piFinset fun _ => s := by simp [← piFinset_filter_const]

end Finset

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Pi
variable {ι : Type*} [Finite ι] {κ : ι -> Type*} {t : forall i, Set (κ i)}

/--
theorem `Finite.pi` / 定理 `Finite.pi`

English:
theorem Finite.pi
  given: (ht : forall i, (t i).Finite)
  statement: (pi univ t).Finite
  proof: by
  cases nonempty_fintype ι
  lift t to forall d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

中文:
定理 Finite.pi
  条件: (ht : 对任意 i, (t i).Finite)
  结论: (pi univ t).Finite
  证明: by
  cases nonempty_fintype ι
  lift t to forall d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

Depends on / 依赖: Finset, Finset.finite_toSet, Fintype, Fintype.coe_piFinset, classical, coe_piFinset, finite_toSet, nonempty_fintype
-/
theorem Finite.pi (ht : forall i, (t i).Finite) : (pi univ t).Finite := by
  cases nonempty_fintype ι
  lift t to forall d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

/--
lemma `Finite.pi'` / 引理 `Finite.pi'`

English:
lemma Finite.pi'
  given: (ht : forall i, (t i).Finite)
  statement: {f : forall i, κ i | forall i, f i in t i}.Finite
  proof: by
  simpa [Set.pi] using Finite.pi ht

中文:
引理 Finite.pi'
  条件: (ht : 对任意 i, (t i).Finite)
  结论: {f : 对任意 i, κ i | 对任意 i, f i in t i}.Finite
  证明: by
  simpa [Set.pi] using Finite.pi ht

Depends on / 依赖: Finite, Finite.pi, Set.pi
-/
lemma Finite.pi' (ht : forall i, (t i).Finite) : {f : forall i, κ i | forall i, f i in t i}.Finite := by
  simpa [Set.pi] using Finite.pi ht

end Pi

end SetFiniteConstructors

/--
theorem `forall_finite_image_eval_iff` / 定理 `forall_finite_image_eval_iff`

English:
theorem forall_finite_image_eval_iff
  given: {δ : Type*} [Finite δ] {κ : δ -> Type*} {s : Set (forall d, κ d)}
  proof: ⟨fun h => (Finite.pi h).subset subset_pi_eval_image _ _, fun h _ => h.image _⟩

@[simp]

中文:
定理 forall_finite_image_eval_iff
  条件: {δ : 类型} [Finite δ] {κ : δ -> 类型} {s : Set (对任意 d, κ d)}
  证明: ⟨fun h => (Finite.pi h).subset subset_pi_eval_image _ _, fun h _ => h.image _⟩

@[simp]

Depends on / 依赖: Finite, Finite.pi, h.image, subset, subset_pi_eval_image
-/
theorem forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ -> Type*} {s : Set (forall d, κ d)} :
    (forall d, (eval d '' s).Finite) ↔ s.Finite :=
⟨fun h => (Finite.pi h).subset subset_pi_eval_image _ _, fun h _ => h.image _⟩

@[simp]
/--
lemma `iUnion_cons` / 引理 `iUnion_cons`

English:
lemma iUnion_cons
  given: {n : Nat} (f : Fin n -> Set α) (s : Set α)
  proof: by
  ext
  simp [Fin.exists_iff_succ]

@[simp]

中文:
引理 iUnion_cons
  条件: {n : 自然数} (f : Fin n -> Set α) (s : Set α)
  证明: by
  ext
  simp [Fin.exists_iff_succ]

@[simp]

Depends on / 依赖: Fin.exists_iff_succ, exists_iff_succ
-/
lemma iUnion_cons {n : Nat} (f : Fin n -> Set α) (s : Set α) :
    iUnion (Fin.cons s f) = s union ⋃ i, f i := by
  ext
  simp [Fin.exists_iff_succ]

@[simp]
/--
lemma `iUnion_snoc` / 引理 `iUnion_snoc`

English:
lemma iUnion_snoc
  given: {n : Nat} (f : Fin n -> Set α) (s : Set α)
  proof: by
  ext
  simp [Fin.exists_iff_castSucc, or_comm]

中文:
引理 iUnion_snoc
  条件: {n : 自然数} (f : Fin n -> Set α) (s : Set α)
  证明: by
  ext
  simp [Fin.exists_iff_castSucc, or_comm]

Depends on / 依赖: Fin.exists_iff_castSucc, exists_iff_castSucc, or_comm
-/
lemma iUnion_snoc {n : Nat} (f : Fin n -> Set α) (s : Set α) :
    iUnion (Fin.snoc f s) = (⋃ i, f i) union s := by
  ext
  simp [Fin.exists_iff_castSucc, or_comm]

/--
lemma `iUnion_fin_add_one_eq_iUnion_succ` / 引理 `iUnion_fin_add_one_eq_iUnion_succ`

English:
lemma iUnion_fin_add_one_eq_iUnion_succ
  given: {n : Nat} (f : Fin (n + 1) -> Set α)
  proof: by
  cases f using Fin.consCases
  simp [Function.comp_def]

中文:
引理 iUnion_fin_add_one_eq_iUnion_succ
  条件: {n : 自然数} (f : Fin (n + 1) -> Set α)
  证明: by
  cases f using Fin.consCases
  simp [Function.comp_def]

Depends on / 依赖: Fin.consCases, Function, Function.comp_def, comp_def, consCases
-/
lemma iUnion_fin_add_one_eq_iUnion_succ {n : Nat} (f : Fin (n + 1) -> Set α) :
    ⋃ i, f i = f 0 union Set.iUnion (f ∘ Fin.succ) := by
  cases f using Fin.consCases
  simp [Function.comp_def]

/--
lemma `iUnion_fin_add_one_eq_iUnion_castSucc` / 引理 `iUnion_fin_add_one_eq_iUnion_castSucc`

English:
lemma iUnion_fin_add_one_eq_iUnion_castSucc
  given: {n : Nat} (f : Fin (n + 1) -> Set α)
  proof: by
  cases f using Fin.snocCases
  simp [Function.comp_def]

中文:
引理 iUnion_fin_add_one_eq_iUnion_castSucc
  条件: {n : 自然数} (f : Fin (n + 1) -> Set α)
  证明: by
  cases f using Fin.snocCases
  simp [Function.comp_def]

Depends on / 依赖: Fin.snocCases, Function, Function.comp_def, comp_def, snocCases
-/
lemma iUnion_fin_add_one_eq_iUnion_castSucc {n : Nat} (f : Fin (n + 1) -> Set α) :
    ⋃ i, f i = Set.iUnion (f ∘ Fin.castSucc) union f (.last n) := by
  cases f using Fin.snocCases
  simp [Function.comp_def]

end Set
