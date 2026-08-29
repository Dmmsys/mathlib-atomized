/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Order.Bounds.Defs

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α, β x`.

The predicate `WellFounded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `WellFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/

@[expose] public section

/--
theorem `acc_def` / 定理 `acc_def`

English:
theorem acc_def
  given: {α} {r : α -> α -> Prop} {a : α}
  statement: Acc r a ↔ forall b, r b a -> Acc r b where
  proof: h.rec fun _ h _ => h
  mpr := .intro a

中文:
定理 acc_def
  条件: {α} {r : α -> α -> 命题} {a : α}
  结论: Acc r a ↔ 对任意 b, r b a -> Acc r b where
  证明: h.rec fun _ h _ => h
  mpr := .intro a

Depends on / 依赖: h.rec
-/
theorem acc_def {α} {r : α -> α -> Prop} {a : α} : Acc r a ↔ forall b, r b a -> Acc r b where
  mp h := h.rec fun _ h _ => h
  mpr := .intro a

/--
theorem `exists_not_acc_lt_of_not_acc` / 定理 `exists_not_acc_lt_of_not_acc`

English:
theorem exists_not_acc_lt_of_not_acc
  given: {α} {a : α} {r} (h : ¬Acc r a)
  statement: exists b, ¬Acc r b ∧ r b a
  proof: by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]

中文:
定理 存在_not_acc_lt_of_not_acc
  条件: {α} {a : α} {r} (h : ¬Acc r a)
  结论: 存在 b, ¬Acc r b ∧ r b a
  证明: by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]

Depends on / 依赖: acc_def, and_comm
-/
theorem exists_not_acc_lt_of_not_acc {α} {a : α} {r} (h : ¬Acc r a) : exists b, ¬Acc r b ∧ r b a := by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]

/--
theorem `not_acc_iff_exists_descending_chain` / 定理 `not_acc_iff_exists_descending_chain`

English:
theorem not_acc_iff_exists_descending_chain
  given: {α} {r : α -> α -> Prop} {x : α}
  proof: let f : Nat -> {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a => ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n => (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ => ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ => hf.2 _⟩) h

中文:
定理 not_acc_iff_存在_descending_chain
  条件: {α} {r : α -> α -> 命题} {x : α}
  证明: let f : Nat -> {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a => ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n => (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ => ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ => hf.2 _⟩) h
-/
theorem not_acc_iff_exists_descending_chain {α} {r : α -> α -> Prop} {x : α} :
    ¬Acc r x ↔ exists f : Nat -> α, f 0 = x ∧ forall n, r (f (n + 1)) (f n) where
  mp hx := let f : Nat -> {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a => ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n => (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ => ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ => hf.2 _⟩) h

/--
theorem `acc_iff_isEmpty_descending_chain` / 定理 `acc_iff_isEmpty_descending_chain`

English:
theorem acc_iff_isEmpty_descending_chain
  given: {α} {r : α -> α -> Prop} {x : α}
  proof: by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

中文:
定理 acc_iff_isEmpty_descending_chain
  条件: {α} {r : α -> α -> 命题} {x : α}
  证明: by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

Depends on / 依赖: contrapose, nonempty_subtype, not_acc_iff_exists_descending_chain
-/
theorem acc_iff_isEmpty_descending_chain {α} {r : α -> α -> Prop} {x : α} :
    Acc r x ↔ IsEmpty { f : Nat -> α // f 0 = x ∧ forall n, r (f (n + 1)) (f n) } := by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

/--
theorem `wellFounded_iff_isEmpty_descending_chain` / 定理 `wellFounded_iff_isEmpty_descending_chain`

English:
theorem wellFounded_iff_isEmpty_descending_chain
  given: {α} {r : α -> α -> Prop}
  proof: fun ⟨h⟩ => ⟨fun ⟨f, hf⟩ => (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ => acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h.false ⟨f, hf.2⟩⟩⟩

中文:
定理 wellFounded_iff_isEmpty_descending_chain
  条件: {α} {r : α -> α -> 命题}
  证明: fun ⟨h⟩ => ⟨fun ⟨f, hf⟩ => (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ => acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h.false ⟨f, hf.2⟩⟩⟩

Depends on / 依赖: acc_iff_isEmpty_descending_chain, acc_iff_isEmpty_descending_chain.mp
-/
theorem wellFounded_iff_isEmpty_descending_chain {α} {r : α -> α -> Prop} :
    WellFounded r ↔ IsEmpty { f : Nat -> α // forall n, r (f (n + 1)) (f n) } where
  mp := fun ⟨h⟩ => ⟨fun ⟨f, hf⟩ => (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ => acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h.false ⟨f, hf.2⟩⟩⟩

variable {α β γ : Type*}

namespace WellFounded

variable {r r' : α -> α -> Prop}

/--
theorem `asymm` / 定理 `asymm`

English:
theorem asymm
  given: (h : WellFounded r)
  statement: Std.Asymm r
  proof: ⟨h.asymmetric⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := WellFounded.asymm

中文:
定理 asymm
  条件: (h : 良基 r)
  结论: Std.Asymm r
  证明: ⟨h.asymmetric⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := WellFounded.asymm
-/
protected theorem asymm (h : WellFounded r) : Std.Asymm r := ⟨h.asymmetric⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := WellFounded.asymm

/--
theorem `irrefl` / 定理 `irrefl`

English:
theorem irrefl
  given: (h : WellFounded r)
  statement: Std.Irrefl r
  proof: @Std.Asymm.irrefl α r h.asymm

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := WellFounded.irrefl

中文:
定理 irrefl
  条件: (h : 良基 r)
  结论: Std.Irrefl r
  证明: @Std.Asymm.irrefl α r h.asymm

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := WellFounded.irrefl
-/
protected theorem irrefl (h : WellFounded r) : Std.Irrefl r := @Std.Asymm.irrefl α r h.asymm

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := WellFounded.irrefl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedRelation
  signature: α] : Std.Asymm (α
  body: WellFoundedRelation.wf.asymm

中文:
实例 [良基关系
  签名: α] : Std.Asymm (α
  定义体: WellFoundedRelation.wf.asymm

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.rel
-/
instance [WellFoundedRelation α] : Std.Asymm (α := α) WellFoundedRelation.rel :=
  WellFoundedRelation.wf.asymm

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hr : WellFounded r) (h : forall a b, r' a b -> r a b)
  statement: WellFounded r'
  proof: Subrelation.wf (h _ _) hr

中文:
定理 mono
  条件: (hr : 良基 r) (h : 对任意 a b, r' a b -> r a b)
  结论: 良基 r'
  证明: Subrelation.wf (h _ _) hr

Depends on / 依赖: Subrelation, Subrelation.wf
-/
theorem mono (hr : WellFounded r) (h : forall a b, r' a b -> r a b) : WellFounded r' :=
  Subrelation.wf (h _ _) hr

open scoped Function in -- required for scoped `on` notation
/--
theorem `onFun` / 定理 `onFun`

English:
theorem onFun
  given: {α β : Sort*} {r : β -> β -> Prop} {f : α -> β}
  proof: InvImage.wf _

中文:
定理 onFun
  条件: {α β : 类型层*} {r : β -> β -> 命题} {f : α -> β}
  证明: InvImage.wf _

Depends on / 依赖: InvImage, InvImage.wf
-/
theorem onFun {α β : Sort*} {r : β -> β -> Prop} {f : α -> β} :
    WellFounded r -> WellFounded (r on f) :=
  InvImage.wf _

instance (r : β -> β -> Prop) (f : α -> β) [IsWellFounded β r] :
    IsWellFounded α (r.onFun f) where
  wf := IsWellFounded.wf.onFun

/--
theorem `_root_.Function.Injective.isWellOrder` / 定理 `_root_.Function.Injective.isWellOrder`

English:
theorem _root_.Function.Injective.isWellOrder
  statement: (r : β -> β -> Prop) {f : α -> β} (hf : f.Injective)
  proof: hf.trichotomous_onFun r

中文:
定理 _root_.函数.单射.isWellOrder
  结论: (r : β -> β -> 命题) {f : α -> β} (hf : f.单射)
  证明: hf.trichotomous_onFun r

Depends on / 依赖: hf.trichotomous_onFun, trichotomous_onFun
-/
theorem _root_.Function.Injective.isWellOrder (r : β -> β -> Prop) {f : α -> β} (hf : f.Injective)
    [IsWellOrder β r] : IsWellOrder α (r.onFun f) where
  __ := hf.trichotomous_onFun r

/--
theorem `has_min` / 定理 `has_min`

English:
theorem has_min
  given: {α} {r : α -> α -> Prop} (H : WellFounded r) (s : Set α)

中文:
定理 has_min
  条件: {α} {r : α -> α -> 命题} (H : 良基 r) (s : 集合 α)
-/
theorem has_min {α} {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) :
    s.Nonempty -> exists a in s, forall x in s, ¬r x a
  | ⟨a, ha⟩ => show exists b in s, forall x in s, ¬r x b from
    Acc.recOn (H.apply a) (fun x _ IH =>
not_imp_not.1 fun hne hx => hne ⟨x, hx, fun y hy hyx => hne IH y hyx hy⟩)
      ha

/--
theorem `not_rightTotal` / 定理 `not_rightTotal`

English:
theorem not_rightTotal
  given: (wf : WellFounded r) [Nonempty α]
  statement: ¬ Relator.RightTotal r
  proof: by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hba⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

中文:
定理 not_rightTotal
  条件: (wf : 良基 r) [非空 α]
  结论: ¬ Relator.RightTotal r
  证明: by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hba⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

Depends on / 依赖: Set.mem_univ, Set.univ, Set.univ_nonempty, has_min, mem_univ, specialize, univ_nonempty, wf.has_min
-/
theorem not_rightTotal (wf : WellFounded r) [Nonempty α] : ¬ Relator.RightTotal r := by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hba⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

/--
theorem `not_leftTotal` / 定理 `not_leftTotal`

English:
theorem not_leftTotal
  given: (wf : WellFounded (Function.swap r)) [Nonempty α]
  proof: by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hab⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

中文:
定理 not_leftTotal
  条件: (wf : 良基 (函数.swap r)) [非空 α]
  证明: by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hab⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

Depends on / 依赖: Set.mem_univ, Set.univ, Set.univ_nonempty, has_min, mem_univ, specialize, univ_nonempty, wf.has_min
-/
theorem not_leftTotal (wf : WellFounded (Function.swap r)) [Nonempty α] :
    ¬ Relator.LeftTotal r := by
  intro h
  obtain ⟨a, -, ha⟩ := wf.has_min Set.univ Set.univ_nonempty
  obtain ⟨b, hab⟩ := h a
  specialize ha b (Set.mem_univ b)
  contradiction

/--
Definition of `min` / `min` 的定义

English:
definition min
  signature: {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty)
  body: Classical.choose (H.has_min s h)

中文:
定义 最小值
  签名: {r : α -> α -> 命题} (H : 良基 r) (s : 集合 α) (h : s.非空)
  定义体: Classical.choose (H.has_min s h)

Depends on / 依赖: Classical, Classical.choose, H.has_min, has_min
-/
noncomputable def min {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)

/--
theorem `min_mem` / 定理 `min_mem`

English:
theorem min_mem
  given: {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty)
  proof: let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h

中文:
定理 min_mem
  条件: {r : α -> α -> 命题} (H : 良基 r) (s : 集合 α) (h : s.非空)
  证明: let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h

Depends on / 依赖: Classical, Classical.choose_spec, H.has_min, choose_spec, has_min
-/
theorem min_mem {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h in s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h

/--
theorem `prop_min` / 定理 `prop_min`

English:
theorem prop_min
  given: {r : α -> α -> Prop} (H : WellFounded r) {p : α -> Prop} (h : exists a, p a)
  proof: H.min_mem {a | p a} h

中文:
定理 prop_min
  条件: {r : α -> α -> 命题} (H : 良基 r) {p : α -> 命题} (h : 存在 a, p a)
  证明: H.min_mem {a | p a} h

Depends on / 依赖: H.min_mem, min_mem
-/
theorem prop_min {r : α -> α -> Prop} (H : WellFounded r) {p : α -> Prop} (h : exists a, p a) :
    p (H.min {a | p a} h) :=
  H.min_mem {a | p a} h

/--
theorem `not_lt_min` / 定理 `not_lt_min`

English:
theorem not_lt_min
  given: {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) {x} (hx : x in s)
  proof: let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s ⟨x, hx⟩)
  h' _ hx

中文:
定理 not_lt_min
  条件: {r : α -> α -> 命题} (H : 良基 r) (s : 集合 α) {x} (hx : x in s)
  证明: let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s ⟨x, hx⟩)
  h' _ hx

Depends on / 依赖: Classical, Classical.choose_spec, H.has_min, choose_spec, has_min
-/
theorem not_lt_min {r : α -> α -> Prop} (H : WellFounded r) (s : Set α) {x} (hx : x in s) :
    ¬r x (H.min s ⟨x, hx⟩) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s ⟨x, hx⟩)
  h' _ hx

/--
theorem `min_eq_of_forall_not_lt` / 定理 `min_eq_of_forall_not_lt`

English:
theorem min_eq_of_forall_not_lt
  statement: [Std.Trichotomous r] (wf : WellFounded r) {s : Set α} {m : α}
  proof: Std.Trichotomous.trichotomous _ m (hrm _ <| wf.min_mem s _) (wf.not_lt_min s hms)

中文:
定理 min_eq_of_对任意_not_lt
  结论: [Std.三歧 r] (wf : 良基 r) {s : 集合 α} {m : α}
  证明: Std.Trichotomous.trichotomous _ m (hrm _ <| wf.min_mem s _) (wf.not_lt_min s hms)

Depends on / 依赖: Std.Trichotomous.trichotomous, Trichotomous, min_mem, not_lt_min, trichotomous, wf.min_mem, wf.not_lt_min
-/
theorem min_eq_of_forall_not_lt [Std.Trichotomous r] (wf : WellFounded r) {s : Set α} {m : α}
    (hms : m in s) (hrm : forall x in s, ¬r x m) : wf.min s ⟨m, hms⟩ = m :=
  Std.Trichotomous.trichotomous _ m (hrm _ <| wf.min_mem s _) (wf.not_lt_min s hms)

/--
theorem `notMem_of_lt_min` / 定理 `notMem_of_lt_min`

English:
theorem notMem_of_lt_min
  statement: {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α}
  proof: (wf.not_lt_min s · hx)

中文:
定理 notMem_of_lt_min
  结论: {wf : 良基 r} {s : 集合 α} {hs : s.非空} {x : α}
  证明: (wf.not_lt_min s · hx)

Depends on / 依赖: not_lt_min, wf.not_lt_min
-/
theorem notMem_of_lt_min {wf : WellFounded r} {s : Set α} {hs : s.Nonempty} {x : α}
    (hx : r x (wf.min s hs)) : x ∉ s :=
  (wf.not_lt_min s · hx)

/--
theorem `mem_of_lt_min_compl` / 定理 `mem_of_lt_min_compl`

English:
theorem mem_of_lt_min_compl
  statement: {wf : WellFounded r} {s : Set α} {hs : sᶜ.Nonempty} {x : α}
  proof: Set.notMem_compl_iff.mp notMem_of_lt_min hx

中文:
定理 mem_of_lt_min_compl
  结论: {wf : 良基 r} {s : 集合 α} {hs : sᶜ.非空} {x : α}
  证明: Set.notMem_compl_iff.mp notMem_of_lt_min hx

Depends on / 依赖: Set.notMem_compl_iff.mp, notMem_compl_iff, notMem_of_lt_min
-/
theorem mem_of_lt_min_compl {wf : WellFounded r} {s : Set α} {hs : sᶜ.Nonempty} {x : α}
    (hx : r x (wf.min sᶜ hs)) : x in s :=
Set.notMem_compl_iff.mp notMem_of_lt_min hx

/--
theorem `wellFounded_iff_has_min` / 定理 `wellFounded_iff_has_min`

English:
theorem wellFounded_iff_has_min
  given: {r : α -> α -> Prop}
  proof: by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

@[to_dual]

中文:
定理 wellFounded_iff_has_min
  条件: {r : α -> α -> 命题}
  证明: by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

@[to_dual]

Depends on / 依赖: h.has_min, has_min
-/
theorem wellFounded_iff_has_min {r : α -> α -> Prop} :
    WellFounded r ↔ forall s : Set α, s.Nonempty -> exists m in s, forall x in s, ¬r x m := by
  refine ⟨fun h => h.has_min, fun h => ⟨fun x => ?_⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h {x | ¬Acc r x} ⟨x, hx⟩
  refine hm ⟨_, fun y hy => ?_⟩
  by_contra hy'
  exact hm' y hy' hy

@[to_dual]
/--
theorem `wellFoundedLT_iff_exists_minimal` / 定理 `wellFoundedLT_iff_exists_minimal`

English:
theorem wellFoundedLT_iff_exists_minimal
  given: [Preorder α]
  proof: by
  simp only [isWellFounded_iff, wellFounded_iff_has_min, not_lt_iff_le_imp_ge, Minimal]

@[to_dual]
alias ⟨_root_.WellFoundedLT.exists_minimal, _⟩ := wellFoundedLT_iff_exists_minimal

@[to_dual]

中文:
定理 wellFoundedLT_iff_存在_minimal
  条件: [预序 α]
  证明: by
  simp only [isWellFounded_iff, wellFounded_iff_has_min, not_lt_iff_le_imp_ge, Minimal]

@[to_dual]
alias ⟨_root_.WellFoundedLT.exists_minimal, _⟩ := wellFoundedLT_iff_exists_minimal

@[to_dual]

Depends on / 依赖: Minimal, isWellFounded_iff, not_lt_iff_le_imp_ge, wellFounded_iff_has_min
-/
theorem wellFoundedLT_iff_exists_minimal [Preorder α] :
    WellFoundedLT α ↔ forall s : Set α, s.Nonempty -> exists m, Minimal (· in s) m := by
  simp only [isWellFounded_iff, wellFounded_iff_has_min, not_lt_iff_le_imp_ge, Minimal]

@[to_dual]
alias ⟨_root_.WellFoundedLT.exists_minimal, _⟩ := wellFoundedLT_iff_exists_minimal

@[to_dual]
/--
theorem `minimal_wellFounded_lt_min` / 定理 `minimal_wellFounded_lt_min`

English:
theorem minimal_wellFounded_lt_min
  given: [Preorder α] [WellFoundedLT α] {s : Set α} (h : s.Nonempty)
  proof: by
  grind [Minimal, lt_iff_le_not_ge, WellFounded.min]

中文:
定理 minimal_wellFounded_lt_min
  条件: [预序 α] [WellFoundedLT α] {s : 集合 α} (h : s.非空)
  证明: by
  grind [Minimal, lt_iff_le_not_ge, WellFounded.min]

Depends on / 依赖: Minimal, WellFounded, WellFounded.min, lt_iff_le_not_ge
-/
theorem minimal_wellFounded_lt_min [Preorder α] [WellFoundedLT α] {s : Set α} (h : s.Nonempty) :
    Minimal (· in s) (wellFounded_lt.min s h) := by
  grind [Minimal, lt_iff_le_not_ge, WellFounded.min]

/--
theorem `isWellOrder_iff_exists_not_lt_and_eq_or_gt` / 定理 `isWellOrder_iff_exists_not_lt_and_eq_or_gt`

English:
theorem isWellOrder_iff_exists_not_lt_and_eq_or_gt
  proof: by
  refine ⟨fun h s hs => ?_, fun h => { wf := ?_, trichotomous a b := ?_ }⟩
  · grind [h.wf.has_min, trichotomous_of r]
  · grind [wellFounded_iff_has_min]
  · grind [h {a, b} <| by simp]

中文:
定理 isWellOrder_iff_存在_not_lt_and_eq_or_gt
  证明: by
  refine ⟨fun h s hs => ?_, fun h => { wf := ?_, trichotomous a b := ?_ }⟩
  · grind [h.wf.has_min, trichotomous_of r]
  · grind [wellFounded_iff_has_min]
  · grind [h {a, b} <| by simp]

Depends on / 依赖: h.wf.has_min, has_min, trichotomous, trichotomous_of, wellFounded_iff_has_min
-/
theorem isWellOrder_iff_exists_not_lt_and_eq_or_gt :
    IsWellOrder α r ↔ forall s : Set α, s.Nonempty -> exists m in s, forall x in s, ¬r x m ∧ (m = x ∨ r m x) := by
  refine ⟨fun h s hs => ?_, fun h => { wf := ?_, trichotomous a b := ?_ }⟩
  · grind [h.wf.has_min, trichotomous_of r]
  · grind [wellFounded_iff_has_min]
  · grind [h {a, b} <| by simp]

/--
theorem `min_image` / 定理 `min_image`

English:
theorem min_image
  statement: {r : β -> β -> Prop} [Std.Trichotomous r] (wf : WellFounded r) (f : α -> β)
  proof: by
apply min_eq_of_forall_not_lt wf Set.mem_image_of_mem f min_mem wf.onFun s hne
  rintro _ ⟨a, has, rfl⟩
  exact wf.onFun.not_lt_min s has

中文:
定理 min_image
  结论: {r : β -> β -> 命题} [Std.三歧 r] (wf : 良基 r) (f : α -> β)
  证明: by
apply min_eq_of_forall_not_lt wf Set.mem_image_of_mem f min_mem wf.onFun s hne
  rintro _ ⟨a, has, rfl⟩
  exact wf.onFun.not_lt_min s has

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem, min_eq_of_forall_not_lt, min_mem, not_lt_min, wf.onFun, wf.onFun.not_lt_min
-/
theorem min_image {r : β -> β -> Prop} [Std.Trichotomous r] (wf : WellFounded r) (f : α -> β)
    {s : Set α} (hne : s.Nonempty) :
    wf.min (f '' s) (hne.image f) = f (wf.onFun (f := f) |>.min s hne) := by
apply min_eq_of_forall_not_lt wf Set.mem_image_of_mem f min_mem wf.onFun s hne
  rintro _ ⟨a, has, rfl⟩
  exact wf.onFun.not_lt_min s has

/--
theorem `not_rel_apply_succ` / 定理 `not_rel_apply_succ`

English:
theorem not_rel_apply_succ
  given: [h : IsWellFounded α r] (f : Nat -> α)
  statement: exists n, ¬ r (f (n + 1)) (f n)
  proof: by
  by_contra! hf
  exact (wellFounded_iff_isEmpty_descending_chain.1 h.wf).elim ⟨f, hf⟩

中文:
定理 not_rel_apply_succ
  条件: [h : 是良基 α r] (f : 自然数 -> α)
  结论: 存在 n, ¬ r (f (n + 1)) (f n)
  证明: by
  by_contra! hf
  exact (wellFounded_iff_isEmpty_descending_chain.1 h.wf).elim ⟨f, hf⟩

Depends on / 依赖: h.wf, wellFounded_iff_isEmpty_descending_chain
-/
theorem not_rel_apply_succ [h : IsWellFounded α r] (f : Nat -> α) : exists n, ¬ r (f (n + 1)) (f n) := by
  by_contra! hf
  exact (wellFounded_iff_isEmpty_descending_chain.1 h.wf).elim ⟨f, hf⟩

open Set

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def sup {r : α -> α -> Prop} (wf : WellFounded r) (s : Set α)
  body: wf.min { x | forall a in s, r a x } h

中文:
定义 noncomputable
  签名: def 上确界 {r : α -> α -> 命题} (wf : 良基 r) (s : 集合 α)
  定义体: wf.min { x | forall a in s, r a x } h
-/
protected noncomputable def sup {r : α -> α -> Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | forall a in s, r a x } h

/--
theorem `lt_sup` / 定理 `lt_sup`

English:
theorem lt_sup
  statement: {r : α -> α -> Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
  proof: min_mem wf { x | forall a in s, r a x } h x hx

中文:
定理 lt_sup
  结论: {r : α -> α -> 命题} (wf : 良基 r) {s : 集合 α} (h : 有界 r s) {x}
  证明: min_mem wf { x | forall a in s, r a x } h x hx
-/
protected theorem lt_sup {r : α -> α -> Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x in s) : r x (wf.sup s h) :=
  min_mem wf { x | forall a in s, r a x } h x hx

end WellFounded

section LinearOrder

variable [LinearOrder β] [Preorder γ]

-- TODO: the name `WellFounded.min` is incorrect when the assumption is that `>` is well-founded.
@[to_dual none]
/--
theorem `WellFounded.min_le` / 定理 `WellFounded.min_le`

English:
theorem WellFounded.min_le
  statement: (h : WellFounded ((· < ·) : β -> β -> Prop))
  proof: not_lt.1 h.not_lt_min _ hx

中文:
定理 良基.min_le
  结论: (h : 良基 ((· < ·) : β -> β -> 命题))
  证明: not_lt.1 h.not_lt_min _ hx

Depends on / 依赖: h.not_lt_min, not_lt, not_lt_min
-/
theorem WellFounded.min_le (h : WellFounded ((· < ·) : β -> β -> Prop))
    {x : β} {s : Set β} (hx : x in s) : h.min s ⟨x, hx⟩ <= x :=
not_lt.1 h.not_lt_min _ hx

/--
theorem `Set.range_injOn_strictMono` / 定理 `Set.range_injOn_strictMono`

English:
theorem Set.range_injOn_strictMono
  given: [WellFoundedLT β]
  proof: by
  intro f hf g hg hfg
  ext a
  apply WellFoundedLT.induction a
  intro a IH
  obtain ⟨b, hb⟩ := hfg ▸ mem_range_self a
  obtain h | rfl | h := lt_trichotomy b a
  · rw [← IH b h] at hb
    cases (hf.injective hb).not_lt h
  · rw [hb]
  · obtain ⟨c, hc⟩ := hfg.symm ▸ mem_range_self a
    have := hg h
    rw [hb]; rw [← hc]; rw [hf.lt_iff_lt] at this
    rw [IH c this] at hc
    cases (hg.injective hc).not_lt this

中文:
定理 集合.range_injOn_strictMono
  条件: [WellFoundedLT β]
  证明: by
  intro f hf g hg hfg
  ext a
  apply WellFoundedLT.induction a
  intro a IH
  obtain ⟨b, hb⟩ := hfg ▸ mem_range_self a
  obtain h | rfl | h := lt_trichotomy b a
  · rw [← IH b h] at hb
    cases (hf.injective hb).not_lt h
  · rw [hb]
  · obtain ⟨c, hc⟩ := hfg.symm ▸ mem_range_self a
    have := hg h
    rw [hb]; rw [← hc]; rw [hf.lt_iff_lt] at this
    rw [IH c this] at hc
    cases (hg.injective hc).not_lt this

Depends on / 依赖: WellFoundedLT, WellFoundedLT.induction, hf.injective, hf.lt_iff_lt, hfg.symm, hg.injective, injective, lt_iff_lt, lt_trichotomy, mem_range_self, not_lt
-/
theorem Set.range_injOn_strictMono [WellFoundedLT β] :
    Set.InjOn Set.range { f : β -> γ | StrictMono f } := by
  intro f hf g hg hfg
  ext a
  apply WellFoundedLT.induction a
  intro a IH
  obtain ⟨b, hb⟩ := hfg ▸ mem_range_self a
  obtain h | rfl | h := lt_trichotomy b a
  · rw [← IH b h] at hb
    cases (hf.injective hb).not_lt h
  · rw [hb]
  · obtain ⟨c, hc⟩ := hfg.symm ▸ mem_range_self a
    have := hg h
    rw [hb]; rw [← hc]; rw [hf.lt_iff_lt] at this
    rw [IH c this] at hc
    cases (hg.injective hc).not_lt this

/--
theorem `Set.range_injOn_strictAnti` / 定理 `Set.range_injOn_strictAnti`

English:
theorem Set.range_injOn_strictAnti
  given: [WellFoundedGT β]
  proof: fun _ hf _ hg => Set.range_injOn_strictMono (β := βᵒᵈ) hf.dual hg.dual

中文:
定理 集合.range_injOn_strictAnti
  条件: [WellFoundedGT β]
  证明: fun _ hf _ hg => Set.range_injOn_strictMono (β := βᵒᵈ) hf.dual hg.dual

Depends on / 依赖: Set.range_injOn_strictMono, hf.dual, hg.dual, range_injOn_strictMono
-/
theorem Set.range_injOn_strictAnti [WellFoundedGT β] :
    Set.InjOn Set.range { f : β -> γ | StrictAnti f } :=
  fun _ hf _ hg => Set.range_injOn_strictMono (β := βᵒᵈ) hf.dual hg.dual

/--
theorem `StrictMono.range_inj` / 定理 `StrictMono.range_inj`

English:
theorem StrictMono.range_inj
  statement: [WellFoundedLT β] {f g : β -> γ}
  proof: Set.range_injOn_strictMono.eq_iff hf hg

中文:
定理 严格递增.range_inj
  结论: [WellFoundedLT β] {f g : β -> γ}
  证明: Set.range_injOn_strictMono.eq_iff hf hg

Depends on / 依赖: Set.range_injOn_strictMono.eq_iff, eq_iff, range_injOn_strictMono
-/
theorem StrictMono.range_inj [WellFoundedLT β] {f g : β -> γ}
    (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictMono.eq_iff hf hg

/--
theorem `StrictAnti.range_inj` / 定理 `StrictAnti.range_inj`

English:
theorem StrictAnti.range_inj
  statement: [WellFoundedGT β] {f g : β -> γ}
  proof: Set.range_injOn_strictAnti.eq_iff hf hg

中文:
定理 严格递减.range_inj
  结论: [WellFoundedGT β] {f g : β -> γ}
  证明: Set.range_injOn_strictAnti.eq_iff hf hg

Depends on / 依赖: Set.range_injOn_strictAnti.eq_iff, eq_iff, range_injOn_strictAnti
-/
theorem StrictAnti.range_inj [WellFoundedGT β] {f g : β -> γ}
    (hf : StrictAnti f) (hg : StrictAnti g) : Set.range f = Set.range g ↔ f = g :=
  Set.range_injOn_strictAnti.eq_iff hf hg

/--
theorem `StrictMono.id_le` / 定理 `StrictMono.id_le`

English:
theorem StrictMono.id_le
  given: [WellFoundedLT β] {f : β -> β} (hf : StrictMono f)
  statement: id <= f
  proof: by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {i | f i < i} H
  exact hm' _ (hf hm) hm

中文:
定理 严格递增.id_le
  条件: [WellFoundedLT β] {f : β -> β} (hf : 严格递增 f)
  结论: id <= f
  证明: by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {i | f i < i} H
  exact hm' _ (hf hm) hm

Depends on / 依赖: Pi.le_def, has_min, le_def, wellFounded_lt, wellFounded_lt.has_min
-/
theorem StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : StrictMono f) : id <= f := by
  rw [Pi.le_def]
  by_contra! H
  obtain ⟨m, hm, hm'⟩ := wellFounded_lt.has_min {i | f i < i} H
  exact hm' _ (hf hm) hm

/--
theorem `StrictMono.le_apply` / 定理 `StrictMono.le_apply`

English:
theorem StrictMono.le_apply
  given: [WellFoundedLT β] {f : β -> β} (hf : StrictMono f) {x}
  statement: x <= f x
  proof: hf.id_le x

中文:
定理 严格递增.le_apply
  条件: [WellFoundedLT β] {f : β -> β} (hf : 严格递增 f) {x}
  结论: x <= f x
  证明: hf.id_le x

Depends on / 依赖: hf.id_le, id_le
-/
theorem StrictMono.le_apply [WellFoundedLT β] {f : β -> β} (hf : StrictMono f) {x} : x <= f x :=
  hf.id_le x

/--
theorem `StrictMono.le_id` / 定理 `StrictMono.le_id`

English:
theorem StrictMono.le_id
  given: [WellFoundedGT β] {f : β -> β} (hf : StrictMono f)
  statement: f <= id
  proof: StrictMono.id_le (β := βᵒᵈ) hf.dual

中文:
定理 严格递增.le_id
  条件: [WellFoundedGT β] {f : β -> β} (hf : 严格递增 f)
  结论: f <= id
  证明: StrictMono.id_le (β := βᵒᵈ) hf.dual

Depends on / 依赖: StrictMono, StrictMono.id_le, hf.dual, id_le
-/
theorem StrictMono.le_id [WellFoundedGT β] {f : β -> β} (hf : StrictMono f) : f <= id :=
  StrictMono.id_le (β := βᵒᵈ) hf.dual

/--
theorem `StrictMono.apply_le` / 定理 `StrictMono.apply_le`

English:
theorem StrictMono.apply_le
  given: [WellFoundedGT β] {f : β -> β} (hf : StrictMono f) {x}
  statement: f x <= x
  proof: StrictMono.le_apply (β := βᵒᵈ) hf.dual

中文:
定理 严格递增.apply_le
  条件: [WellFoundedGT β] {f : β -> β} (hf : 严格递增 f) {x}
  结论: f x <= x
  证明: StrictMono.le_apply (β := βᵒᵈ) hf.dual

Depends on / 依赖: StrictMono, StrictMono.le_apply, hf.dual, le_apply
-/
theorem StrictMono.apply_le [WellFoundedGT β] {f : β -> β} (hf : StrictMono f) {x} : f x <= x :=
  StrictMono.le_apply (β := βᵒᵈ) hf.dual

/--
theorem `StrictMono.not_bddAbove_range_of_wellFoundedLT` / 定理 `StrictMono.not_bddAbove_range_of_wellFoundedLT`

English:
theorem StrictMono.not_bddAbove_range_of_wellFoundedLT
  statement: {f : β -> β} [WellFoundedLT β] [NoMaxOrder β]
  proof: by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := exists_gt a
  exact ((hf.le_apply.trans_lt (hf hb)).trans_le <| ha (Set.mem_range_self _)).false

中文:
定理 严格递增.not_bddAbove_range_of_wellFoundedLT
  结论: {f : β -> β} [WellFoundedLT β] [NoMax序 β]
  证明: by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := exists_gt a
  exact ((hf.le_apply.trans_lt (hf hb)).trans_le <| ha (Set.mem_range_self _)).false

Depends on / 依赖: Set.mem_range_self, exists_gt, hf.le_apply.trans_lt, le_apply, mem_range_self, trans_le, trans_lt
-/
theorem StrictMono.not_bddAbove_range_of_wellFoundedLT {f : β -> β} [WellFoundedLT β] [NoMaxOrder β]
    (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := exists_gt a
  exact ((hf.le_apply.trans_lt (hf hb)).trans_le <| ha (Set.mem_range_self _)).false

/--
theorem `StrictMono.not_bddBelow_range_of_wellFoundedGT` / 定理 `StrictMono.not_bddBelow_range_of_wellFoundedGT`

English:
theorem StrictMono.not_bddBelow_range_of_wellFoundedGT
  statement: {f : β -> β} [WellFoundedGT β] [NoMinOrder β]
  proof: hf.dual.not_bddAbove_range_of_wellFoundedLT

中文:
定理 严格递增.not_bddBelow_range_of_wellFoundedGT
  结论: {f : β -> β} [WellFoundedGT β] [NoMin序 β]
  证明: hf.dual.not_bddAbove_range_of_wellFoundedLT

Depends on / 依赖: hf.dual.not_bddAbove_range_of_wellFoundedLT, not_bddAbove_range_of_wellFoundedLT
-/
theorem StrictMono.not_bddBelow_range_of_wellFoundedGT {f : β -> β} [WellFoundedGT β] [NoMinOrder β]
    (hf : StrictMono f) : ¬ BddBelow (Set.range f) :=
  hf.dual.not_bddAbove_range_of_wellFoundedLT

end LinearOrder

namespace Function

variable (f : α -> β)

section LT

variable [LT β] [WellFoundedLT β]

/--
Definition of `argmin` / `argmin` 的定义

English:
definition argmin
  signature: [Nonempty α]
  body: WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

中文:
定义 argmin
  签名: [非空 α]
  定义体: WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

Depends on / 依赖: InvImage, InvImage.wf, Set.univ, Set.univ_nonempty, WellFounded, WellFounded.min, univ_nonempty, wellFounded_lt
-/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

/--
theorem `not_lt_argmin` / 定理 `not_lt_argmin`

English:
theorem not_lt_argmin
  given: [Nonempty α] (a : α)
  statement: ¬f a < f (argmin f)
  proof: WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ (Set.mem_univ a)

中文:
定理 not_lt_argmin
  条件: [非空 α] (a : α)
  结论: ¬f a < f (argmin f)
  证明: WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ (Set.mem_univ a)

Depends on / 依赖: InvImage, InvImage.wf, Set.mem_univ, WellFounded, WellFounded.not_lt_min, mem_univ, not_lt_min, wellFounded_lt
-/
theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ (Set.mem_univ a)

/--
Definition of `argminOn` / `argminOn` 的定义

English:
definition argminOn
  signature: (s : Set α) (hs : s.Nonempty)
  body: WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]

中文:
定义 argminOn
  签名: (s : 集合 α) (hs : s.非空)
  定义体: WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]

Depends on / 依赖: InvImage, InvImage.wf, WellFounded, WellFounded.min, wellFounded_lt
-/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]
/--
theorem `argminOn_mem` / 定理 `argminOn_mem`

English:
theorem argminOn_mem
  given: (s : Set α) (hs : s.Nonempty)
  statement: argminOn f s hs in s
  proof: WellFounded.min_mem _ _ _

中文:
定理 argminOn_mem
  条件: (s : 集合 α) (hs : s.非空)
  结论: argminOn f s hs in s
  证明: WellFounded.min_mem _ _ _

Depends on / 依赖: WellFounded, WellFounded.min_mem, min_mem
-/
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs in s :=
  WellFounded.min_mem _ _ _

/--
theorem `not_lt_argminOn` / 定理 `not_lt_argminOn`

English:
theorem not_lt_argminOn
  given: (s : Set α) {a : α} (ha : a in s)
  statement: ¬f a < f (argminOn f s ⟨a, ha⟩)
  proof: WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s ha

中文:
定理 not_lt_argminOn
  条件: (s : 集合 α) {a : α} (ha : a in s)
  结论: ¬f a < f (argminOn f s ⟨a, ha⟩)
  证明: WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s ha

Depends on / 依赖: InvImage, InvImage.wf, WellFounded, WellFounded.not_lt_min, not_lt_min, wellFounded_lt
-/
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a in s) : ¬f a < f (argminOn f s ⟨a, ha⟩) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s ha

end LT

section LinearOrder

variable [LinearOrder β] [WellFoundedLT β]

/--
theorem `argmin_le` / 定理 `argmin_le`

English:
theorem argmin_le
  given: (a : α) [Nonempty α]
  statement: f (argmin f) <= f a
  proof: not_lt.mp not_lt_argmin f a

中文:
定理 argmin_le
  条件: (a : α) [非空 α]
  结论: f (argmin f) <= f a
  证明: not_lt.mp not_lt_argmin f a

Depends on / 依赖: not_lt, not_lt.mp, not_lt_argmin
-/
theorem argmin_le (a : α) [Nonempty α] : f (argmin f) <= f a :=
not_lt.mp not_lt_argmin f a

/--
theorem `isMinimalFor_argmin` / 定理 `isMinimalFor_argmin`

English:
theorem isMinimalFor_argmin
  given: [Nonempty α]
  proof: ⟨trivial, fun a _ _ => argmin_le f a⟩

中文:
定理 isMinimalFor_argmin
  条件: [非空 α]
  证明: ⟨trivial, fun a _ _ => argmin_le f a⟩

Depends on / 依赖: argmin_le
-/
theorem isMinimalFor_argmin [Nonempty α] :
    MinimalFor (fun _ => True) f (argmin f) :=
  ⟨trivial, fun a _ _ => argmin_le f a⟩

/--
theorem `argminOn_le` / 定理 `argminOn_le`

English:
theorem argminOn_le
  given: (s : Set α) {a : α} (ha : a in s)
  proof: not_lt.mp not_lt_argminOn f s ha

中文:
定理 argminOn_le
  条件: (s : 集合 α) {a : α} (ha : a in s)
  证明: not_lt.mp not_lt_argminOn f s ha

Depends on / 依赖: not_lt, not_lt.mp, not_lt_argminOn
-/
theorem argminOn_le (s : Set α) {a : α} (ha : a in s) :
    f (argminOn f s ⟨a, ha⟩) <= f a :=
not_lt.mp not_lt_argminOn f s ha

/--
theorem `isMinimalFor_argminOn` / 定理 `isMinimalFor_argminOn`

English:
theorem isMinimalFor_argminOn
  given: (s : Set α) (hs : s.Nonempty)
  proof: ⟨argminOn_mem f s hs, fun _ h _ => argminOn_le f s h⟩

中文:
定理 isMinimalFor_argminOn
  条件: (s : 集合 α) (hs : s.非空)
  证明: ⟨argminOn_mem f s hs, fun _ h _ => argminOn_le f s h⟩

Depends on / 依赖: argminOn_le, argminOn_mem
-/
theorem isMinimalFor_argminOn (s : Set α) (hs : s.Nonempty) :
    MinimalFor (· in s) f (argminOn f s hs) :=
  ⟨argminOn_mem f s hs, fun _ h _ => argminOn_le f s h⟩

end LinearOrder

end Function

section Induction

/--
theorem `Acc.induction_bot'` / 定理 `Acc.induction_bot'`

English:
theorem Acc.induction_bot'
  statement: {α β} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {C : β -> Prop}
  proof: (@Acc.recOn _ _ (fun x _ => C (f x) -> C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

中文:
定理 Acc.induction_bot'
  结论: {α β} {r : α -> α -> 命题} {a bot : α} (ha : Acc r a) {C : β -> 命题}
  证明: (@Acc.recOn _ _ (fun x _ => C (f x) -> C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

Depends on / 依赖: Acc.recOn, eq_or_ne
-/
theorem Acc.induction_bot' {α β} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {C : β -> Prop}
    {f : α -> β} (ih : forall b, f b != f bot -> C (f b) -> exists c, r c b ∧ C (f c)) : C (f a) -> C (f bot) :=
  (@Acc.recOn _ _ (fun x _ => C (f x) -> C (f bot)) _ ha) fun x _ ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) (fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂)

/--
theorem `Acc.induction_bot` / 定理 `Acc.induction_bot`

English:
theorem Acc.induction_bot
  statement: {α} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {C : α -> Prop}
  proof: ha.induction_bot' ih

中文:
定理 Acc.induction_bot
  结论: {α} {r : α -> α -> 命题} {a bot : α} (ha : Acc r a) {C : α -> 命题}
  证明: ha.induction_bot' ih

Depends on / 依赖: ha.induction_bot, induction_bot
-/
theorem Acc.induction_bot {α} {r : α -> α -> Prop} {a bot : α} (ha : Acc r a) {C : α -> Prop}
    (ih : forall b, b != bot -> C b -> exists c, r c b ∧ C c) : C a -> C bot :=
  ha.induction_bot' ih

/--
theorem `WellFounded.induction_bot'` / 定理 `WellFounded.induction_bot'`

English:
theorem WellFounded.induction_bot'
  statement: {α β} {r : α -> α -> Prop} (hwf : WellFounded r) {a bot : α}
  proof: (hwf.apply a).induction_bot' ih

中文:
定理 良基.induction_bot'
  结论: {α β} {r : α -> α -> 命题} (hwf : 良基 r) {a bot : α}
  证明: (hwf.apply a).induction_bot' ih

Depends on / 依赖: hwf.apply, induction_bot
-/
theorem WellFounded.induction_bot' {α β} {r : α -> α -> Prop} (hwf : WellFounded r) {a bot : α}
    {C : β -> Prop} {f : α -> β} (ih : forall b, f b != f bot -> C (f b) -> exists c, r c b ∧ C (f c)) :
    C (f a) -> C (f bot) :=
  (hwf.apply a).induction_bot' ih

/--
theorem `WellFounded.induction_bot` / 定理 `WellFounded.induction_bot`

English:
theorem WellFounded.induction_bot
  statement: {α} {r : α -> α -> Prop} (hwf : WellFounded r) {a bot : α}
  proof: hwf.induction_bot' ih

中文:
定理 良基.induction_bot
  结论: {α} {r : α -> α -> 命题} (hwf : 良基 r) {a bot : α}
  证明: hwf.induction_bot' ih

Depends on / 依赖: hwf.induction_bot, induction_bot
-/
theorem WellFounded.induction_bot {α} {r : α -> α -> Prop} (hwf : WellFounded r) {a bot : α}
    {C : α -> Prop} (ih : forall b, b != bot -> C b -> exists c, r c b ∧ C c) : C a -> C bot :=
  hwf.induction_bot' ih

end Induction

/-- A nonempty linear order with well-founded `<` has a bottom element. -/
@[to_dual (attr := instance_reducible)
/-- A nonempty linear order with well-founded `>` has a top element. -/]
/--
Definition of `WellFoundedLT.toOrderBot` / `WellFoundedLT.toOrderBot` 的定义

English:
definition WellFoundedLT.toOrderBot
  signature: (α) [LinearOrder α] [Nonempty α] [h : WellFoundedLT α]
  body: h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

@[to_dual]

中文:
定义 WellFoundedLT.toOrderBot
  签名: (α) [线性序 α] [非空 α] [h : WellFoundedLT α]
  定义体: h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

@[to_dual]

Depends on / 依赖: Set.univ_nonempty, h.wf.min, univ_nonempty
-/
noncomputable def WellFoundedLT.toOrderBot (α) [LinearOrder α] [Nonempty α] [h : WellFoundedLT α] :
    OrderBot α where
  bot := h.wf.min _ Set.univ_nonempty
  bot_le a := h.wf.min_le (Set.mem_univ a)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LT
  signature: α] [h
  body: InvImage.wf ULift.down h.wf

中文:
实例 [LT
  签名: α] [h
  定义体: InvImage.wf ULift.down h.wf

Depends on / 依赖: InvImage, InvImage.wf, ULift.down, h.wf
-/
instance [LT α] [h : WellFoundedLT α] : WellFoundedLT (ULift α) where
  wf := InvImage.wf ULift.down h.wf
