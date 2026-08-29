/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Multiset.Fold
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# The fold operation for a commutative associative operation over a finset.
-/

@[expose] public section

assert_not_exists Monoid

namespace Finset

open Multiset

variable {α β γ : Type*}

/-! ### fold -/


section Fold

variable (op : β -> β -> β) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/--
Definition of `fold` / `fold` 的定义

English:
definition fold
  signature: (b : β) (f : α -> β) (s : Finset α)
  body: (s.1.map f).fold op b

中文:
定义 fold
  签名: (b : β) (f : α -> β) (s : 有限集 α)
  定义体: (s.1.map f).fold op b
-/
def fold (b : β) (f : α -> β) (s : Finset α) : β :=
  (s.1.map f).fold op b

variable {op} {f : α -> β} {b : β} {s : Finset α} {a : α}

@[simp]
/--
theorem `fold_empty` / 定理 `fold_empty`

English:
theorem fold_empty
  statement: (∅ : Finset α).fold op b f = b
  proof: rfl

@[simp]

中文:
定理 fold_empty
  结论: (∅ : 有限集 α).fold op b f = b
  证明: rfl

@[simp]
-/
theorem fold_empty : (∅ : Finset α).fold op b f = b :=
  rfl

@[simp]
/--
theorem `fold_cons` / 定理 `fold_cons`

English:
theorem fold_cons
  given: (h : a ∉ s)
  statement: (cons a s h).fold op b f = f a * s.fold op b f
  proof: by
  dsimp only [fold]
  rw [cons_val]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]

中文:
定理 fold_cons
  条件: (h : a ∉ s)
  结论: (cons a s h).fold op b f = f a * s.fold op b f
  证明: by
  dsimp only [fold]
  rw [cons_val]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_cons, cons_val, fold_cons_left, map_cons
-/
theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f := by
  dsimp only [fold]
  rw [cons_val]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]
/--
theorem `fold_insert` / 定理 `fold_insert`

English:
theorem fold_insert
  given: [DecidableEq α] (h : a ∉ s)
  proof: by
  unfold fold
  rw [insert_val]; rw [ndinsert_of_notMem h]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]

中文:
定理 fold_insert
  条件: [DecidableEq α] (h : a ∉ s)
  证明: by
  unfold fold
  rw [insert_val]; rw [ndinsert_of_notMem h]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_cons, fold_cons_left, insert_val, map_cons, ndinsert_of_notMem
-/
theorem fold_insert [DecidableEq α] (h : a ∉ s) :
    (insert a s).fold op b f = f a * s.fold op b f := by
  unfold fold
  rw [insert_val]; rw [ndinsert_of_notMem h]; rw [Multiset.map_cons]; rw [fold_cons_left]

@[simp]
/--
theorem `fold_singleton` / 定理 `fold_singleton`

English:
theorem fold_singleton
  statement: ({a} : Finset α).fold op b f = f a * b
  proof: rfl

@[simp]

中文:
定理 fold_singleton
  结论: ({a} : 有限集 α).fold op b f = f a * b
  证明: rfl

@[simp]
-/
theorem fold_singleton : ({a} : Finset α).fold op b f = f a * b :=
  rfl

@[simp]
/--
theorem `fold_map` / 定理 `fold_map`

English:
theorem fold_map
  given: {g : γ ↪ α} {s : Finset γ}
  statement: (s.map g).fold op b f = s.fold op b (f ∘ g)
  proof: by
  simp only [fold, map, Multiset.map_map]

@[simp]

中文:
定理 fold_map
  条件: {g : γ ↪ α} {s : 有限集 γ}
  结论: (s.map g).fold op b f = s.fold op b (f ∘ g)
  证明: by
  simp only [fold, map, Multiset.map_map]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_map, map_map
-/
theorem fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, map, Multiset.map_map]

@[simp]
/--
theorem `fold_image` / 定理 `fold_image`

English:
theorem fold_image
  statement: [DecidableEq α] {g : γ -> α} {s : Finset γ}
  proof: by
  simp only [fold, image_val_of_injOn H, Multiset.map_map]

@[congr]

中文:
定理 fold_image
  结论: [DecidableEq α] {g : γ -> α} {s : 有限集 γ}
  证明: by
  simp only [fold, image_val_of_injOn H, Multiset.map_map]

@[congr]

Depends on / 依赖: Multiset, Multiset.map_map, image_val_of_injOn, map_map
-/
theorem fold_image [DecidableEq α] {g : γ -> α} {s : Finset γ}
    (H : Set.InjOn g s) : (s.image g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, image_val_of_injOn H, Multiset.map_map]

@[congr]
/--
theorem `fold_congr` / 定理 `fold_congr`

English:
theorem fold_congr
  given: {g : α -> β} (H : forall x in s, f x = g x)
  statement: s.fold op b f = s.fold op b g
  proof: by
  rw [fold]; rw [fold]; rw [map_congr rfl H]

中文:
定理 fold_congr
  条件: {g : α -> β} (H : 对任意 x in s, f x = g x)
  结论: s.fold op b f = s.fold op b g
  证明: by
  rw [fold]; rw [fold]; rw [map_congr rfl H]

Depends on / 依赖: map_congr
-/
theorem fold_congr {g : α -> β} (H : forall x in s, f x = g x) : s.fold op b f = s.fold op b g := by
  rw [fold]; rw [fold]; rw [map_congr rfl H]

/--
theorem `fold_op_distrib` / 定理 `fold_op_distrib`

English:
theorem fold_op_distrib
  given: {f g : α -> β} {b₁ b₂ : β}
  proof: by
  simp only [fold, fold_distrib]

中文:
定理 fold_op_distrib
  条件: {f g : α -> β} {b₁ b₂ : β}
  证明: by
  simp only [fold, fold_distrib]

Depends on / 依赖: fold_distrib
-/
theorem fold_op_distrib {f g : α -> β} {b₁ b₂ : β} :
    (s.fold op (b₁ * b₂) fun x => f x * g x) = s.fold op b₁ f * s.fold op b₂ g := by
  simp only [fold, fold_distrib]

/--
theorem `fold_const` / 定理 `fold_const`

English:
theorem fold_const
  given: [hd : Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c)
  proof: by
  classical
    induction s using Finset.induction_on generalizing hd with
    | empty => simp
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h

中文:
定理 fold_const
  条件: [hd : 可判定 (s = ∅)] (c : β) (h : op c (op b c) = op b c)
  证明: by
  classical
    induction s using Finset.induction_on generalizing hd with
    | empty => simp
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h

Depends on / 依赖: Finset, Finset.fold_insert, Finset.induction_on, Finset.insert_ne_empty, classical, fold_insert, generalizing, hc.comm, if_false, induction_on, insert, insert_ne_empty, split_ifs
-/
theorem fold_const [hd : Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c) :
    Finset.fold op b (fun _ => c) s = if s = ∅ then b else op b c := by
  classical
    induction s using Finset.induction_on generalizing hd with
    | empty => simp
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h

/--
theorem `fold_hom` / 定理 `fold_hom`

English:
theorem fold_hom
  statement: {op' : γ -> γ -> γ} [Std.Commutative op'] [Std.Associative op'] {m : β -> γ}
  proof: by
  rw [fold]; rw [fold]; rw [← Multiset.fold_hom op hm]; rw [Multiset.map_map]
  simp only [Function.comp_apply]

中文:
定理 fold_hom
  结论: {op' : γ -> γ -> γ} [Std.交换 op'] [Std.结合 op'] {m : β -> γ}
  证明: by
  rw [fold]; rw [fold]; rw [← Multiset.fold_hom op hm]; rw [Multiset.map_map]
  simp only [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Multiset, Multiset.fold_hom, Multiset.map_map, comp_apply, fold_hom, map_map
-/
theorem fold_hom {op' : γ -> γ -> γ} [Std.Commutative op'] [Std.Associative op'] {m : β -> γ}
    (hm : forall x y, m (op x y) = op' (m x) (m y)) :
    (s.fold op' (m b) fun x => m (f x)) = m (s.fold op b f) := by
  rw [fold]; rw [fold]; rw [← Multiset.fold_hom op hm]; rw [Multiset.map_map]
  simp only [Function.comp_apply]

/--
theorem `fold_disjUnion` / 定理 `fold_disjUnion`

English:
theorem fold_disjUnion
  given: {s₁ s₂ : Finset α} {b₁ b₂ : β} (h)
  proof: (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)

中文:
定理 fold_disjUnion
  条件: {s₁ s₂ : 有限集 α} {b₁ b₂ : β} (h)
  证明: (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)

Depends on / 依赖: Multiset, Multiset.fold_add, Multiset.map_add, congr_arg, fold_add, map_add
-/
theorem fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h) :
    (s₁.disjUnion s₂ h).fold op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f :=
  (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)

/--
theorem `fold_union_inter` / 定理 `fold_union_inter`

English:
theorem fold_union_inter
  given: [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β}
  proof: by
  unfold fold
  rw [← fold_add op]; rw [← Multiset.map_add]; rw [union_val]; rw [inter_val]; rw [union_add_inter]; rw [Multiset.map_add]; rw [hc.comm]; rw [fold_add]

@[simp]

中文:
定理 fold_union_inter
  条件: [DecidableEq α] {s₁ s₂ : 有限集 α} {b₁ b₂ : β}
  证明: by
  unfold fold
  rw [← fold_add op]; rw [← Multiset.map_add]; rw [union_val]; rw [inter_val]; rw [union_add_inter]; rw [Multiset.map_add]; rw [hc.comm]; rw [fold_add]

@[simp]

Depends on / 依赖: Multiset, Multiset.map_add, fold_add, hc.comm, inter_val, map_add, union_add_inter, union_val
-/
theorem fold_union_inter [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β} :
    ((s₁ union s₂).fold op b₁ f * (s₁ inter s₂).fold op b₂ f) = s₁.fold op b₂ f * s₂.fold op b₁ f := by
  unfold fold
  rw [← fold_add op]; rw [← Multiset.map_add]; rw [union_val]; rw [inter_val]; rw [union_add_inter]; rw [Multiset.map_add]; rw [hc.comm]; rw [fold_add]

@[simp]
/--
theorem `fold_insert_idem` / 定理 `fold_insert_idem`

English:
theorem fold_insert_idem
  given: [DecidableEq α] [hi : Std.IdempotentOp op]
  proof: by
  by_cases h : a in s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h

中文:
定理 fold_insert_idem
  条件: [DecidableEq α] [hi : Std.IdempotentOp op]
  证明: by
  by_cases h : a in s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h

Depends on / 依赖: fold_insert, ha.assoc, hi.idempotent, idempotent, insert_erase
-/
theorem fold_insert_idem [DecidableEq α] [hi : Std.IdempotentOp op] :
    (insert a s).fold op b f = f a * s.fold op b f := by
  by_cases h : a in s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h

/--
theorem `fold_image_idem` / 定理 `fold_image_idem`

English:
theorem fold_image_idem
  given: [DecidableEq α] {g : γ -> α} {s : Finset γ} [hi : Std.IdempotentOp op]
  proof: by
  induction s using Finset.cons_induction with
  | empty => rw [fold_empty, image_empty, fold_empty]
  | cons x xs hx ih =>
    have := Classical.decEq γ
    rw [fold_cons]; rw [cons_eq_insert]; rw [image_insert]; rw [fold_insert_idem]; rw [ih]
    simp only [Function.comp_apply]

中文:
定理 fold_image_idem
  条件: [DecidableEq α] {g : γ -> α} {s : 有限集 γ} [hi : Std.IdempotentOp op]
  证明: by
  induction s using Finset.cons_induction with
  | empty => rw [fold_empty, image_empty, fold_empty]
  | cons x xs hx ih =>
    have := Classical.decEq γ
    rw [fold_cons]; rw [cons_eq_insert]; rw [image_insert]; rw [fold_insert_idem]; rw [ih]
    simp only [Function.comp_apply]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.cons_induction, Function, Function.comp_apply, comp_apply, cons_eq_insert, cons_induction, fold_cons, fold_empty, fold_insert_idem, image_empty, image_insert
-/
theorem fold_image_idem [DecidableEq α] {g : γ -> α} {s : Finset γ} [hi : Std.IdempotentOp op] :
    (image g s).fold op b f = s.fold op b (f ∘ g) := by
  induction s using Finset.cons_induction with
  | empty => rw [fold_empty, image_empty, fold_empty]
  | cons x xs hx ih =>
    have := Classical.decEq γ
    rw [fold_cons]; rw [cons_eq_insert]; rw [image_insert]; rw [fold_insert_idem]; rw [ih]
    simp only [Function.comp_apply]

/--
theorem `fold_ite'` / 定理 `fold_ite'`

English:
theorem fold_ite'
  given: {g : α -> β} (hb : op b b = b) (p : α -> Prop) [DecidablePred p]
  proof: by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hb]
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx]
      split_ifs with h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬ p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]

中文:
定理 fold_ite'
  条件: {g : α -> β} (hb : op b b = b) (p : α -> 命题) [DecidablePred p]
  证明: by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hb]
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx]
      split_ifs with h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬ p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]

Depends on / 依赖: Finset, Finset.filter, Finset.filter_insert, Finset.fold_insert, Finset.induction_on, classical, filter, filter_insert, fold_insert, ha.assoc, hc.comm, induction_on, insert, split_ifs
-/
theorem fold_ite' {g : α -> β} (hb : op b b = b) (p : α -> Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hb]
    | insert x s hx IH =>
      simp only [Finset.fold_insert hx]
      split_ifs with h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬ p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]

/--
theorem `fold_ite` / 定理 `fold_ite`

English:
theorem fold_ite
  given: [Std.IdempotentOp op] {g : α -> β} (p : α -> Prop) [DecidablePred p]
  proof: fold_ite' (Std.IdempotentOp.idempotent _) _

中文:
定理 fold_ite
  条件: [Std.IdempotentOp op] {g : α -> β} (p : α -> 命题) [DecidablePred p]
  证明: fold_ite' (Std.IdempotentOp.idempotent _) _

Depends on / 依赖: IdempotentOp, Std.IdempotentOp.idempotent, fold_ite, idempotent
-/
theorem fold_ite [Std.IdempotentOp op] {g : α -> β} (p : α -> Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  fold_ite' (Std.IdempotentOp.idempotent _) _

/--
theorem `fold_op_rel_iff_and` / 定理 `fold_op_rel_iff_and`

English:
theorem fold_op_rel_iff_and
  statement: {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z)
  proof: by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← and_assoc]; rw [@and_comm (r c (f a))]; rw [and_assoc]
      simp

中文:
定理 fold_op_rel_iff_and
  结论: {r : β -> β -> 命题} (hr : 对任意 {x y z}, r x (op y z) ↔ r x y ∧ r x z)
  证明: by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← and_assoc]; rw [@and_comm (r c (f a))]; rw [and_assoc]
      simp

Depends on / 依赖: Finset, Finset.fold_insert, Finset.induction_on, and_assoc, and_comm, classical, fold_insert, induction_on, insert
-/
theorem fold_op_rel_iff_and {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∧ forall x in s, r c (f x) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← and_assoc]; rw [@and_comm (r c (f a))]; rw [and_assoc]
      simp

/--
theorem `fold_op_rel_iff_or` / 定理 `fold_op_rel_iff_or`

English:
theorem fold_op_rel_iff_or
  statement: {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z) ↔ r x y ∨ r x z)
  proof: by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← or_assoc]; rw [@or_comm (r c (f a))]; rw [or_assoc]
      simp

@[simp]

中文:
定理 fold_op_rel_iff_or
  结论: {r : β -> β -> 命题} (hr : 对任意 {x y z}, r x (op y z) ↔ r x y ∨ r x z)
  证明: by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← or_assoc]; rw [@or_comm (r c (f a))]; rw [or_assoc]
      simp

@[simp]

Depends on / 依赖: Finset, Finset.fold_insert, Finset.induction_on, classical, fold_insert, induction_on, insert, or_assoc, or_comm
-/
theorem fold_op_rel_iff_or {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z) ↔ r x y ∨ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∨ exists x in s, r c (f x) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha]; rw [hr]; rw [IH]; rw [← or_assoc]; rw [@or_comm (r c (f a))]; rw [or_assoc]
      simp

@[simp]
/--
theorem `fold_union_empty_singleton` / 定理 `fold_union_empty_singleton`

English:
theorem fold_union_empty_singleton
  given: [DecidableEq α] (s : Finset α)
  proof: by
  induction s using Finset.induction_on with
  | empty => simp only [fold_empty]
  | insert a s has ih => rw [fold_insert has, ih, insert_eq]

中文:
定理 fold_union_empty_singleton
  条件: [DecidableEq α] (s : 有限集 α)
  证明: by
  induction s using Finset.induction_on with
  | empty => simp only [fold_empty]
  | insert a s has ih => rw [fold_insert has, ih, insert_eq]

Depends on / 依赖: Finset, Finset.induction_on, fold_empty, fold_insert, induction_on, insert, insert_eq
-/
theorem fold_union_empty_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· union ·) ∅ singleton s = s := by
  induction s using Finset.induction_on with
  | empty => simp only [fold_empty]
  | insert a s has ih => rw [fold_insert has, ih, insert_eq]

/--
theorem `fold_sup_bot_singleton` / 定理 `fold_sup_bot_singleton`

English:
theorem fold_sup_bot_singleton
  given: [DecidableEq α] (s : Finset α)
  proof: fold_union_empty_singleton s

中文:
定理 fold_sup_bot_singleton
  条件: [DecidableEq α] (s : 有限集 α)
  证明: fold_union_empty_singleton s

Depends on / 依赖: fold_union_empty_singleton
-/
theorem fold_sup_bot_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ⊔ ·) ⊥ singleton s = s :=
  fold_union_empty_singleton s

section Order

variable [LinearOrder β] (c : β)

/--
theorem `le_fold_min` / 定理 `le_fold_min`

English:
theorem le_fold_min
  statement: c <= s.fold min b f ↔ c <= b ∧ forall x in s, c <= f x
  proof: fold_op_rel_iff_and le_min_iff

中文:
定理 le_fold_min
  结论: c <= s.fold 最小值 b f ↔ c <= b ∧ 对任意 x in s, c <= f x
  证明: fold_op_rel_iff_and le_min_iff

Depends on / 依赖: fold_op_rel_iff_and, le_min_iff
-/
theorem le_fold_min : c <= s.fold min b f ↔ c <= b ∧ forall x in s, c <= f x :=
  fold_op_rel_iff_and le_min_iff

/--
theorem `fold_min_le` / 定理 `fold_min_le`

English:
theorem fold_min_le
  statement: s.fold min b f <= c ↔ b <= c ∨ exists x in s, f x <= c
  proof: by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ <= _ ↔ _
  exact min_le_iff

中文:
定理 fold_min_le
  结论: s.fold 最小值 b f <= c ↔ b <= c ∨ 存在 x in s, f x <= c
  证明: by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ <= _ ↔ _
  exact min_le_iff

Depends on / 依赖: fold_op_rel_iff_or, min_le_iff
-/
theorem fold_min_le : s.fold min b f <= c ↔ b <= c ∨ exists x in s, f x <= c := by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ <= _ ↔ _
  exact min_le_iff

/--
theorem `lt_fold_min` / 定理 `lt_fold_min`

English:
theorem lt_fold_min
  statement: c < s.fold min b f ↔ c < b ∧ forall x in s, c < f x
  proof: fold_op_rel_iff_and lt_min_iff

中文:
定理 lt_fold_min
  结论: c < s.fold 最小值 b f ↔ c < b ∧ 对任意 x in s, c < f x
  证明: fold_op_rel_iff_and lt_min_iff

Depends on / 依赖: fold_op_rel_iff_and, lt_min_iff
-/
theorem lt_fold_min : c < s.fold min b f ↔ c < b ∧ forall x in s, c < f x :=
  fold_op_rel_iff_and lt_min_iff

/--
theorem `fold_min_lt` / 定理 `fold_min_lt`

English:
theorem fold_min_lt
  statement: s.fold min b f < c ↔ b < c ∨ exists x in s, f x < c
  proof: by
  change _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ < _ ↔ _
  exact min_lt_iff

中文:
定理 fold_min_lt
  结论: s.fold 最小值 b f < c ↔ b < c ∨ 存在 x in s, f x < c
  证明: by
  change _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ < _ ↔ _
  exact min_lt_iff

Depends on / 依赖: fold_op_rel_iff_or, min_lt_iff
-/
theorem fold_min_lt : s.fold min b f < c ↔ b < c ∨ exists x in s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ < _ ↔ _
  exact min_lt_iff

/--
theorem `fold_max_le` / 定理 `fold_max_le`

English:
theorem fold_max_le
  statement: s.fold max b f <= c ↔ b <= c ∧ forall x in s, f x <= c
  proof: by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ <= _ ↔ _
  exact max_le_iff

中文:
定理 fold_max_le
  结论: s.fold 最大值 b f <= c ↔ b <= c ∧ 对任意 x in s, f x <= c
  证明: by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ <= _ ↔ _
  exact max_le_iff

Depends on / 依赖: fold_op_rel_iff_and, max_le_iff
-/
theorem fold_max_le : s.fold max b f <= c ↔ b <= c ∧ forall x in s, f x <= c := by
  change _ >= _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ <= _ ↔ _
  exact max_le_iff

/--
theorem `le_fold_max` / 定理 `le_fold_max`

English:
theorem le_fold_max
  statement: c <= s.fold max b f ↔ c <= b ∨ exists x in s, c <= f x
  proof: fold_op_rel_iff_or le_max_iff

中文:
定理 le_fold_max
  结论: c <= s.fold 最大值 b f ↔ c <= b ∨ 存在 x in s, c <= f x
  证明: fold_op_rel_iff_or le_max_iff

Depends on / 依赖: fold_op_rel_iff_or, le_max_iff
-/
theorem le_fold_max : c <= s.fold max b f ↔ c <= b ∨ exists x in s, c <= f x :=
  fold_op_rel_iff_or le_max_iff

/--
theorem `fold_max_lt` / 定理 `fold_max_lt`

English:
theorem fold_max_lt
  statement: s.fold max b f < c ↔ b < c ∧ forall x in s, f x < c
  proof: by
  change _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ < _ ↔ _
  exact max_lt_iff

中文:
定理 fold_max_lt
  结论: s.fold 最大值 b f < c ↔ b < c ∧ 对任意 x in s, f x < c
  证明: by
  change _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ < _ ↔ _
  exact max_lt_iff

Depends on / 依赖: fold_op_rel_iff_and, max_lt_iff
-/
theorem fold_max_lt : s.fold max b f < c ↔ b < c ∧ forall x in s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ < _ ↔ _
  exact max_lt_iff

/--
theorem `lt_fold_max` / 定理 `lt_fold_max`

English:
theorem lt_fold_max
  statement: c < s.fold max b f ↔ c < b ∨ exists x in s, c < f x
  proof: fold_op_rel_iff_or lt_max_iff

中文:
定理 lt_fold_max
  结论: c < s.fold 最大值 b f ↔ c < b ∨ 存在 x in s, c < f x
  证明: fold_op_rel_iff_or lt_max_iff

Depends on / 依赖: fold_op_rel_iff_or, lt_max_iff
-/
theorem lt_fold_max : c < s.fold max b f ↔ c < b ∨ exists x in s, c < f x :=
  fold_op_rel_iff_or lt_max_iff

end Order

end Fold

end Finset
