/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Dedup

/-!
# The fold operation for a commutative associative operation over a multiset.
-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

/-! ### fold -/


section Fold

variable (op : α -> α -> α) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/--
Definition of `fold` / `fold` 的定义

English:
definition fold
  signature: : α -> Multiset α -> α
  body: foldr op

中文:
定义 fold
  签名: : α -> Multiset α -> α
  定义体: foldr op
-/
def fold : α -> Multiset α -> α :=
  foldr op

/--
theorem `fold_eq_foldr` / 定理 `fold_eq_foldr`

English:
theorem fold_eq_foldr
  given: (b : α) (s : Multiset α)
  proof: rfl

@[simp]

中文:
定理 fold_eq_foldr
  条件: (b : α) (s : Multiset α)
  证明: rfl

@[simp]
-/
theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op b s :=
  rfl

@[simp]
/--
theorem `coe_fold_r` / 定理 `coe_fold_r`

English:
theorem coe_fold_r
  given: (b : α) (l : List α)
  statement: fold op b l = l.foldr op b
  proof: rfl

中文:
定理 coe_fold_r
  条件: (b : α) (l : 列表 α)
  结论: fold op b l = l.foldr op b
  证明: rfl
-/
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl

/--
theorem `coe_fold_l` / 定理 `coe_fold_l`

English:
theorem coe_fold_l
  given: (b : α) (l : List α)
  statement: fold op b l = l.foldl op b
  proof: (coe_foldr_swap op b l).trans by simp [hc.comm]

中文:
定理 coe_fold_l
  条件: (b : α) (l : 列表 α)
  结论: fold op b l = l.foldl op b
  证明: (coe_foldr_swap op b l).trans by simp [hc.comm]

Depends on / 依赖: coe_foldr_swap, hc.comm
-/
theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
(coe_foldr_swap op b l).trans by simp [hc.comm]

/--
theorem `fold_eq_foldl` / 定理 `fold_eq_foldl`

English:
theorem fold_eq_foldl
  given: (b : α) (s : Multiset α)
  proof: Quot.inductionOn s fun _ => coe_fold_l _ _ _

@[simp]

中文:
定理 fold_eq_foldl
  条件: (b : α) (s : Multiset α)
  证明: Quot.inductionOn s fun _ => coe_fold_l _ _ _

@[simp]

Depends on / 依赖: Quot.inductionOn, coe_fold_l, inductionOn
-/
theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op b s :=
  Quot.inductionOn s fun _ => coe_fold_l _ _ _

@[simp]
/--
theorem `fold_zero` / 定理 `fold_zero`

English:
theorem fold_zero
  given: (b : α)
  statement: (0 : Multiset α).fold op b = b
  proof: rfl

@[simp]

中文:
定理 fold_zero
  条件: (b : α)
  结论: (0 : Multiset α).fold op b = b
  证明: rfl

@[simp]
-/
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl

@[simp]
/--
theorem `fold_cons_left` / 定理 `fold_cons_left`

English:
theorem fold_cons_left
  statement: forall (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b
  proof: foldr_cons _

中文:
定理 fold_cons_left
  结论: 对任意 (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b
  证明: foldr_cons _

Depends on / 依赖: foldr_cons
-/
theorem fold_cons_left : forall (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b :=
  foldr_cons _

/--
theorem `fold_cons_right` / 定理 `fold_cons_right`

English:
theorem fold_cons_right
  given: (b a : α) (s : Multiset α)
  statement: (a ::ₘ s).fold op b = s.fold op b * a
  proof: by
  simp [hc.comm]

中文:
定理 fold_cons_right
  条件: (b a : α) (s : Multiset α)
  结论: (a ::ₘ s).fold op b = s.fold op b * a
  证明: by
  simp [hc.comm]

Depends on / 依赖: hc.comm
-/
theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b * a := by
  simp [hc.comm]

/--
theorem `fold_cons'_right` / 定理 `fold_cons'_right`

English:
theorem fold_cons'_right
  given: (b a : α) (s : Multiset α)
  statement: (a ::ₘ s).fold op b = s.fold op (b * a)
  proof: by
  rw [fold_eq_foldl]; rw [foldl_cons]; rw [← fold_eq_foldl]

中文:
定理 fold_cons'_right
  条件: (b a : α) (s : Multiset α)
  结论: (a ::ₘ s).fold op b = s.fold op (b * a)
  证明: by
  rw [fold_eq_foldl]; rw [foldl_cons]; rw [← fold_eq_foldl]

Depends on / 依赖: fold_eq_foldl, foldl_cons
-/
theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) := by
  rw [fold_eq_foldl]; rw [foldl_cons]; rw [← fold_eq_foldl]

/--
theorem `fold_cons'_left` / 定理 `fold_cons'_left`

English:
theorem fold_cons'_left
  given: (b a : α) (s : Multiset α)
  statement: (a ::ₘ s).fold op b = s.fold op (a * b)
  proof: by
  rw [fold_cons'_right]; rw [hc.comm]

中文:
定理 fold_cons'_left
  条件: (b a : α) (s : Multiset α)
  结论: (a ::ₘ s).fold op b = s.fold op (a * b)
  证明: by
  rw [fold_cons'_right]; rw [hc.comm]
-/
theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) := by
  rw [fold_cons'_right]; rw [hc.comm]

/--
theorem `fold_add` / 定理 `fold_add`

English:
theorem fold_add
  given: (b₁ b₂ : α) (s₁ s₂ : Multiset α)
  proof: Multiset.induction_on s₂
    (by rw [Multiset.add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])

中文:
定理 fold_add
  条件: (b₁ b₂ : α) (s₁ s₂ : Multiset α)
  证明: Multiset.induction_on s₂
    (by rw [Multiset.add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])

Depends on / 依赖: Multiset, Multiset.add_zero, Multiset.induction_on, _right, add_cons, add_zero, fold_cons, fold_cons_left, fold_cons_right, fold_zero, ha.assoc, hc.comm, induction_on
-/
theorem fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) :
    (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
  Multiset.induction_on s₂
    (by rw [Multiset.add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])

/--
theorem `fold_singleton` / 定理 `fold_singleton`

English:
theorem fold_singleton
  given: (b a : α)
  statement: ({a} : Multiset α).fold op b = a * b
  proof: foldr_singleton _ _ _

中文:
定理 fold_singleton
  条件: (b a : α)
  结论: ({a} : Multiset α).fold op b = a * b
  证明: foldr_singleton _ _ _

Depends on / 依赖: foldr_singleton
-/
theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b :=
  foldr_singleton _ _ _

/--
theorem `fold_distrib` / 定理 `fold_distrib`

English:
theorem fold_distrib
  given: {f g : β -> α} (u₁ u₂ : α) (s : Multiset β)
  proof: Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons]; rw [fold_cons_left]; rw [h]; rw [map_cons]; rw [fold_cons_left]; rw [map_cons]; rw [fold_cons_right]; rw [ha.assoc]; rw [← ha.assoc (g a)]; rw [hc.comm (g a)]; rw [ha.assoc]; rw [hc.comm (g a)]; rw [ha.assoc])

中文:
定理 fold_distrib
  条件: {f g : β -> α} (u₁ u₂ : α) (s : Multiset β)
  证明: Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons]; rw [fold_cons_left]; rw [h]; rw [map_cons]; rw [fold_cons_left]; rw [map_cons]; rw [fold_cons_right]; rw [ha.assoc]; rw [← ha.assoc (g a)]; rw [hc.comm (g a)]; rw [ha.assoc]; rw [hc.comm (g a)]; rw [ha.assoc])

Depends on / 依赖: Multiset, Multiset.induction_on, fold_cons_left, fold_cons_right, ha.assoc, hc.comm, induction_on, map_cons
-/
theorem fold_distrib {f g : β -> α} (u₁ u₂ : α) (s : Multiset β) :
    (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
  Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons]; rw [fold_cons_left]; rw [h]; rw [map_cons]; rw [fold_cons_left]; rw [map_cons]; rw [fold_cons_right]; rw [ha.assoc]; rw [← ha.assoc (g a)]; rw [hc.comm (g a)]; rw [ha.assoc]; rw [hc.comm (g a)]; rw [ha.assoc])

/--
theorem `fold_hom` / 定理 `fold_hom`

English:
theorem fold_hom
  statement: {op' : β -> β -> β} [Std.Commutative op'] [Std.Associative op'] {m : α -> β}
  proof: Multiset.induction_on s (by simp) (by simp +contextual [hm])

中文:
定理 fold_hom
  结论: {op' : β -> β -> β} [Std.交换 op'] [Std.结合 op'] {m : α -> β}
  证明: Multiset.induction_on s (by simp) (by simp +contextual [hm])

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem fold_hom {op' : β -> β -> β} [Std.Commutative op'] [Std.Associative op'] {m : α -> β}
    (hm : forall x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp +contextual [hm])

/--
theorem `fold_union_inter` / 定理 `fold_union_inter`

English:
theorem fold_union_inter
  given: [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α)
  proof: by
  rw [← fold_add op]; rw [union_add_inter]; rw [fold_add op]

@[simp]

中文:
定理 fold_union_inter
  条件: [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α)
  证明: by
  rw [← fold_add op]; rw [union_add_inter]; rw [fold_add op]

@[simp]

Depends on / 依赖: fold_add, union_add_inter
-/
theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
    ((s₁ union s₂).fold op b₁ * (s₁ inter s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂ := by
  rw [← fold_add op]; rw [union_add_inter]; rw [fold_add op]

@[simp]
/--
theorem `fold_dedup_idem` / 定理 `fold_dedup_idem`

English:
theorem fold_dedup_idem
  given: [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α)
  proof: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, fold_cons_left]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← ha.assoc]; rw [hi.idempotent]

中文:
定理 fold_dedup_idem
  条件: [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α)
  证明: Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, fold_cons_left]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← ha.assoc]; rw [hi.idempotent]

Depends on / 依赖: Multiset, Multiset.induction_on, cons_erase, dedup_cons_of_mem, fold_cons_left, ha.assoc, hi.idempotent, idempotent, induction_on
-/
theorem fold_dedup_idem [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a in s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, fold_cons_left]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h]; rw [fold_cons_left]; rw [← ha.assoc]; rw [hi.idempotent]

end Fold

end Multiset
