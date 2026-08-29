/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Order.SuccPred.Archimedean

/-!
# Relations on types with a `SuccOrder`

This file contains properties about relations on types with a `SuccOrder`
and their closure operations (like the transitive closure).
-/

public section

open Function Order Relation Set

section PartialSucc

variable {α : Type*} [PartialOrder α] [SuccOrder α] [IsSuccArchimedean α]

/--
theorem `reflTransGen_of_succ_of_le` / 定理 `reflTransGen_of_succ_of_le`

English:
theorem reflTransGen_of_succ_of_le
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ico n m, r i (succ i))
  proof: by
  revert h; refine Succ.rec ?_ ?_ hnm
  · intro _
    exact ReflTransGen.refl
  · intro m hnm ih h
have : ReflTransGen r n m := ih fun i hi => h i ⟨hi.1, hi.2.trans_le le_succ m⟩
    rcases (le_succ m).eq_or_lt with hm | hm
    · rwa [← hm]
    exact this.tail (h m ⟨hnm, hm⟩)

中文:
定理 reflTransGen_of_succ_of_le
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左闭右开区间 n m, r i (succ i))
  证明: by
  revert h; refine Succ.rec ?_ ?_ hnm
  · intro _
    exact ReflTransGen.refl
  · intro m hnm ih h
have : ReflTransGen r n m := ih fun i hi => h i ⟨hi.1, hi.2.trans_le le_succ m⟩
    rcases (le_succ m).eq_or_lt with hm | hm
    · rwa [← hm]
    exact this.tail (h m ⟨hnm, hm⟩)

Depends on / 依赖: ReflTransGen, ReflTransGen.refl, Succ.rec, eq_or_lt, le_succ, revert, this.tail, trans_le
-/
theorem reflTransGen_of_succ_of_le (r : α -> α -> Prop) {n m : α} (h : forall i in Ico n m, r i (succ i))
    (hnm : n <= m) : ReflTransGen r n m := by
  revert h; refine Succ.rec ?_ ?_ hnm
  · intro _
    exact ReflTransGen.refl
  · intro m hnm ih h
have : ReflTransGen r n m := ih fun i hi => h i ⟨hi.1, hi.2.trans_le le_succ m⟩
    rcases (le_succ m).eq_or_lt with hm | hm
    · rwa [← hm]
    exact this.tail (h m ⟨hnm, hm⟩)

/--
theorem `reflTransGen_of_succ_of_ge` / 定理 `reflTransGen_of_succ_of_ge`

English:
theorem reflTransGen_of_succ_of_ge
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ico m n, r (succ i) i)
  proof: by
  rw [← reflTransGen_swap]
  exact reflTransGen_of_succ_of_le (swap r) h hmn

中文:
定理 reflTransGen_of_succ_of_ge
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左闭右开区间 m n, r (succ i) i)
  证明: by
  rw [← reflTransGen_swap]
  exact reflTransGen_of_succ_of_le (swap r) h hmn

Depends on / 依赖: reflTransGen_of_succ_of_le, reflTransGen_swap
-/
theorem reflTransGen_of_succ_of_ge (r : α -> α -> Prop) {n m : α} (h : forall i in Ico m n, r (succ i) i)
    (hmn : m <= n) : ReflTransGen r n m := by
  rw [← reflTransGen_swap]
  exact reflTransGen_of_succ_of_le (swap r) h hmn

/--
theorem `transGen_of_succ_of_lt` / 定理 `transGen_of_succ_of_lt`

English:
theorem transGen_of_succ_of_lt
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ico n m, r i (succ i))
  proof: (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_le r h hnm.le).resolve_left
    hnm.ne'

中文:
定理 transGen_of_succ_of_lt
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左闭右开区间 n m, r i (succ i))
  证明: (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_le r h hnm.le).resolve_left
    hnm.ne'

Depends on / 依赖: hnm.le, hnm.ne, reflTransGen_iff_eq_or_transGen, reflTransGen_iff_eq_or_transGen.mp, reflTransGen_of_succ_of_le, resolve_left
-/
theorem transGen_of_succ_of_lt (r : α -> α -> Prop) {n m : α} (h : forall i in Ico n m, r i (succ i))
    (hnm : n < m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_le r h hnm.le).resolve_left
    hnm.ne'

/--
theorem `transGen_of_succ_of_gt` / 定理 `transGen_of_succ_of_gt`

English:
theorem transGen_of_succ_of_gt
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ico m n, r (succ i) i)
  proof: (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_ge r h hmn.le).resolve_left
    hmn.ne

中文:
定理 transGen_of_succ_of_gt
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左闭右开区间 m n, r (succ i) i)
  证明: (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_ge r h hmn.le).resolve_left
    hmn.ne

Depends on / 依赖: hmn.le, hmn.ne, reflTransGen_iff_eq_or_transGen, reflTransGen_iff_eq_or_transGen.mp, reflTransGen_of_succ_of_ge, resolve_left
-/
theorem transGen_of_succ_of_gt (r : α -> α -> Prop) {n m : α} (h : forall i in Ico m n, r (succ i) i)
    (hmn : m < n) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_ge r h hmn.le).resolve_left
    hmn.ne

end PartialSucc

section LinearSucc

variable {α : Type*} [LinearOrder α] [SuccOrder α] [IsSuccArchimedean α]

/--
theorem `reflTransGen_of_succ` / 定理 `reflTransGen_of_succ`

English:
theorem reflTransGen_of_succ
  statement: (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ico n m, r i (succ i))
  proof: (le_total n m).elim (reflTransGen_of_succ_of_le r h1) reflTransGen_of_succ_of_ge r h2

中文:
定理 reflTransGen_of_succ
  结论: (r : α -> α -> 命题) {n m : α} (h1 : 对任意 i in 左闭右开区间 n m, r i (succ i))
  证明: (le_total n m).elim (reflTransGen_of_succ_of_le r h1) reflTransGen_of_succ_of_ge r h2

Depends on / 依赖: le_total, reflTransGen_of_succ_of_ge, reflTransGen_of_succ_of_le
-/
theorem reflTransGen_of_succ (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ico n m, r i (succ i))
    (h2 : forall i in Ico m n, r (succ i) i) : ReflTransGen r n m :=
(le_total n m).elim (reflTransGen_of_succ_of_le r h1) reflTransGen_of_succ_of_ge r h2

/--
theorem `transGen_of_succ_of_ne` / 定理 `transGen_of_succ_of_ne`

English:
theorem transGen_of_succ_of_ne
  statement: (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ico n m, r i (succ i))
  proof: (reflTransGen_iff_eq_or_transGen.mp (reflTransGen_of_succ r h1 h2)).resolve_left hnm.symm

中文:
定理 transGen_of_succ_of_ne
  结论: (r : α -> α -> 命题) {n m : α} (h1 : 对任意 i in 左闭右开区间 n m, r i (succ i))
  证明: (reflTransGen_iff_eq_or_transGen.mp (reflTransGen_of_succ r h1 h2)).resolve_left hnm.symm

Depends on / 依赖: hnm.symm, reflTransGen_iff_eq_or_transGen, reflTransGen_iff_eq_or_transGen.mp, reflTransGen_of_succ, resolve_left
-/
theorem transGen_of_succ_of_ne (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ico n m, r i (succ i))
    (h2 : forall i in Ico m n, r (succ i) i) (hnm : n != m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp (reflTransGen_of_succ r h1 h2)).resolve_left hnm.symm

/--
theorem `transGen_of_succ_of_refl` / 定理 `transGen_of_succ_of_refl`

English:
theorem transGen_of_succ_of_refl
  statement: (r : α -> α -> Prop) {n m : α} [Std.Refl r]
  proof: by
  rcases eq_or_ne m n with (rfl | hmn); · exact TransGen.single (refl m)
  exact transGen_of_succ_of_ne r h1 h2 hmn.symm

@[deprecated (since := "2026-03-27")]
alias transGen_of_succ_of_reflexive := transGen_of_succ_of_refl

中文:
定理 transGen_of_succ_of_refl
  结论: (r : α -> α -> 命题) {n m : α} [Std.Refl r]
  证明: by
  rcases eq_or_ne m n with (rfl | hmn); · exact TransGen.single (refl m)
  exact transGen_of_succ_of_ne r h1 h2 hmn.symm

@[deprecated (since := "2026-03-27")]
alias transGen_of_succ_of_reflexive := transGen_of_succ_of_refl

Depends on / 依赖: TransGen, TransGen.single, eq_or_ne, hmn.symm, single, transGen_of_succ_of_ne
-/
theorem transGen_of_succ_of_refl (r : α -> α -> Prop) {n m : α} [Std.Refl r]
    (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i) i) : TransGen r n m := by
  rcases eq_or_ne m n with (rfl | hmn); · exact TransGen.single (refl m)
  exact transGen_of_succ_of_ne r h1 h2 hmn.symm

@[deprecated (since := "2026-03-27")]
alias transGen_of_succ_of_reflexive := transGen_of_succ_of_refl

end LinearSucc

section PartialPred

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]

/--
theorem `reflTransGen_of_pred_of_ge` / 定理 `reflTransGen_of_pred_of_ge`

English:
theorem reflTransGen_of_pred_of_ge
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc m n, r i (pred i))
  proof: reflTransGen_of_succ_of_le (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

中文:
定理 reflTransGen_of_pred_of_ge
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左开右闭区间 m n, r i (pred i))
  证明: reflTransGen_of_succ_of_le (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

Depends on / 依赖: reflTransGen_of_succ_of_le
-/
theorem reflTransGen_of_pred_of_ge (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc m n, r i (pred i))
    (hnm : m <= n) : ReflTransGen r n m :=
  reflTransGen_of_succ_of_le (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

/--
theorem `reflTransGen_of_pred_of_le` / 定理 `reflTransGen_of_pred_of_le`

English:
theorem reflTransGen_of_pred_of_le
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc n m, r (pred i) i)
  proof: reflTransGen_of_succ_of_ge (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

中文:
定理 reflTransGen_of_pred_of_le
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左开右闭区间 n m, r (pred i) i)
  证明: reflTransGen_of_succ_of_ge (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

Depends on / 依赖: reflTransGen_of_succ_of_ge
-/
theorem reflTransGen_of_pred_of_le (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc n m, r (pred i) i)
    (hmn : n <= m) : ReflTransGen r n m :=
  reflTransGen_of_succ_of_ge (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

/--
theorem `transGen_of_pred_of_gt` / 定理 `transGen_of_pred_of_gt`

English:
theorem transGen_of_pred_of_gt
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc m n, r i (pred i))
  proof: transGen_of_succ_of_lt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

中文:
定理 transGen_of_pred_of_gt
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左开右闭区间 m n, r i (pred i))
  证明: transGen_of_succ_of_lt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

Depends on / 依赖: transGen_of_succ_of_lt
-/
theorem transGen_of_pred_of_gt (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc m n, r i (pred i))
    (hnm : m < n) : TransGen r n m :=
  transGen_of_succ_of_lt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

/--
theorem `transGen_of_pred_of_lt` / 定理 `transGen_of_pred_of_lt`

English:
theorem transGen_of_pred_of_lt
  statement: (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc n m, r (pred i) i)
  proof: transGen_of_succ_of_gt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

中文:
定理 transGen_of_pred_of_lt
  结论: (r : α -> α -> 命题) {n m : α} (h : 对任意 i in 左开右闭区间 n m, r (pred i) i)
  证明: transGen_of_succ_of_gt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

Depends on / 依赖: transGen_of_succ_of_gt
-/
theorem transGen_of_pred_of_lt (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc n m, r (pred i) i)
    (hmn : n < m) : TransGen r n m :=
  transGen_of_succ_of_gt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

end PartialPred

section LinearPred

variable {α : Type*} [LinearOrder α] [PredOrder α] [IsPredArchimedean α]

/--
theorem `reflTransGen_of_pred` / 定理 `reflTransGen_of_pred`

English:
theorem reflTransGen_of_pred
  statement: (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ioc m n, r i (pred i))
  proof: reflTransGen_of_succ (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩) fun x hx =>
    h2 x ⟨hx.2, hx.1⟩

中文:
定理 reflTransGen_of_pred
  结论: (r : α -> α -> 命题) {n m : α} (h1 : 对任意 i in 左开右闭区间 m n, r i (pred i))
  证明: reflTransGen_of_succ (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩) fun x hx =>
    h2 x ⟨hx.2, hx.1⟩

Depends on / 依赖: reflTransGen_of_succ
-/
theorem reflTransGen_of_pred (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ioc m n, r i (pred i))
    (h2 : forall i in Ioc n m, r (pred i) i) : ReflTransGen r n m :=
  reflTransGen_of_succ (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩) fun x hx =>
    h2 x ⟨hx.2, hx.1⟩

/--
theorem `transGen_of_pred_of_ne` / 定理 `transGen_of_pred_of_ne`

English:
theorem transGen_of_pred_of_ne
  statement: (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ioc m n, r i (pred i))
  proof: transGen_of_succ_of_ne (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    (fun x hx => h2 x ⟨hx.2, hx.1⟩) hnm

中文:
定理 transGen_of_pred_of_ne
  结论: (r : α -> α -> 命题) {n m : α} (h1 : 对任意 i in 左开右闭区间 m n, r i (pred i))
  证明: transGen_of_succ_of_ne (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    (fun x hx => h2 x ⟨hx.2, hx.1⟩) hnm

Depends on / 依赖: transGen_of_succ_of_ne
-/
theorem transGen_of_pred_of_ne (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ioc m n, r i (pred i))
    (h2 : forall i in Ioc n m, r (pred i) i) (hnm : n != m) : TransGen r n m :=
  transGen_of_succ_of_ne (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    (fun x hx => h2 x ⟨hx.2, hx.1⟩) hnm

/--
theorem `transGen_of_pred_of_refl` / 定理 `transGen_of_pred_of_refl`

English:
theorem transGen_of_pred_of_refl
  statement: (r : α -> α -> Prop) {n m : α} [Std.Refl r]
  proof: @transGen_of_succ_of_refl αᵒᵈ _ _ _ r _ _ ‹_› (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    fun x hx => h2 x ⟨hx.2, hx.1⟩

@[deprecated (since := "2026-03-27")]
alias transGen_of_pred_of_reflexive := transGen_of_pred_of_refl

中文:
定理 transGen_of_pred_of_refl
  结论: (r : α -> α -> 命题) {n m : α} [Std.Refl r]
  证明: @transGen_of_succ_of_refl αᵒᵈ _ _ _ r _ _ ‹_› (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    fun x hx => h2 x ⟨hx.2, hx.1⟩

@[deprecated (since := "2026-03-27")]
alias transGen_of_pred_of_reflexive := transGen_of_pred_of_refl

Depends on / 依赖: transGen_of_succ_of_refl
-/
theorem transGen_of_pred_of_refl (r : α -> α -> Prop) {n m : α} [Std.Refl r]
    (h1 : forall i in Ioc m n, r i (pred i)) (h2 : forall i in Ioc n m, r (pred i) i) : TransGen r n m :=
  @transGen_of_succ_of_refl αᵒᵈ _ _ _ r _ _ ‹_› (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    fun x hx => h2 x ⟨hx.2, hx.1⟩

@[deprecated (since := "2026-03-27")]
alias transGen_of_pred_of_reflexive := transGen_of_pred_of_refl

end LinearPred
