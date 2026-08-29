/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.SuccPred.Basic

/-!
# Archimedean successor and predecessor

* `IsSuccArchimedean`: `SuccOrder` where `succ` iterated to an element gives all the greater
  ones.
* `IsPredArchimedean`: `PredOrder` where `pred` iterated to an element gives all the smaller
  ones.
-/

public section

variable {α β : Type*}

open Order Function

/--
Definition of `IsSuccArchimedean` / `IsSuccArchimedean` 的定义

English:
class IsSuccArchimedean
  parameters: (α : Type*) [Preorder α] [SuccOrder α]
  axioms and operations (1):
    - exists_succ_iterate_of_le({a b : α} (h : a <= b)) : exists n, succ^[n] a = b

中文:
类 IsSuccArchimedean
  参数: (α : 类型) [Preorder α] [SuccOrder α]
  公理与运算 (1 个):
    - exists_succ_iterate_of_le({a b : α} (h : a <= b)) : 存在 n, succ^[n] a = b
-/
class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `a` from `b` by iterating `succ` -/
  exists_succ_iterate_of_le {a b : α} (h : a <= b) : exists n, succ^[n] a = b

/-- A `PredOrder` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
@[to_dual existing]
/--
Definition of `IsPredArchimedean` / `IsPredArchimedean` 的定义

English:
class IsPredArchimedean
  parameters: (α : Type*) [Preorder α] [PredOrder α]
  axioms and operations (1):
    - exists_pred_iterate_of_le({a b : α} (h : a <= b)) : exists n, pred^[n] b = a

中文:
类 IsPredArchimedean
  参数: (α : 类型) [Preorder α] [PredOrder α]
  公理与运算 (1 个):
    - exists_pred_iterate_of_le({a b : α} (h : a <= b)) : 存在 n, pred^[n] b = a
-/
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `b` from `a` by iterating `pred` -/
  exists_pred_iterate_of_le {a b : α} (h : a <= b) : exists n, pred^[n] b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)
export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

-- `to_dual` cannot yet reorder arguments of arguments
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SuccOrder
  signature: α] [IsSuccArchimedean α] : IsPredArchimedean αᵒᵈ
  body: ⟨fun {a b} h => by convert! exists_succ_iterate_of_le h.ofDual⟩

@[to_dual existing]

中文:
实例 [SuccOrder
  签名: α] [IsSuccArchimedean α] : IsPredArchimedean αᵒᵈ
  定义体: ⟨fun {a b} h => by convert! exists_succ_iterate_of_le h.ofDual⟩

@[to_dual existing]

Depends on / 依赖: convert, exists_succ_iterate_of_le, h.ofDual, ofDual
-/
instance [SuccOrder α] [IsSuccArchimedean α] : IsPredArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert! exists_succ_iterate_of_le h.ofDual⟩

@[to_dual existing]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PredOrder
  signature: α] [IsPredArchimedean α] : IsSuccArchimedean αᵒᵈ
  body: ⟨fun {a b} h => by convert! exists_pred_iterate_of_le h.ofDual⟩

中文:
实例 [PredOrder
  签名: α] [IsPredArchimedean α] : IsSuccArchimedean αᵒᵈ
  定义体: ⟨fun {a b} h => by convert! exists_pred_iterate_of_le h.ofDual⟩

Depends on / 依赖: convert, exists_pred_iterate_of_le, h.ofDual, ofDual
-/
instance [PredOrder α] [IsPredArchimedean α] : IsSuccArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert! exists_pred_iterate_of_le h.ofDual⟩

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

@[to_dual]
/--
theorem `LE.le.exists_succ_iterate` / 定理 `LE.le.exists_succ_iterate`

English:
theorem LE.le.exists_succ_iterate
  given: (h : a <= b)
  statement: exists n, succ^[n] a = b
  proof: exists_succ_iterate_of_le h

@[to_dual]

中文:
定理 LE.le.exists_succ_iterate
  条件: (h : a <= b)
  结论: 存在 n, succ^[n] a = b
  证明: exists_succ_iterate_of_le h

@[to_dual]

Depends on / 依赖: exists_succ_iterate_of_le
-/
theorem LE.le.exists_succ_iterate (h : a <= b) : exists n, succ^[n] a = b :=
  exists_succ_iterate_of_le h

@[to_dual]
/--
theorem `exists_succ_iterate_iff_le` / 定理 `exists_succ_iterate_iff_le`

English:
theorem exists_succ_iterate_iff_le
  statement: (exists n, succ^[n] a = b) ↔ a <= b
  proof: by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

中文:
定理 exists_succ_iterate_iff_le
  结论: (存在 n, succ^[n] a = b) ↔ a <= b
  证明: by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

Depends on / 依赖: exists_succ_iterate_of_le, id_le_iterate_of_id_le, le_succ
-/
theorem exists_succ_iterate_iff_le : (exists n, succ^[n] a = b) ↔ a <= b := by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

-- TODO: rename to `Order.succ_rec`?
/-- Induction principle on a type with a `SuccOrder` for all elements above a given element `m`. -/
@[to_dual (attr := elab_as_elim) Pred.rec
/-- Induction principle on a type with a `PredOrder` for all elements below a given element `m`. -/]
/--
theorem `Succ.rec` / 定理 `Succ.rec`

English:
theorem Succ.rec
  statement: {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_rfl)
  proof: by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp_rw [Function.iterate_succ_apply']
    exact succ _ (id_le_iterate_of_id_le le_succ n m) (ih _)

@[to_dual Pred.rec_iff]

中文:
定理 Succ.rec
  结论: {m : α} {P : 对任意 n, m <= n -> 命题} (rfl : P m le_rfl)
  证明: by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp_rw [Function.iterate_succ_apply']
    exact succ _ (id_le_iterate_of_id_le le_succ n m) (ih _)

@[to_dual Pred.rec_iff]

Depends on / 依赖: Function, Function.iterate_succ_apply, exists_succ_iterate, hmn.exists_succ_iterate, id_le_iterate_of_id_le, iterate_succ_apply, le_succ, simp_rw
-/
theorem Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_rfl)
    (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_succ _)) ⦃n : α⦄
    (hmn : m <= n) : P n hmn := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp_rw [Function.iterate_succ_apply']
    exact succ _ (id_le_iterate_of_id_le le_succ n m) (ih _)

@[to_dual Pred.rec_iff]
/--
theorem `Succ.rec_iff` / 定理 `Succ.rec_iff`

English:
theorem Succ.rec_iff
  given: {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) {a b : α} (h : a <= b)
  proof: by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) Iff.rfl (fun c hc => hc.trans (hsucc _)) n

@[to_dual le_total_of_directed]

中文:
定理 Succ.rec_iff
  条件: {p : α -> 命题} (hsucc : 对任意 a, p a ↔ p (succ a)) {a b : α} (h : a <= b)
  证明: by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) Iff.rfl (fun c hc => hc.trans (hsucc _)) n

@[to_dual le_total_of_directed]

Depends on / 依赖: Iff.rfl, Iterate, Iterate.rec, exists_succ_iterate, h.exists_succ_iterate, hc.trans
-/
theorem Succ.rec_iff {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) {a b : α} (h : a <= b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) Iff.rfl (fun c hc => hc.trans (hsucc _)) n

@[to_dual le_total_of_directed]
/--
lemma `le_total_of_codirected` / 引理 `le_total_of_codirected`

English:
lemma le_total_of_codirected
  given: {r v₁ v₂ : α} (h₁ : r <= v₁) (h₂ : r <= v₂)
  statement: v₁ <= v₂ ∨ v₂ <= v₁
  proof: by
  obtain ⟨n, rfl⟩ := h₁.exists_succ_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_succ_iterate
  clear h₁ h₂
  wlog h : n <= m
  · rw [Or.comm]
    apply this
    exact Nat.le_of_not_ge h
  left
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]; rw [Function.iterate_add]; rw [Function.c

中文:
引理 le_total_of_codirected
  条件: {r v₁ v₂ : α} (h₁ : r <= v₁) (h₂ : r <= v₂)
  结论: v₁ <= v₂ ∨ v₂ <= v₁
  证明: by
  obtain ⟨n, rfl⟩ := h₁.exists_succ_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_succ_iterate
  clear h₁ h₂
  wlog h : n <= m
  · rw [Or.comm]
    apply this
    exact Nat.le_of_not_ge h
  left
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]; rw [Function.iterate_add]; rw [Function.c

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_add, Nat.add_comm, Nat.exists_eq_add_of_le, Nat.le_of_not_ge, Or.comm, Order.le_succ_iterate, add_comm, comp_apply, exists_eq_add_of_le, exists_succ_iterate, iterate_add, le_of_not_ge, le_succ_iterate
-/
lemma le_total_of_codirected {r v₁ v₂ : α} (h₁ : r <= v₁) (h₂ : r <= v₂) : v₁ <= v₂ ∨ v₂ <= v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_succ_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_succ_iterate
  clear h₁ h₂
  wlog h : n <= m
  · rw [Or.comm]
    apply this
    exact Nat.le_of_not_ge h
  left
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]; rw [Function.iterate_add]; rw [Function.comp_apply]
  apply Order.le_succ_iterate

end SuccOrder

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual (reorder := h₁ h₂) lt_or_le_of_directed]
/--
lemma `lt_or_le_of_codirected` / 引理 `lt_or_le_of_codirected`

English:
lemma lt_or_le_of_codirected
  statement: [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r <= v₁)
  proof: by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_codirected h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

中文:
引理 lt_or_le_of_codirected
  结论: [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r <= v₁)
  证明: by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_codirected h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

Depends on / 依赖: Classical, Classical.or_iff_not_imp_right, le_total_of_codirected, lt_of_le_of_ne, ne_of_not_le, or_iff_not_imp_right
-/
lemma lt_or_le_of_codirected [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r <= v₁)
    (h₂ : r <= v₂) : v₁ < v₂ ∨ v₂ <= v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_codirected h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

-- `to_dual` cannot yet reorder arguments of arguments
-- See note [reducible non-instances]
/--
Definition of `IsSuccArchimedean.linearOrder` / `IsSuccArchimedean.linearOrder` 的定义

English:
abbreviation IsSuccArchimedean.linearOrder
  signature: [SuccOrder α] [IsSuccArchimedean α]
  body: have ⟨c, ha, hb⟩ := directed_of (· >= ·) a b
    le_total_of_codirected ha hb
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

中文:
缩写 IsSuccArchimedean.linearOrder
  签名: [SuccOrder α] [IsSuccArchimedean α]
  定义体: have ⟨c, ha, hb⟩ := directed_of (· >= ·) a b
    le_total_of_codirected ha hb
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

Depends on / 依赖: directed_of, le_total_of_codirected, toDecidableEq, toDecidableLE, toDecidableLT
-/
abbrev IsSuccArchimedean.linearOrder [SuccOrder α] [IsSuccArchimedean α]
     [DecidableEq α] [DecidableLE α] [DecidableLT α]
     [IsCodirectedOrder α] : LinearOrder α where
  le_total a b :=
    have ⟨c, ha, hb⟩ := directed_of (· >= ·) a b
    le_total_of_codirected ha hb
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non-instances]
@[to_dual existing]
/--
Definition of `IsPredArchimedean.linearOrder` / `IsPredArchimedean.linearOrder` 的定义

English:
abbreviation IsPredArchimedean.linearOrder
  signature: [PredOrder α] [IsPredArchimedean α]
  body: letI : LinearOrder αᵒᵈ := IsSuccArchimedean.linearOrder
  inferInstanceAs (LinearOrder αᵒᵈᵒᵈ)

中文:
缩写 IsPredArchimedean.linearOrder
  签名: [PredOrder α] [IsPredArchimedean α]
  定义体: letI : LinearOrder αᵒᵈ := IsSuccArchimedean.linearOrder
  inferInstanceAs (LinearOrder αᵒᵈᵒᵈ)

Depends on / 依赖: IsSuccArchimedean, IsSuccArchimedean.linearOrder, LinearOrder, linearOrder
-/
abbrev IsPredArchimedean.linearOrder [PredOrder α] [IsPredArchimedean α]
     [DecidableEq α] [DecidableLE α] [DecidableLT α]
     [IsDirectedOrder α] : LinearOrder α :=
  letI : LinearOrder αᵒᵈ := IsSuccArchimedean.linearOrder
  inferInstanceAs (LinearOrder αᵒᵈᵒᵈ)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section SuccOrder
variable [SuccOrder α]

@[deprecated (since := "2026-02-05")] alias succ_max := Order.succ_max
@[deprecated (since := "2026-02-05")] alias succ_min := Order.succ_min

@[deprecated (since := "2026-02-05")] alias pred_max := Order.pred_max
@[deprecated (since := "2026-02-05")] alias pred_min := Order.pred_min

variable [IsSuccArchimedean α] {a b : α}

@[to_dual]
/--
theorem `exists_succ_iterate_or` / 定理 `exists_succ_iterate_or`

English:
theorem exists_succ_iterate_or
  statement: (exists n, succ^[n] a = b) ∨ exists n, succ^[n] b = a
  proof: (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

@[to_dual Pred.rec_linear]

中文:
定理 exists_succ_iterate_or
  结论: (存在 n, succ^[n] a = b) ∨ 存在 n, succ^[n] b = a
  证明: (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

@[to_dual Pred.rec_linear]

Depends on / 依赖: exists_succ_iterate_of_le, le_total
-/
theorem exists_succ_iterate_or : (exists n, succ^[n] a = b) ∨ exists n, succ^[n] b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

@[to_dual Pred.rec_linear]
/--
theorem `Succ.rec_linear` / 定理 `Succ.rec_linear`

English:
theorem Succ.rec_linear
  given: {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) (a b : α)
  statement: p a ↔ p b
  proof: (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

中文:
定理 Succ.rec_linear
  条件: {p : α -> 命题} (hsucc : 对任意 a, p a ↔ p (succ a)) (a b : α)
  结论: p a ↔ p b
  证明: (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

Depends on / 依赖: Succ.rec_iff, le_total, rec_iff
-/
theorem Succ.rec_linear {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

end LinearOrder

section bdd_range
variable [Preorder α] [Nonempty α] [Preorder β] {f : α -> β}

@[to_dual]
/--
lemma `StrictMono.not_bddAbove_range_of_isSuccArchimedean` / 引理 `StrictMono.not_bddAbove_range_of_isSuccArchimedean`

English:
lemma StrictMono.not_bddAbove_range_of_isSuccArchimedean
  statement: [NoMaxOrder α] [SuccOrder β]
  proof: by
  rintro ⟨m, hm⟩
have hm' : forall a, f a <= m := fun a => hm Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices forall b, f a₀ <= b -> exists a, b < f a by
    obtain ⟨a, ha⟩ : exists a, m < f a := this m (hm' a₀)
    exact ha.not_ge (hm' a)
  have h : forall a, exists a', f a < f a' 

中文:
引理 StrictMono.not_bddAbove_range_of_isSuccArchimedean
  结论: [NoMaxOrder α] [SuccOrder β]
  证明: by
  rintro ⟨m, hm⟩
have hm' : forall a, f a <= m := fun a => hm Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices forall b, f a₀ <= b -> exists a, b < f a by
    obtain ⟨a, ha⟩ : exists a, m < f a := this m (hm' a₀)
    exact ha.not_ge (hm' a)
  have h : forall a, exists a', f a < f a' 

Depends on / 依赖: Nonempty, Set.mem_range_self, Succ.rec, exists_gt, ha.not_ge, mem_range_self, not_ge, succ_le_of_lt, trans_lt
-/
lemma StrictMono.not_bddAbove_range_of_isSuccArchimedean [NoMaxOrder α] [SuccOrder β]
    [IsSuccArchimedean β] (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨m, hm⟩
have hm' : forall a, f a <= m := fun a => hm Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices forall b, f a₀ <= b -> exists a, b < f a by
    obtain ⟨a, ha⟩ : exists a, m < f a := this m (hm' a₀)
    exact ha.not_ge (hm' a)
  have h : forall a, exists a', f a < f a' := fun a => (exists_gt a).imp (fun a' h => hf h)
  apply Succ.rec
  · exact h a₀
  rintro b _ ⟨a, hba⟩
  exact (h a).imp (fun a' => (succ_le_of_lt hba).trans_lt)

@[to_dual]
/--
lemma `StrictAnti.not_bddAbove_range_of_isSuccArchimedean` / 引理 `StrictAnti.not_bddAbove_range_of_isSuccArchimedean`

English:
lemma StrictAnti.not_bddAbove_range_of_isSuccArchimedean
  statement: [NoMinOrder α] [SuccOrder β]
  proof: hf.dual_right.not_bddBelow_range_of_isPredArchimedean

@[deprecated (since := "2026-02-05")]
alias StrictMono.not_bddBelow_range_of_isSuccArchimedean :=
  StrictMono.not_bddAbove_range_of_isSuccArchimedean

中文:
引理 StrictAnti.not_bddAbove_range_of_isSuccArchimedean
  结论: [NoMinOrder α] [SuccOrder β]
  证明: hf.dual_right.not_bddBelow_range_of_isPredArchimedean

@[deprecated (since := "2026-02-05")]
alias StrictMono.not_bddBelow_range_of_isSuccArchimedean :=
  StrictMono.not_bddAbove_range_of_isSuccArchimedean

Depends on / 依赖: IsScalarTower, dual_right, hf.dual_right.not_bddBelow_range_of_isPredArchimedean, not_bddBelow_range_of_isPredArchimedean
-/
lemma StrictAnti.not_bddAbove_range_of_isSuccArchimedean [NoMinOrder α] [SuccOrder β]
    [IsSuccArchimedean β] (hf : StrictAnti f) : ¬ BddAbove (Set.range f) :=
  hf.dual_right.not_bddBelow_range_of_isPredArchimedean

@[deprecated (since := "2026-02-05")]
alias StrictMono.not_bddBelow_range_of_isSuccArchimedean :=
  StrictMono.not_bddAbove_range_of_isSuccArchimedean

end bdd_range

section IsWellFounded

variable [PartialOrder α]

-- `to_dual` cannot yet reorder arguments of arguments
instance (priority := 100) WellFoundedLT.toIsPredArchimedean [h : WellFoundedLT α]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun {a b} => by
    refine WellFounded.fix (C := fun b => a <= b -> exists n, Nat.iterate pred n b = a)
      h.wf ?_ b
    intro b ih hab
    replace hab := eq_or_lt_of_le hab
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
    rcases eq_or_lt_of_le (pred_le b) with hb | hb
    · cases (min_of_le_pred hb.ge).not_lt hab
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine ⟨k + 1, ?_⟩
    rw [iterate_add_apply]; rw [iterate_one]; rw [hk]⟩

@[to_dual existing]
instance (priority := 100) WellFoundedGT.toIsSuccArchimedean [h : WellFoundedGT α]
    [SuccOrder α] : IsSuccArchimedean α :=
  let h : IsPredArchimedean αᵒᵈ := by infer_instance
  ⟨h.1⟩

end IsWellFounded

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

@[to_dual Pred.rec_top]
/--
theorem `Succ.rec_bot` / 定理 `Succ.rec_bot`

English:
theorem Succ.rec_bot
  given: (p : α -> Prop) (hbot : p ⊥) (hsucc : forall a, p a -> p (succ a)) (a : α)
  statement: p a
  proof: Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ <= a)

中文:
定理 Succ.rec_bot
  条件: (p : α -> 命题) (hbot : p ⊥) (hsucc : 对任意 a, p a -> p (succ a)) (a : α)
  结论: p a
  证明: Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ <= a)

Depends on / 依赖: Succ.rec, bot_le
-/
theorem Succ.rec_bot (p : α -> Prop) (hbot : p ⊥) (hsucc : forall a, p a -> p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ <= a)

end OrderBot

@[to_dual]
/--
lemma `SuccOrder.forall_ne_bot_iff` / 引理 `SuccOrder.forall_ne_bot_iff`

English:
lemma SuccOrder.forall_ne_bot_iff
  proof: by
  refine ⟨fun h i => h _ (Order.succ_ne_bot i), fun h i hi => ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ <= i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_appl

中文:
引理 SuccOrder.forall_ne_bot_iff
  证明: by
  refine ⟨fun h i => h _ (Order.succ_ne_bot i), fun h i hi => ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ <= i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_appl

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Nat.pos_of_ne_zero, Nat.succ_pred_eq_of_pos, Order.succ_ne_bot, bot_le, comp_apply, contrapose, exists_succ_iterate_of_le, iterate_succ, pos_of_ne_zero, succ_ne_bot, succ_pred_eq_of_pos
-/
lemma SuccOrder.forall_ne_bot_iff
    [Nontrivial α] [PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]
    (P : α -> Prop) :
    (forall i, i != ⊥ -> P i) ↔ (forall i, P (SuccOrder.succ i)) := by
  refine ⟨fun h i => h _ (Order.succ_ne_bot i), fun h i hi => ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ <= i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_apply]
  apply h

section IsLeast

-- TODO: generalize to PartialOrder and `DirectedOn`
@[to_dual]
/--
lemma `BddAbove.exists_isGreatest_of_nonempty` / 引理 `BddAbove.exists_isGreatest_of_nonempty`

English:
lemma BddAbove.exists_isGreatest_of_nonempty
  statement: {X : Type*} [LinearOrder X] [SuccOrder X]
  proof: by
  obtain ⟨m, hm⟩ := hS
  obtain ⟨n, hn⟩ := hS'
  by_cases hm' : m in S
  · exact ⟨_, hm', hm⟩
  have hn' := hm hn
  revert hn hm hm'
  refine Succ.rec ?_ ?_ hn'
  · simp +contextual
  intro m _ IH hm hn hm'
  rw [mem_upperBounds] at IH hm
  simp_rw [Order.le_succ_iff_eq_or_le] at hm
  replace hm 

中文:
引理 BddAbove.exists_isGreatest_of_nonempty
  结论: {X : 类型} [LinearOrder X] [SuccOrder X]
  证明: by
  obtain ⟨m, hm⟩ := hS
  obtain ⟨n, hn⟩ := hS'
  by_cases hm' : m in S
  · exact ⟨_, hm', hm⟩
  have hn' := hm hn
  revert hn hm hm'
  refine Succ.rec ?_ ?_ hn'
  · simp +contextual
  intro m _ IH hm hn hm'
  rw [mem_upperBounds] at IH hm
  simp_rw [Order.le_succ_iff_eq_or_le] at hm
  replace hm 

Depends on / 依赖: Module, Order.le_succ_iff_eq_or_le, Succ.rec, contextual, le_succ_iff_eq_or_le, maximalIdeal, mem_upperBounds, replace, resolve_left, revert, simp_rw
-/
lemma BddAbove.exists_isGreatest_of_nonempty {X : Type*} [LinearOrder X] [SuccOrder X]
    [IsSuccArchimedean X] {S : Set X} (hS : BddAbove S) (hS' : S.Nonempty) :
    exists x, IsGreatest S x := by
  obtain ⟨m, hm⟩ := hS
  obtain ⟨n, hn⟩ := hS'
  by_cases hm' : m in S
  · exact ⟨_, hm', hm⟩
  have hn' := hm hn
  revert hn hm hm'
  refine Succ.rec ?_ ?_ hn'
  · simp +contextual
  intro m _ IH hm hn hm'
  rw [mem_upperBounds] at IH hm
  simp_rw [Order.le_succ_iff_eq_or_le] at hm
  replace hm : forall x in S, x <= m := by
    intro x hx
    refine (hm x hx).resolve_left ?_
    rintro rfl
    exact hm' hx
  by_cases hmS : m in S
  · exact ⟨m, hmS, hm⟩
  · exact IH hm hn hmS

end IsLeast

section OrderIso

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

-- `to_dual` cannot yet reorder arguments of arguments
/--
lemma `IsSuccArchimedean.of_orderIso` / 引理 `IsSuccArchimedean.of_orderIso`

English:
lemma IsSuccArchimedean.of_orderIso
  statement: [SuccOrder X] [IsSuccArchimedean X] [SuccOrder Y]
  proof: by
    refine (exists_succ_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing a with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Functio

中文:
引理 IsSuccArchimedean.of_orderIso
  结论: [SuccOrder X] [IsSuccArchimedean X] [SuccOrder Y]
  证明: by
    refine (exists_succ_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing a with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Functio

Depends on / 依赖: Ideal.Quotient.mk_surjective, IsScalarTower, IsScalarTower.toAlgHom, Quotient, mk_surjective, of_surjective, toAlgHom, toLinearMap
-/
protected lemma IsSuccArchimedean.of_orderIso [SuccOrder X] [IsSuccArchimedean X] [SuccOrder Y]
    (f : X ≃o Y) : IsSuccArchimedean Y where
  exists_succ_iterate_of_le {a b} h := by
    refine (exists_succ_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing a with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_succ]

/-- `IsPredArchimedean` transfers across equivalences between `PredOrder`s. -/
@[to_dual existing]
/--
lemma `IsPredArchimedean.of_orderIso` / 引理 `IsPredArchimedean.of_orderIso`

English:
lemma IsPredArchimedean.of_orderIso
  statement: [PredOrder X] [IsPredArchimedean X] [PredOrder Y]
  proof: by
    refine (exists_pred_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing b with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Functio

中文:
引理 IsPredArchimedean.of_orderIso
  结论: [PredOrder X] [IsPredArchimedean X] [PredOrder Y]
  证明: by
    refine (exists_pred_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing b with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Functio
-/
protected lemma IsPredArchimedean.of_orderIso [PredOrder X] [IsPredArchimedean X] [PredOrder Y]
    (f : X ≃o Y) : IsPredArchimedean Y where
  exists_pred_iterate_of_le {a b} h := by
    refine (exists_pred_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq]; rw [EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing b with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_pred]

end OrderIso

section OrdConnected

variable [PartialOrder α]

/--
Instance `Set.OrdConnected.isPredArchimedean` / 实例 `Set.OrdConnected.isPredArchimedean`

English:
instance Set.OrdConnected.isPredArchimedean
  signature: [PredOrder α] [IsPredArchimedean α]
  body: @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc => by classical
    simp only [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := hbc.exists_pred_iterate
    use n
    induction n generalizing c with
    | zero => simp_all
    | succ n hi =>
      simp_all only [Function.iterate_succ, Function.comp_apply]
      change Order.p

中文:
实例 Set.OrdConnected.isPredArchimedean
  签名: [PredOrder α] [IsPredArchimedean α]
  定义体: @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc => by classical
    simp only [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := hbc.exists_pred_iterate
    use n
    induction n generalizing c with
    | zero => simp_all
    | succ n hi =>
      simp_all only [Function.iterate_succ, Function.comp_apply]
      change Order.p

Depends on / 依赖: classical
-/
instance Set.OrdConnected.isPredArchimedean [PredOrder α] [IsPredArchimedean α]
    (s : Set α) [s.OrdConnected] : IsPredArchimedean s where
  exists_pred_iterate_of_le := @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc => by classical
    simp only [Subtype.mk_le_mk] at hbc
    obtain ⟨n, hn⟩ := hbc.exists_pred_iterate
    use n
    induction n generalizing c with
    | zero => simp_all
    | succ n hi =>
      simp_all only [Function.iterate_succ, Function.comp_apply]
      change Order.pred^[n] (dite ..) = _
      split_ifs with h
      · dsimp only at h ⊢
        apply hi _ _ _ hn
        · rw [← hn]
          apply Order.pred_iterate_le
      · have : Order.pred (⟨c, hc⟩ : s) = ⟨c, hc⟩ := by
          change dite .. = _
          simp [h]
        rw [Function.iterate_fixed]
        · simp only [Order.pred_eq_iff_isMin] at this
          apply (this.eq_of_le _).symm
          exact hbc
        · exact this

/--
Instance `Set.OrdConnected.isSuccArchimedean` / 实例 `Set.OrdConnected.isSuccArchimedean`

English:
instance Set.OrdConnected.isSuccArchimedean
  signature: [SuccOrder α] [IsSuccArchimedean α]
  body: letI : IsPredArchimedean sᵒᵈ := inferInstanceAs (IsPredArchimedean (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (IsSuccArchimedean sᵒᵈᵒᵈ)

中文:
实例 Set.OrdConnected.isSuccArchimedean
  签名: [SuccOrder α] [IsSuccArchimedean α]
  定义体: letI : IsPredArchimedean sᵒᵈ := inferInstanceAs (IsPredArchimedean (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (IsSuccArchimedean sᵒᵈᵒᵈ)

Depends on / 依赖: IsPredArchimedean, IsSuccArchimedean, OrderDual, OrderDual.ofDual, ofDual
-/
instance Set.OrdConnected.isSuccArchimedean [SuccOrder α] [IsSuccArchimedean α]
    (s : Set α) [s.OrdConnected] : IsSuccArchimedean s :=
  letI : IsPredArchimedean sᵒᵈ := inferInstanceAs (IsPredArchimedean (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (IsSuccArchimedean sᵒᵈᵒᵈ)

end OrdConnected

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccOrder
variable [SuccOrder α] [IsSuccArchimedean α] {s : Set α} {f : α -> β}

/--
lemma `monotoneOn_of_le_succ` / 引理 `monotoneOn_of_le_succ`

English:
lemma monotoneOn_of_le_succ
  statement: (hs : s.OrdConnected)
  proof: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n] a in s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n] a)
 

中文:
引理 monotoneOn_of_le_succ
  结论: (hs : s.OrdConnected)
  证明: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n] a in s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n] a)
 

Depends on / 依赖: Function, Function.iterate_succ_apply, exists_succ_iterate_of_le, iterate_succ_apply, le_succ, le_succ_iterate, succ_eq_iff_isMax
-/
lemma monotoneOn_of_le_succ (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a <= f (succ a)) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n] a in s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)

/--
lemma `antitoneOn_of_succ_le` / 引理 `antitoneOn_of_succ_le`

English:
lemma antitoneOn_of_succ_le
  statement: (hs : s.OrdConnected)
  proof: monotoneOn_of_le_succ (β := βᵒᵈ) hs hf

中文:
引理 antitoneOn_of_succ_le
  结论: (hs : s.OrdConnected)
  证明: monotoneOn_of_le_succ (β := βᵒᵈ) hs hf

Depends on / 依赖: monotoneOn_of_le_succ
-/
lemma antitoneOn_of_succ_le (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) <= f a) : AntitoneOn f s :=
  monotoneOn_of_le_succ (β := βᵒᵈ) hs hf

/--
lemma `strictMonoOn_of_lt_succ` / 引理 `strictMonoOn_of_lt_succ`

English:
lemma strictMonoOn_of_lt_succ
  statement: (hs : s.OrdConnected)
  proof: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMax_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab ha hb
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n + 1] a in s :

中文:
引理 strictMonoOn_of_lt_succ
  结论: (hs : s.OrdConnected)
  证明: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMax_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab ha hb
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n + 1] a in s :

Depends on / 依赖: Function, Function.iterate_succ_apply, exists_succ_iterate_of_le, hab.le, iterate_succ_apply, le_succ, le_succ_iterate, not_isMax_of_lt, succ_eq_iff_isMax
-/
lemma strictMonoOn_of_lt_succ (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a < f (succ a)) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMax_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab ha hb
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n + 1] a in s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n + 1] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)

/--
lemma `strictAntiOn_of_succ_lt` / 引理 `strictAntiOn_of_succ_lt`

English:
lemma strictAntiOn_of_succ_lt
  statement: (hs : s.OrdConnected)
  proof: strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf

中文:
引理 strictAntiOn_of_succ_lt
  结论: (hs : s.OrdConnected)
  证明: strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf

Depends on / 依赖: strictMonoOn_of_lt_succ
-/
lemma strictAntiOn_of_succ_lt (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) < f a) : StrictAntiOn f s :=
  strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf

/--
lemma `monotone_of_le_succ` / 引理 `monotone_of_le_succ`

English:
lemma monotone_of_le_succ
  given: (hf : forall a, ¬ IsMax a -> f a <= f (succ a))
  statement: Monotone f
  proof: by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)

中文:
引理 monotone_of_le_succ
  条件: (hf : 对任意 a, ¬ IsMax a -> f a <= f (succ a))
  结论: Monotone f
  证明: by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, monotoneOn_of_le_succ, ordConnected_univ
-/
lemma monotone_of_le_succ (hf : forall a, ¬ IsMax a -> f a <= f (succ a)) : Monotone f := by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)

/--
lemma `antitone_of_succ_le` / 引理 `antitone_of_succ_le`

English:
lemma antitone_of_succ_le
  given: (hf : forall a, ¬ IsMax a -> f (succ a) <= f a)
  statement: Antitone f
  proof: by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)

中文:
引理 antitone_of_succ_le
  条件: (hf : 对任意 a, ¬ IsMax a -> f (succ a) <= f a)
  结论: Antitone f
  证明: by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, antitoneOn_of_succ_le, ordConnected_univ
-/
lemma antitone_of_succ_le (hf : forall a, ¬ IsMax a -> f (succ a) <= f a) : Antitone f := by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)

/--
lemma `strictMono_of_lt_succ` / 引理 `strictMono_of_lt_succ`

English:
lemma strictMono_of_lt_succ
  given: (hf : forall a, ¬ IsMax a -> f a < f (succ a))
  statement: StrictMono f
  proof: by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)

中文:
引理 strictMono_of_lt_succ
  条件: (hf : 对任意 a, ¬ IsMax a -> f a < f (succ a))
  结论: StrictMono f
  证明: by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, ordConnected_univ, strictMonoOn_of_lt_succ
-/
lemma strictMono_of_lt_succ (hf : forall a, ¬ IsMax a -> f a < f (succ a)) : StrictMono f := by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)

/--
lemma `strictAnti_of_succ_lt` / 引理 `strictAnti_of_succ_lt`

English:
lemma strictAnti_of_succ_lt
  given: (hf : forall a, ¬ IsMax a -> f (succ a) < f a)
  statement: StrictAnti f
  proof: by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)

中文:
引理 strictAnti_of_succ_lt
  条件: (hf : 对任意 a, ¬ IsMax a -> f (succ a) < f a)
  结论: StrictAnti f
  证明: by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, ordConnected_univ, strictAntiOn_of_succ_lt
-/
lemma strictAnti_of_succ_lt (hf : forall a, ¬ IsMax a -> f (succ a) < f a) : StrictAnti f := by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)

end SuccOrder

section PredOrder
variable [PredOrder α] [IsPredArchimedean α] {s : Set α} {f : α -> β}

/--
lemma `monotoneOn_of_pred_le` / 引理 `monotoneOn_of_pred_le`

English:
lemma monotoneOn_of_pred_le
  statement: (hs : s.OrdConnected)
  proof: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n] b in s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n] b)
 

中文:
引理 monotoneOn_of_pred_le
  结论: (hs : s.OrdConnected)
  证明: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n] b in s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n] b)
 

Depends on / 依赖: Function, Function.iterate_succ_apply, exists_pred_iterate_of_le, iterate_succ_apply, pred_eq_iff_isMin, pred_iterate_le, pred_le
-/
lemma monotoneOn_of_pred_le (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) <= f a) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n] b in s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)

/--
lemma `antitoneOn_of_le_pred` / 引理 `antitoneOn_of_le_pred`

English:
lemma antitoneOn_of_le_pred
  statement: (hs : s.OrdConnected)
  proof: monotoneOn_of_pred_le (β := βᵒᵈ) hs hf

中文:
引理 antitoneOn_of_le_pred
  结论: (hs : s.OrdConnected)
  证明: monotoneOn_of_pred_le (β := βᵒᵈ) hs hf

Depends on / 依赖: monotoneOn_of_pred_le
-/
lemma antitoneOn_of_le_pred (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a <= f (pred a)) : AntitoneOn f s :=
  monotoneOn_of_pred_le (β := βᵒᵈ) hs hf

/--
lemma `strictMonoOn_of_pred_lt` / 引理 `strictMonoOn_of_pred_lt`

English:
lemma strictMonoOn_of_pred_lt
  statement: (hs : s.OrdConnected)
  proof: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMin_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab hb ha
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n + 1] b in s :

中文:
引理 strictMonoOn_of_pred_lt
  结论: (hs : s.OrdConnected)
  证明: by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMin_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab hb ha
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n + 1] b in s :

Depends on / 依赖: Function, Function.iterate_succ_apply, exists_pred_iterate_of_le, hab.le, iterate_succ_apply, not_isMin_of_lt, pred_eq_iff_isMin, pred_iterate_le, pred_le
-/
lemma strictMonoOn_of_pred_lt (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) < f a) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMin_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab hb ha
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n + 1] b in s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n + 1] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)

/--
lemma `strictAntiOn_of_lt_pred` / 引理 `strictAntiOn_of_lt_pred`

English:
lemma strictAntiOn_of_lt_pred
  statement: (hs : s.OrdConnected)
  proof: strictMonoOn_of_pred_lt (β := βᵒᵈ) hs hf

中文:
引理 strictAntiOn_of_lt_pred
  结论: (hs : s.OrdConnected)
  证明: strictMonoOn_of_pred_lt (β := βᵒᵈ) hs hf

Depends on / 依赖: strictMonoOn_of_pred_lt
-/
lemma strictAntiOn_of_lt_pred (hs : s.OrdConnected)
    (hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a < f (pred a)) : StrictAntiOn f s :=
  strictMonoOn_of_pred_lt (β := βᵒᵈ) hs hf

/--
lemma `monotone_of_pred_le` / 引理 `monotone_of_pred_le`

English:
lemma monotone_of_pred_le
  given: (hf : forall a, ¬ IsMin a -> f (pred a) <= f a)
  statement: Monotone f
  proof: by
  simpa using monotoneOn_of_pred_le Set.ordConnected_univ (by simpa using hf)

中文:
引理 monotone_of_pred_le
  条件: (hf : 对任意 a, ¬ IsMin a -> f (pred a) <= f a)
  结论: Monotone f
  证明: by
  simpa using monotoneOn_of_pred_le Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, monotoneOn_of_pred_le, ordConnected_univ
-/
lemma monotone_of_pred_le (hf : forall a, ¬ IsMin a -> f (pred a) <= f a) : Monotone f := by
  simpa using monotoneOn_of_pred_le Set.ordConnected_univ (by simpa using hf)

/--
lemma `antitone_of_le_pred` / 引理 `antitone_of_le_pred`

English:
lemma antitone_of_le_pred
  given: (hf : forall a, ¬ IsMin a -> f a <= f (pred a))
  statement: Antitone f
  proof: by
  simpa using antitoneOn_of_le_pred Set.ordConnected_univ (by simpa using hf)

中文:
引理 antitone_of_le_pred
  条件: (hf : 对任意 a, ¬ IsMin a -> f a <= f (pred a))
  结论: Antitone f
  证明: by
  simpa using antitoneOn_of_le_pred Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, antitoneOn_of_le_pred, ordConnected_univ
-/
lemma antitone_of_le_pred (hf : forall a, ¬ IsMin a -> f a <= f (pred a)) : Antitone f := by
  simpa using antitoneOn_of_le_pred Set.ordConnected_univ (by simpa using hf)

/--
lemma `strictMono_of_pred_lt` / 引理 `strictMono_of_pred_lt`

English:
lemma strictMono_of_pred_lt
  given: (hf : forall a, ¬ IsMin a -> f (pred a) < f a)
  statement: StrictMono f
  proof: by
  simpa using strictMonoOn_of_pred_lt Set.ordConnected_univ (by simpa using hf)

中文:
引理 strictMono_of_pred_lt
  条件: (hf : 对任意 a, ¬ IsMin a -> f (pred a) < f a)
  结论: StrictMono f
  证明: by
  simpa using strictMonoOn_of_pred_lt Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, ordConnected_univ, strictMonoOn_of_pred_lt
-/
lemma strictMono_of_pred_lt (hf : forall a, ¬ IsMin a -> f (pred a) < f a) : StrictMono f := by
  simpa using strictMonoOn_of_pred_lt Set.ordConnected_univ (by simpa using hf)

/--
lemma `strictAnti_of_lt_pred` / 引理 `strictAnti_of_lt_pred`

English:
lemma strictAnti_of_lt_pred
  given: (hf : forall a, ¬ IsMin a -> f a < f (pred a))
  statement: StrictAnti f
  proof: by
  simpa using strictAntiOn_of_lt_pred Set.ordConnected_univ (by simpa using hf)

中文:
引理 strictAnti_of_lt_pred
  条件: (hf : 对任意 a, ¬ IsMin a -> f a < f (pred a))
  结论: StrictAnti f
  证明: by
  simpa using strictAntiOn_of_lt_pred Set.ordConnected_univ (by simpa using hf)

Depends on / 依赖: Set.ordConnected_univ, ordConnected_univ, strictAntiOn_of_lt_pred
-/
lemma strictAnti_of_lt_pred (hf : forall a, ¬ IsMin a -> f a < f (pred a)) : StrictAnti f := by
  simpa using strictAntiOn_of_lt_pred Set.ordConnected_univ (by simpa using hf)

end PredOrder
end Monotone
