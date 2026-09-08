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

/-- A `SuccOrder` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
/-
**IsSuccArchimedean** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [inst : Preorder α] → [SuccOrder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SuccOrder` is succ-archimedean if one can go from any two comparable elements
 by iterating
`succ`
-/
class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `a` from `b` by iterating `succ` -/
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, succ^[n] a = b

/-- A `PredOrder` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
@[to_dual existing]
/-
**IsPredArchimedean** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [inst : Preorder α] → [PredOrder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PredOrder` is pred-archimedean if one can go from any two comparable elements
 by iterating
`pred`
-/
class IsPredArchimedean (α : Type*) [Preorder α] [PredOrder α] : Prop where
  /-- If `a ≤ b` then one can get to `b` from `a` by iterating `pred` -/
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, pred^[n] b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)
export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

-- `to_dual` cannot yet reorder arguments of arguments
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SuccOrder α] [IsSuccArchimedean α] : IsPredArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert! exists_succ_iterate_of_le h.ofDual⟩

@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PredOrder α] [IsPredArchimedean α] : IsSuccArchimedean αᵒᵈ :=
  ⟨fun {a b} h => by convert! exists_pred_iterate_of_le h.ofDual⟩

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

@[to_dual]
/-
**LE.le.exists_succ_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LE.le.exists_succ_iterate (h : a <= b) : exists n, succ^[n] a = b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
-/
theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, succ^[n] a = b :=
  exists_succ_iterate_of_le h

@[to_dual]
/-
**exists_succ_iterate_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_succ_iterate_iff_le : (exists n, succ^[n] a = b) ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.id_le_iterate_of_id_le`：id_le_iterate_of_id_le (h : id <= f) (n
 : Nat) : id <= f^[n]
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
-/
theorem exists_succ_iterate_iff_le : (∃ n, succ^[n] a = b) ↔ a ≤ b := by
  refine ⟨?_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

-- TODO: rename to `Order.succ_rec`?
/-- Induction principle on a type with a `SuccOrder` for all elements above a given element `m`. -/
@[to_dual (attr := elab_as_elim) Pred.rec
/-- Induction principle on a type with a `PredOrder` for all elements below a given element `m`. -/]
/-
**Succ.rec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_rfl) (succ :
 forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_succ _)) ⦃n : α
⦄ (hmn : m <= n) : P n hmn
参数：rfl : P m le_rfl；succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.t
rans <| le_succ _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LE.le.exists_succ_iterate`：LE.le.exists_succ_iterate (h : a <= b) : exis
ts n, succ^[n] a = b
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Function.id_le_iterate_of_id_le`：id_le_iterate_of_id_le (h : id <= f) (n
 : Nat) : id <= f^[n]
-/
theorem Succ.rec {m : α} {P : ∀ n, m ≤ n → Prop} (rfl : P m le_rfl)
    (succ : ∀ n (hmn : m ≤ n), P n hmn → P (succ n) (hmn.trans <| le_succ _)) ⦃n : α⦄
    (hmn : m ≤ n) : P n hmn := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp_rw [Function.iterate_succ_apply']
    exact succ _ (id_le_iterate_of_id_le le_succ n m) (ih _)

@[to_dual Pred.rec_iff]
/-
**Succ.rec_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Succ.rec_iff {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) {a b : α
} (h : a <= b) : p a ↔ p b
参数：hsucc : forall a, p a ↔ p (succ a)；h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_succ_iterate`：LE.le.exists_succ_iterate (h : a <= b) : exis
ts n, succ^[n] a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact Iterate.rec (fun b => p a ↔ p b) Iff.rfl (fun c hc => hc.trans (hsucc _)) n

@[to_dual le_total_of_directed]
/-
**le_total_of_codirected** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_total_of_codirected {r v₁ v₂ : α} (h₁ : r <= v₁) (h₂ : r <= v₂) : v₁ <=
 v₂ ∨ v₂ <= v₁
参数：h₁ : r <= v₁；h₂ : r <= v₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_succ_iterate`：LE.le.exists_succ_iterate (h : a <= b) : exis
ts n, succ^[n] a = b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Order.le_succ_iterate`：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k]
 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Nat.le_of_not_ge`：∀ {a b : ℕ}, ¬a ≥ b → a ≤ b
-/
lemma le_total_of_codirected {r v₁ v₂ : α} (h₁ : r ≤ v₁) (h₂ : r ≤ v₂) : v₁ ≤ v₂ ∨ v₂ ≤ v₁ := by
  obtain ⟨n, rfl⟩ := h₁.exists_succ_iterate
  obtain ⟨m, rfl⟩ := h₂.exists_succ_iterate
  clear h₁ h₂
  wlog h : n ≤ m
  · rw [Or.comm]
    apply this
    exact Nat.le_of_not_ge h
  left
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, Function.iterate_add, Function.comp_apply]
  apply Order.le_succ_iterate

end SuccOrder

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual (reorder := h₁ h₂) lt_or_le_of_directed]
/-
**lt_or_le_of_codirected** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lt_or_le_of_codirected [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (
h₁ : r <= v₁) (h₂ : r <= v₂) : v₁ < v₂ ∨ v₂ <= v₁
参数：h₁ : r <= v₁；h₂ : r <= v₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `le_total_of_codirected`：le_total_of_codirected {r v₁ v₂ : α} (h₁ : r <= 
v₁) (h₂ : r <= v₂) : v₁ <= v₂ ∨ v₂ <= v₁
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_not_le`：ne_of_not_le (h : ¬a <= b) : a != b
-/
lemma lt_or_le_of_codirected [SuccOrder α] [IsSuccArchimedean α] {r v₁ v₂ : α} (h₁ : r ≤ v₁)
    (h₂ : r ≤ v₂) : v₁ < v₂ ∨ v₂ ≤ v₁ := by
  rw [Classical.or_iff_not_imp_right]
  intro nh
  rcases le_total_of_codirected h₁ h₂ with h | h
  · apply lt_of_le_of_ne h (ne_of_not_le nh).symm
  · contradiction

-- `to_dual` cannot yet reorder arguments of arguments
/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non-instances]
/-
**IsSuccArchimedean.linearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsSuccArchimedean.linearOrder [SuccOrder α] [IsSuccArchimedean α] [Decidab
leEq α] [DecidableLE α] [DecidableLT α] [IsCodirectedOrder α] : LinearOrder α wh
ere le_total a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev IsSuccArchimedean.linearOrder [SuccOrder α] [IsSuccArchimedean α]
     [DecidableEq α] [DecidableLE α] [DecidableLT α]
     [IsCodirectedOrder α] : LinearOrder α where
  le_total a b :=
    have ⟨c, ha, hb⟩ := directed_of (· ≥ ·) a b
    le_total_of_codirected ha hb
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance

/--
This isn't an instance due to a loop with `LinearOrder`.
-/
-- See note [reducible non-instances]
@[to_dual existing]
/-
**IsPredArchimedean.linearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsPredArchimedean.linearOrder [PredOrder α] [IsPredArchimedean α] [Decidab
leEq α] [DecidableLE α] [DecidableLT α] [IsDirectedOrder α] : LinearOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**exists_succ_iterate_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_succ_iterate_or : (exists n, succ^[n] a = b) ∨ exists n, succ^[n] b
 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
-/
theorem exists_succ_iterate_or : (∃ n, succ^[n] a = b) ∨ ∃ n, succ^[n] b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

@[to_dual Pred.rec_linear]
/-
**Succ.rec_linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Succ.rec_linear {p : α -> Prop} (hsucc : forall a, p a ↔ p (succ a)) (a b 
: α) : p a ↔ p b
参数：hsucc : forall a, p a ↔ p (succ a)；a b : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Succ.rec_iff`：Succ.rec_iff {p : α -> Prop} (hsucc : forall a, p a ↔ p (s
ucc a)) {a b : α} (h : a <= b) : p a ↔ p b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

end LinearOrder

section bdd_range
variable [Preorder α] [Nonempty α] [Preorder β] {f : α → β}

@[to_dual]
/-
**StrictMono.not_bddAbove_range_of_isSuccArchimedean** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：StrictMono.not_bddAbove_range_of_isSuccArchimedean [NoMaxOrder α] [SuccOrd
er β] [IsSuccArchimedean β] (hf : StrictMono f) : ¬ BddAbove (Set.range f)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma StrictMono.not_bddAbove_range_of_isSuccArchimedean [NoMaxOrder α] [SuccOrder β]
    [IsSuccArchimedean β] (hf : StrictMono f) : ¬ BddAbove (Set.range f) := by
  rintro ⟨m, hm⟩
  have hm' : ∀ a, f a ≤ m := fun a ↦ hm <| Set.mem_range_self _
  obtain ⟨a₀⟩ := ‹Nonempty α›
  suffices ∀ b, f a₀ ≤ b → ∃ a, b < f a by
    obtain ⟨a, ha⟩ : ∃ a, m < f a := this m (hm' a₀)
    exact ha.not_ge (hm' a)
  have h : ∀ a, ∃ a', f a < f a' := fun a ↦ (exists_gt a).imp (fun a' h ↦ hf h)
  apply Succ.rec
  · exact h a₀
  rintro b _ ⟨a, hba⟩
  exact (h a).imp (fun a' ↦ (succ_le_of_lt hba).trans_lt)

@[to_dual]
/-
**StrictAnti.not_bddAbove_range_of_isSuccArchimedean** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：StrictAnti.not_bddAbove_range_of_isSuccArchimedean [NoMinOrder α] [SuccOrd
er β] [IsSuccArchimedean β] (hf : StrictAnti f) : ¬ BddAbove (Set.range f)
参数：hf : StrictAnti f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.not_bddBelow_range_of_isPredArchimedean`：∀ {α : Type u_1} {β 
: Type u_2} [inst : Preorder α] [Nonempty α] [inst_2 : Preorder β] {f : α → β} [
NoMinOrder α]   [inst_4 : PredOrder β] […
· 使用定理 `instIsPredArchimedeanOrderDualOfIsSuccArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : SuccOrder α] [IsSuccArchimedean α], IsPredArchimedean 
αᵒᵈ
· 使用定理 `StrictAnti.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   StrictAnti f → StrictMono (⇑OrderDual.toDual
 ∘ f)
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) WellFoundedLT.toIsPredArchimedean [h : WellFoundedLT α]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun {a b} => by
    refine WellFounded.fix (C := fun b => a ≤ b → ∃ n, Nat.iterate pred n b = a)
      h.wf ?_ b
    intro b ih hab
    replace hab := eq_or_lt_of_le hab
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
    rcases eq_or_lt_of_le (pred_le b) with hb | hb
    · cases (min_of_le_pred hb.ge).not_lt hab
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine ⟨k + 1, ?_⟩
    rw [iterate_add_apply, iterate_one, hk]⟩

@[to_dual existing]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) WellFoundedGT.toIsSuccArchimedean [h : WellFoundedGT α]
    [SuccOrder α] : IsSuccArchimedean α :=
  let h : IsPredArchimedean αᵒᵈ := by infer_instance
  ⟨h.1⟩

end IsWellFounded

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

@[to_dual Pred.rec_top]
/-
**Succ.rec_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Succ.rec_bot (p : α -> Prop) (hbot : p ⊥) (hsucc : forall a, p a -> p (suc
c a)) (a : α) : p a
参数：p : α -> Prop；hbot : p ⊥；hsucc : forall a, p a -> p (succ a)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)

end OrderBot

@[to_dual]
/-
**SuccOrder.forall_ne_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SuccOrder.forall_ne_bot_iff [Nontrivial α] [PartialOrder α] [OrderBot α] [
SuccOrder α] [IsSuccArchimedean α] (P : α -> Prop) : (forall i, i != ⊥ -> P i) ↔
 (forall i, P (SuccOrder.succ i))
参数：P : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_ne_bot`：succ_ne_bot (a : α) : succ a != ⊥
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
lemma SuccOrder.forall_ne_bot_iff
    [Nontrivial α] [PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]
    (P : α → Prop) :
    (∀ i, i ≠ ⊥ → P i) ↔ (∀ i, P (SuccOrder.succ i)) := by
  refine ⟨fun h i ↦ h _ (Order.succ_ne_bot i), fun h i hi ↦ ?_⟩
  obtain ⟨j, rfl⟩ := exists_succ_iterate_of_le (bot_le : ⊥ ≤ i)
  have hj : 0 < j := by apply Nat.pos_of_ne_zero; contrapose hi; simp [hi]
  rw [← Nat.succ_pred_eq_of_pos hj]
  simp only [Function.iterate_succ', Function.comp_apply]
  apply h

section IsLeast

-- TODO: generalize to PartialOrder and `DirectedOn`
@[to_dual]
/-
**BddAbove.exists_isGreatest_of_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.exists_isGreatest_of_nonempty {X : Type*} [LinearOrder X] [SuccOr
der X] [IsSuccArchimedean X] {S : Set X} (hS : BddAbove S) (hS' : S.Nonempty) : 
exists x, IsGreatest S x
参数：hS : BddAbove S；hS' : S.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma BddAbove.exists_isGreatest_of_nonempty {X : Type*} [LinearOrder X] [SuccOrder X]
    [IsSuccArchimedean X] {S : Set X} (hS : BddAbove S) (hS' : S.Nonempty) :
    ∃ x, IsGreatest S x := by
  obtain ⟨m, hm⟩ := hS
  obtain ⟨n, hn⟩ := hS'
  by_cases hm' : m ∈ S
  · exact ⟨_, hm', hm⟩
  have hn' := hm hn
  revert hn hm hm'
  refine Succ.rec ?_ ?_ hn'
  · simp +contextual
  intro m _ IH hm hn hm'
  rw [mem_upperBounds] at IH hm
  simp_rw [Order.le_succ_iff_eq_or_le] at hm
  replace hm : ∀ x ∈ S, x ≤ m := by
    intro x hx
    refine (hm x hx).resolve_left ?_
    rintro rfl
    exact hm' hx
  by_cases hmS : m ∈ S
  · exact ⟨m, hmS, hm⟩
  · exact IH hm hn hmS

end IsLeast

section OrderIso

variable {X Y : Type*} [PartialOrder X] [PartialOrder Y]

-- `to_dual` cannot yet reorder arguments of arguments
/-- `IsSuccArchimedean` transfers across equivalences between `SuccOrder`s. -/
/-
**IsSuccArchimedean.of_orderIso** 是 Mathlib 中的一个定理，位于命名空间 `IsSuccArchimedean`。
形式化陈述：∀ {X : Type u_3} {Y : Type u_4} [inst : PartialOrder X] [inst_1 : PartialO
rder Y] [inst_2 : SuccOrder X]   [IsSuccArchimedean X] [inst_4 : SuccOrder Y] (f
 : X ≃o Y), IsSuccArchimedean Y
参数：f : X ≃o Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.apply_eq_iff_eq`：apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x =
 e y ↔ x = y
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `OrderIso.map_succ`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : SuccOrder α] [inst_2 : PartialOrder β]   [inst_3 : SuccOrder β] (f 
: α ≃o …
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_inv_le_map_inv_iff`：map_inv_le_map_inv_iff (f : F) {a b : β} : Equiv
Like.inv f b <= EquivLike.inv f a ↔ b <= a
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β

--- 原说明 ---
`IsSuccArchimedean` transfers across equivalences between `SuccOrder`s.
-/
protected lemma IsSuccArchimedean.of_orderIso [SuccOrder X] [IsSuccArchimedean X] [SuccOrder Y]
    (f : X ≃o Y) : IsSuccArchimedean Y where
  exists_succ_iterate_of_le {a b} h := by
    refine (exists_succ_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq, EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing a with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_succ]

/-- `IsPredArchimedean` transfers across equivalences between `PredOrder`s. -/
@[to_dual existing]
/-
**IsPredArchimedean.of_orderIso** 是 Mathlib 中的一个定理，位于命名空间 `IsPredArchimedean`。
形式化陈述：∀ {X : Type u_3} {Y : Type u_4} [inst : PartialOrder X] [inst_1 : PartialO
rder Y] [inst_2 : PredOrder X]   [IsPredArchimedean X] [inst_4 : PredOrder Y] (f
 : X ≃o Y), IsPredArchimedean Y
参数：f : X ≃o Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.apply_eq_iff_eq`：apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x =
 e y ↔ x = y
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `OrderIso.map_pred`：∀ {α : Type u_1} {β : Type u_2} [inst : PartialOrder 
α] [inst_1 : PredOrder α] [inst_2 : PartialOrder β]   [inst_3 : PredOrder β] (f 
: α ≃o …
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_inv_le_map_inv_iff`：map_inv_le_map_inv_iff (f : F) {a b : β} : Equiv
Like.inv f b <= EquivLike.inv f a ↔ b <= a
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β

--- 原说明 ---
`IsPredArchimedean` transfers across equivalences between `PredOrder`s.
-/
protected lemma IsPredArchimedean.of_orderIso [PredOrder X] [IsPredArchimedean X] [PredOrder Y]
    (f : X ≃o Y) : IsPredArchimedean Y where
  exists_pred_iterate_of_le {a b} h := by
    refine (exists_pred_iterate_of_le ((map_inv_le_map_inv_iff f).mpr h)).imp ?_
    intro n
    rw [← f.apply_eq_iff_eq, EquivLike.apply_inv_apply]
    rintro rfl
    clear h
    induction n generalizing b with
    | zero => simp
    | succ n IH => simp only [Function.iterate_succ', Function.comp_apply, IH, f.map_pred]

end OrderIso

section OrdConnected

variable [PartialOrder α]

/-
**Set.OrdConnected.isPredArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.OrdConnected.isPredArchimedean [PredOrder α] [IsPredArchimedean α] (s 
: Set α) [s.OrdConnected] : IsPredArchimedean s where exists_pred_iterate_of_le
参数：s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_pred_iterate`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 
: PredOrder α] [IsPredArchimedean α] {a b : α},   b ≤ a → ∃ n, Order.pred^[n] a 
= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
· 使用定理 `IsMin.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMi
n a → b ≤ a → b = a
-/
instance Set.OrdConnected.isPredArchimedean [PredOrder α] [IsPredArchimedean α]
    (s : Set α) [s.OrdConnected] : IsPredArchimedean s where
  exists_pred_iterate_of_le := @fun ⟨b, hb⟩ ⟨c, hc⟩ hbc ↦ by classical
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
/-
**Set.OrdConnected.isSuccArchimedean** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Set.OrdConnected.isSuccArchimedean [SuccOrder α] [IsSuccArchimedean α] (s 
: Set α) [s.OrdConnected] : IsSuccArchimedean s
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Set.OrdConnected.isSuccArchimedean [SuccOrder α] [IsSuccArchimedean α]
    (s : Set α) [s.OrdConnected] : IsSuccArchimedean s :=
  letI : IsPredArchimedean sᵒᵈ := inferInstanceAs (IsPredArchimedean (OrderDual.ofDual ⁻¹' s))
  inferInstanceAs (IsSuccArchimedean sᵒᵈᵒᵈ)

end OrdConnected

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccOrder
variable [SuccOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

/-
**monotoneOn_of_le_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_le_succ (hs : s.OrdConnected) (hf : forall a, ¬ IsMax a -> a
 in s -> succ a in s -> f a <= f (succ a)) : MonotoneOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a 
<= f (succ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Order.le_succ_iterate`：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k]
 x
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma monotoneOn_of_le_succ (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f a ≤ f (succ a)) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)
/-
**antitoneOn_of_succ_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_succ_le (hs : s.OrdConnected) (hf : forall a, ¬ IsMax a -> a
 in s -> succ a in s -> f (succ a) <= f a) : AntitoneOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (s
ucc a) <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotoneOn_of_le_succ`：monotoneOn_of_le_succ (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMax a -> a in s -> succ a in s -> f a <= f (succ a)) : MonotoneOn
 f s
-/
lemma antitoneOn_of_succ_le (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f (succ a) ≤ f a) : AntitoneOn f s :=
  monotoneOn_of_le_succ (β := βᵒᵈ) hs hf
/-
**strictMonoOn_of_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_lt_succ (hs : s.OrdConnected) (hf : forall a, ¬ IsMax a ->
 a in s -> succ a in s -> f a < f (succ a)) : StrictMonoOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a 
< f (succ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `not_isMax_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Order.le_succ_iterate`：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k]
 x
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.succ_eq_iff_isMax`：succ_eq_iff_isMax : succ a = a ↔ IsMax a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
lemma strictMonoOn_of_lt_succ (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f a < f (succ a)) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_succ_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMax_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab ha hb
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at hb ⊢
    have : succ^[n + 1] a ∈ s := hs.1 ha hb ⟨le_succ_iterate .., le_succ _⟩
    by_cases hb' : IsMax (succ^[n + 1] a)
    · rw [succ_eq_iff_isMax.2 hb']
      exact hn this
    · exact (hn this).trans (hf _ hb' this hb)
/-
**strictAntiOn_of_succ_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_succ_lt (hs : s.OrdConnected) (hf : forall a, ¬ IsMax a ->
 a in s -> succ a in s -> f (succ a) < f a) : StrictAntiOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (s
ucc a) < f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_lt_succ`：strictMonoOn_of_lt_succ (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a < f (succ a)) : StrictM
onoOn f s
-/
lemma strictAntiOn_of_succ_lt (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMax a → a ∈ s → succ a ∈ s → f (succ a) < f a) : StrictAntiOn f s :=
  strictMonoOn_of_lt_succ (β := βᵒᵈ) hs hf
/-
**monotone_of_le_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_le_succ (hf : forall a, ¬ IsMax a -> f a <= f (succ a)) : Mono
tone f
参数：hf : forall a, ¬ IsMax a -> f a <= f (succ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotoneOn_of_le_succ`：monotoneOn_of_le_succ (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMax a -> a in s -> succ a in s -> f a <= f (succ a)) : MonotoneOn
 f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma monotone_of_le_succ (hf : ∀ a, ¬ IsMax a → f a ≤ f (succ a)) : Monotone f := by
  simpa using monotoneOn_of_le_succ Set.ordConnected_univ (by simpa using hf)
/-
**antitone_of_succ_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_succ_le (hf : forall a, ¬ IsMax a -> f (succ a) <= f a) : Anti
tone f
参数：hf : forall a, ¬ IsMax a -> f (succ a) <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antitoneOn_of_succ_le`：antitoneOn_of_succ_le (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) <= f a) : AntitoneOn
 f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma antitone_of_succ_le (hf : ∀ a, ¬ IsMax a → f (succ a) ≤ f a) : Antitone f := by
  simpa using antitoneOn_of_succ_le Set.ordConnected_univ (by simpa using hf)
/-
**strictMono_of_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_of_lt_succ (hf : forall a, ¬ IsMax a -> f a < f (succ a)) : Str
ictMono f
参数：hf : forall a, ¬ IsMax a -> f a < f (succ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_lt_succ`：strictMonoOn_of_lt_succ (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a < f (succ a)) : StrictM
onoOn f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma strictMono_of_lt_succ (hf : ∀ a, ¬ IsMax a → f a < f (succ a)) : StrictMono f := by
  simpa using strictMonoOn_of_lt_succ Set.ordConnected_univ (by simpa using hf)
/-
**strictAnti_of_succ_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_of_succ_lt (hf : forall a, ¬ IsMax a -> f (succ a) < f a) : Str
ictAnti f
参数：hf : forall a, ¬ IsMax a -> f (succ a) < f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictAntiOn_of_succ_lt`：strictAntiOn_of_succ_lt (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) < f a) : StrictA
ntiOn f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma strictAnti_of_succ_lt (hf : ∀ a, ¬ IsMax a → f (succ a) < f a) : StrictAnti f := by
  simpa using strictAntiOn_of_succ_lt Set.ordConnected_univ (by simpa using hf)

end SuccOrder

section PredOrder
variable [PredOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

/-
**monotoneOn_of_pred_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_pred_le (hs : s.OrdConnected) (hf : forall a, ¬ IsMin a -> a
 in s -> pred a in s -> f (pred a) <= f a) : MonotoneOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (p
red a) <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.pred_eq_iff_isMin`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_
1 : PredOrder α] {a : α}, Order.pred a = a ↔ IsMin a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
lemma monotoneOn_of_pred_le (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f (pred a) ≤ f a) : MonotoneOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab
  clear hab
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n] b ∈ s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)
/-
**antitoneOn_of_le_pred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_le_pred (hs : s.OrdConnected) (hf : forall a, ¬ IsMin a -> a
 in s -> pred a in s -> f a <= f (pred a)) : AntitoneOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a 
<= f (pred a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotoneOn_of_pred_le`：monotoneOn_of_pred_le (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) <= f a) : MonotoneOn
 f s
-/
lemma antitoneOn_of_le_pred (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f a ≤ f (pred a)) : AntitoneOn f s :=
  monotoneOn_of_pred_le (β := βᵒᵈ) hs hf
/-
**strictMonoOn_of_pred_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_pred_lt (hs : s.OrdConnected) (hf : forall a, ¬ IsMin a ->
 a in s -> pred a in s -> f (pred a) < f a) : StrictMonoOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (p
red a) < f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `not_isMin_of_lt`：not_isMin_of_lt (h : b < a) : ¬IsMin a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Set.OrdConnected.out'`：∀ {α : Type u_1} {inst : Preorder α} {s : Set α} 
[self : s.OrdConnected] ⦃x : α⦄,   x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.pred_eq_iff_isMin`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_
1 : PredOrder α] {a : α}, Order.pred a = a ↔ IsMin a
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
-/
lemma strictMonoOn_of_pred_lt (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f (pred a) < f a) : StrictMonoOn f s := by
  rintro a ha b hb hab
  obtain ⟨n, rfl⟩ := exists_pred_iterate_of_le hab.le
  obtain _ | n := n
  · simp at hab
  apply not_isMin_of_lt at hab
  induction n with
  | zero => simpa using hf _ hab hb ha
  | succ n hn =>
    rw [Function.iterate_succ_apply'] at ha ⊢
    have : pred^[n + 1] b ∈ s := hs.1 ha hb ⟨pred_le _, pred_iterate_le ..⟩
    by_cases ha' : IsMin (pred^[n + 1] b)
    · rw [pred_eq_iff_isMin.2 ha']
      exact hn this
    · exact (hn this).trans' (hf _ ha' this ha)
/-
**strictAntiOn_of_lt_pred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_lt_pred (hs : s.OrdConnected) (hf : forall a, ¬ IsMin a ->
 a in s -> pred a in s -> f a < f (pred a)) : StrictAntiOn f s
参数：hs : s.OrdConnected；hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a 
< f (pred a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_pred_lt`：strictMonoOn_of_pred_lt (hs : s.OrdConnected) (
hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) < f a) : StrictM
onoOn f s
-/
lemma strictAntiOn_of_lt_pred (hs : s.OrdConnected)
    (hf : ∀ a, ¬ IsMin a → a ∈ s → pred a ∈ s → f a < f (pred a)) : StrictAntiOn f s :=
  strictMonoOn_of_pred_lt (β := βᵒᵈ) hs hf
/-
**monotone_of_pred_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_pred_le (hf : forall a, ¬ IsMin a -> f (pred a) <= f a) : Mono
tone f
参数：hf : forall a, ¬ IsMin a -> f (pred a) <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `monotoneOn_of_pred_le`：monotoneOn_of_pred_le (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) <= f a) : MonotoneOn
 f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma monotone_of_pred_le (hf : ∀ a, ¬ IsMin a → f (pred a) ≤ f a) : Monotone f := by
  simpa using monotoneOn_of_pred_le Set.ordConnected_univ (by simpa using hf)
/-
**antitone_of_le_pred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_le_pred (hf : forall a, ¬ IsMin a -> f a <= f (pred a)) : Anti
tone f
参数：hf : forall a, ¬ IsMin a -> f a <= f (pred a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antitoneOn_of_le_pred`：antitoneOn_of_le_pred (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMin a -> a in s -> pred a in s -> f a <= f (pred a)) : AntitoneOn
 f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma antitone_of_le_pred (hf : ∀ a, ¬ IsMin a → f a ≤ f (pred a)) : Antitone f := by
  simpa using antitoneOn_of_le_pred Set.ordConnected_univ (by simpa using hf)
/-
**strictMono_of_pred_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_of_pred_lt (hf : forall a, ¬ IsMin a -> f (pred a) < f a) : Str
ictMono f
参数：hf : forall a, ¬ IsMin a -> f (pred a) < f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_pred_lt`：strictMonoOn_of_pred_lt (hs : s.OrdConnected) (
hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) < f a) : StrictM
onoOn f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma strictMono_of_pred_lt (hf : ∀ a, ¬ IsMin a → f (pred a) < f a) : StrictMono f := by
  simpa using strictMonoOn_of_pred_lt Set.ordConnected_univ (by simpa using hf)
/-
**strictAnti_of_lt_pred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_of_lt_pred (hf : forall a, ¬ IsMin a -> f a < f (pred a)) : Str
ictAnti f
参数：hf : forall a, ¬ IsMin a -> f a < f (pred a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictAntiOn_of_lt_pred`：strictAntiOn_of_lt_pred (hs : s.OrdConnected) (
hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a < f (pred a)) : StrictA
ntiOn f s
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma strictAnti_of_lt_pred (hf : ∀ a, ¬ IsMin a → f a < f (pred a)) : StrictAnti f := by
  simpa using strictAntiOn_of_lt_pred Set.ordConnected_univ (by simpa using hf)

end PredOrder
end Monotone

