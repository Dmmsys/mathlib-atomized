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

/-- For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_succ_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_succ_of_le (r : α -> α -> Prop) {n m : α} (h : forall i in
 Ico n m, r i (succ i)) (hnm : n <= m) : ReflTransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ico n m, r i (succ i)；hnm : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ
 i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_succ_of_le (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico n m, r i (succ i))
    (hnm : n ≤ m) : ReflTransGen r n m := by
  revert h; refine Succ.rec ?_ ?_ hnm
  · intro _
    exact ReflTransGen.refl
  · intro m hnm ih h
    have : ReflTransGen r n m := ih fun i hi => h i ⟨hi.1, hi.2.trans_le <| le_succ m⟩
    rcases (le_succ m).eq_or_lt with hm | hm
    · rwa [← hm]
    exact this.tail (h m ⟨hnm, hm⟩)

/-- For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `succ i ~ i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_succ_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_succ_of_ge (r : α -> α -> Prop) {n m : α} (h : forall i in
 Ico m n, r (succ i) i) (hmn : m <= n) : ReflTransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ico m n, r (succ i) i；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.reflTransGen_swap`：reflTransGen_swap : ReflTransGen (swap r) a 
b ↔ ReflTransGen r b a
· 使用定理 `reflTransGen_of_succ_of_le`：reflTransGen_of_succ_of_le (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico n m, r i (succ i)) (hnm : n <= m) : ReflTrans
Gen r n m

--- 原说明 ---
For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `succ i ~
 i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_succ_of_ge (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico m n, r (succ i) i)
    (hmn : m ≤ n) : ReflTransGen r n m := by
  rw [← reflTransGen_swap]
  exact reflTransGen_of_succ_of_le (swap r) h hmn

/-- For `n < m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ succ i`
  for all `i` between `n` and `m`. -/
/-
**transGen_of_succ_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_succ_of_lt (r : α -> α -> Prop) {n m : α} (h : forall i in Ico
 n m, r i (succ i)) (hnm : n < m) : TransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ico n m, r i (succ i)；hnm : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `reflTransGen_of_succ_of_le`：reflTransGen_of_succ_of_le (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico n m, r i (succ i)) (hnm : n <= m) : ReflTrans
Gen r n m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
For `n < m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ suc
c i`
  for all `i` between `n` and `m`.
-/
theorem transGen_of_succ_of_lt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico n m, r i (succ i))
    (hnm : n < m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_le r h hnm.le).resolve_left
    hnm.ne'

/-- For `m < n`, `(n, m)` is in the transitive closure of a relation `~` if `succ i ~ i`
  for all `i` between `n` and `m`. -/
/-
**transGen_of_succ_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_succ_of_gt (r : α -> α -> Prop) {n m : α} (h : forall i in Ico
 m n, r (succ i) i) (hmn : m < n) : TransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ico m n, r (succ i) i；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `reflTransGen_of_succ_of_ge`：reflTransGen_of_succ_of_ge (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico m n, r (succ i) i) (hmn : m <= n) : ReflTrans
Gen r n m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
For `m < n`, `(n, m)` is in the transitive closure of a relation `~` if `succ i 
~ i`
  for all `i` between `n` and `m`.
-/
theorem transGen_of_succ_of_gt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ico m n, r (succ i) i)
    (hmn : m < n) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp <| reflTransGen_of_succ_of_ge r h hmn.le).resolve_left
    hmn.ne

end PartialSucc

section LinearSucc

variable {α : Type*} [LinearOrder α] [SuccOrder α] [IsSuccArchimedean α]

/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ i` and `succ i ~ i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ico 
n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i) i) : ReflTransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ico n m, r i (succ i)；h2 : forall i in Ic
o m n, r (succ i) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `reflTransGen_of_succ_of_le`：reflTransGen_of_succ_of_le (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico n m, r i (succ i)) (hnm : n <= m) : ReflTrans
Gen r n m
· 使用定理 `reflTransGen_of_succ_of_ge`：reflTransGen_of_succ_of_ge (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico m n, r (succ i) i) (hmn : m <= n) : ReflTrans
Gen r n m

--- 原说明 ---
`(n, m)` is in the reflexive-transitive closure of `~` if `i ~ succ i` and `succ
 i ~ i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_succ (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ico n m, r i (succ i))
    (h2 : ∀ i ∈ Ico m n, r (succ i) i) : ReflTransGen r n m :=
  (le_total n m).elim (reflTransGen_of_succ_of_le r h1) <| reflTransGen_of_succ_of_ge r h2

/-- For `n ≠ m`,`(n, m)` is in the transitive closure of a relation `~` if `i ~ succ i` and
  `succ i ~ i` for all `i` between `n` and `m`. -/
/-
**transGen_of_succ_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_succ_of_ne (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ic
o n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i) i) (hnm : n != m) : T
ransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ico n m, r i (succ i)；h2 : forall i in Ic
o m n, r (succ i) i；hnm : n != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
For `n ≠ m`,`(n, m)` is in the transitive closure of a relation `~` if `i ~ succ
 i` and
  `succ i ~ i` for all `i` between `n` and `m`.
-/
theorem transGen_of_succ_of_ne (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ico n m, r i (succ i))
    (h2 : ∀ i ∈ Ico m n, r (succ i) i) (hnm : n ≠ m) : TransGen r n m :=
  (reflTransGen_iff_eq_or_transGen.mp (reflTransGen_of_succ r h1 h2)).resolve_left hnm.symm

/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ succ i` and
  `succ i ~ i` for all `i` between `n` and `m`. -/
/-
**transGen_of_succ_of_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_succ_of_refl (r : α -> α -> Prop) {n m : α} [Std.Refl r] (h1 :
 forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i) i) : T
ransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ico n m, r i (succ i)；h2 : forall i in Ic
o m n, r (succ i) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `transGen_of_succ_of_ne`：transGen_of_succ_of_ne (r : α -> α -> Prop) {n m
 : α} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (suc
c i) i) (hnm…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
`(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ succ i
` and
  `succ i ~ i` for all `i` between `n` and `m`.
-/
theorem transGen_of_succ_of_refl (r : α → α → Prop) {n m : α} [Std.Refl r]
    (h1 : ∀ i ∈ Ico n m, r i (succ i)) (h2 : ∀ i ∈ Ico m n, r (succ i) i) : TransGen r n m := by
  rcases eq_or_ne m n with (rfl | hmn); · exact TransGen.single (refl m)
  exact transGen_of_succ_of_ne r h1 h2 hmn.symm

@[deprecated (since := "2026-03-27")]
alias transGen_of_succ_of_reflexive := transGen_of_succ_of_refl

end LinearSucc

section PartialPred

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]

/-- For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_pred_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_pred_of_ge (r : α -> α -> Prop) {n m : α} (h : forall i in
 Ioc m n, r i (pred i)) (hnm : m <= n) : ReflTransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ioc m n, r i (pred i)；hnm : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `reflTransGen_of_succ_of_le`：reflTransGen_of_succ_of_le (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico n m, r i (succ i)) (hnm : n <= m) : ReflTrans
Gen r n m
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For `m ≤ n`, `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred
 i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_pred_of_ge (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ioc m n, r i (pred i))
    (hnm : m ≤ n) : ReflTransGen r n m :=
  reflTransGen_of_succ_of_le (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

/-- For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `pred i ~ i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_pred_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_pred_of_le (r : α -> α -> Prop) {n m : α} (h : forall i in
 Ioc n m, r (pred i) i) (hmn : n <= m) : ReflTransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ioc n m, r (pred i) i；hmn : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `reflTransGen_of_succ_of_ge`：reflTransGen_of_succ_of_ge (r : α -> α -> Pr
op) {n m : α} (h : forall i in Ico m n, r (succ i) i) (hmn : m <= n) : ReflTrans
Gen r n m
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For `n ≤ m`, `(n, m)` is in the reflexive-transitive closure of `~` if `pred i ~
 i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_pred_of_le (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ioc n m, r (pred i) i)
    (hmn : n ≤ m) : ReflTransGen r n m :=
  reflTransGen_of_succ_of_ge (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

/-- For `m < n`, `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m` if `i ~ pred i`
  for all `i` between `n` and `m`. -/
/-
**transGen_of_pred_of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_pred_of_gt (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc
 m n, r i (pred i)) (hnm : m < n) : TransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ioc m n, r i (pred i)；hnm : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_of_succ_of_lt`：transGen_of_succ_of_lt (r : α -> α -> Prop) {n m
 : α} (h : forall i in Ico n m, r i (succ i)) (hnm : n < m) : TransGen r n m
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For `m < n`, `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m`
 if `i ~ pred i`
  for all `i` between `n` and `m`.
-/
theorem transGen_of_pred_of_gt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ioc m n, r i (pred i))
    (hnm : m < n) : TransGen r n m :=
  transGen_of_succ_of_lt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hnm

/-- For `n < m`, `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m` if `pred i ~ i`
  for all `i` between `n` and `m`. -/
/-
**transGen_of_pred_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_pred_of_lt (r : α -> α -> Prop) {n m : α} (h : forall i in Ioc
 n m, r (pred i) i) (hmn : n < m) : TransGen r n m
参数：r : α -> α -> Prop；h : forall i in Ioc n m, r (pred i) i；hmn : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_of_succ_of_gt`：transGen_of_succ_of_gt (r : α -> α -> Prop) {n m
 : α} (h : forall i in Ico m n, r (succ i) i) (hmn : m < n) : TransGen r n m
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For `n < m`, `(n, m)` is in the transitive closure of a relation `~` for `n ≠ m`
 if `pred i ~ i`
  for all `i` between `n` and `m`.
-/
theorem transGen_of_pred_of_lt (r : α → α → Prop) {n m : α} (h : ∀ i ∈ Ioc n m, r (pred i) i)
    (hmn : n < m) : TransGen r n m :=
  transGen_of_succ_of_gt (α := αᵒᵈ) r (fun x hx => h x ⟨hx.2, hx.1⟩) hmn

end PartialPred

section LinearPred

variable {α : Type*} [LinearOrder α] [PredOrder α] [IsPredArchimedean α]

/-- `(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred i` and `pred i ~ i`
  for all `i` between `n` and `m`. -/
/-
**reflTransGen_of_pred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：reflTransGen_of_pred (r : α -> α -> Prop) {n m : α} (h1 : forall i in Ioc 
m n, r i (pred i)) (h2 : forall i in Ioc n m, r (pred i) i) : ReflTransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ioc m n, r i (pred i)；h2 : forall i in Io
c n m, r (pred i) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
`(n, m)` is in the reflexive-transitive closure of `~` if `i ~ pred i` and `pred
 i ~ i`
  for all `i` between `n` and `m`.
-/
theorem reflTransGen_of_pred (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ioc m n, r i (pred i))
    (h2 : ∀ i ∈ Ioc n m, r (pred i) i) : ReflTransGen r n m :=
  reflTransGen_of_succ (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩) fun x hx =>
    h2 x ⟨hx.2, hx.1⟩

/-- For `n ≠ m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ pred i` and
  `pred i ~ i` for all `i` between `n` and `m`. -/
/-
**transGen_of_pred_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_pred_of_ne (r : α -> α -> Prop) {n m : α} (h1 : forall i in Io
c m n, r i (pred i)) (h2 : forall i in Ioc n m, r (pred i) i) (hnm : n != m) : T
ransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ioc m n, r i (pred i)；h2 : forall i in Io
c n m, r (pred i) i；hnm : n != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_of_succ_of_ne`：transGen_of_succ_of_ne (r : α -> α -> Prop) {n m
 : α} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (suc
c i) i) (hnm…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For `n ≠ m`, `(n, m)` is in the transitive closure of a relation `~` if `i ~ pre
d i` and
  `pred i ~ i` for all `i` between `n` and `m`.
-/
theorem transGen_of_pred_of_ne (r : α → α → Prop) {n m : α} (h1 : ∀ i ∈ Ioc m n, r i (pred i))
    (h2 : ∀ i ∈ Ioc n m, r (pred i) i) (hnm : n ≠ m) : TransGen r n m :=
  transGen_of_succ_of_ne (α := αᵒᵈ) r (fun x hx => h1 x ⟨hx.2, hx.1⟩)
    (fun x hx => h2 x ⟨hx.2, hx.1⟩) hnm

/-- `(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ pred i` and
  `pred i ~ i` for all `i` between `n` and `m`. -/
/-
**transGen_of_pred_of_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transGen_of_pred_of_refl (r : α -> α -> Prop) {n m : α} [Std.Refl r] (h1 :
 forall i in Ioc m n, r i (pred i)) (h2 : forall i in Ioc n m, r (pred i) i) : T
ransGen r n m
参数：r : α -> α -> Prop；h1 : forall i in Ioc m n, r i (pred i)；h2 : forall i in Io
c n m, r (pred i) i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `transGen_of_succ_of_refl`：transGen_of_succ_of_refl (r : α -> α -> Prop) 
{n m : α} [Std.Refl r] (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i i
n Ico m n, r (…
· 使用定理 `instIsSuccArchimedeanOrderDualOfIsPredArchimedean`：∀ {α : Type u_1} [ins
t : Preorder α] [inst_1 : PredOrder α] [IsPredArchimedean α], IsSuccArchimedean 
αᵒᵈ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
`(n, m)` is in the transitive closure of a reflexive relation `~` if `i ~ pred i
` and
  `pred i ~ i` for all `i` between `n` and `m`.
-/
theorem transGen_of_pred_of_refl (r : α → α → Prop) {n m : α} [Std.Refl r]
    (h1 : ∀ i ∈ Ioc m n, r i (pred i)) (h2 : ∀ i ∈ Ioc n m, r (pred i) i) : TransGen r n m :=
  @transGen_of_succ_of_refl αᵒᵈ _ _ _ r _ _ ‹_› (fun x hx ↦ h1 x ⟨hx.2, hx.1⟩)
    fun x hx ↦ h2 x ⟨hx.2, hx.1⟩

@[deprecated (since := "2026-03-27")]
alias transGen_of_pred_of_reflexive := transGen_of_pred_of_refl

end LinearPred

