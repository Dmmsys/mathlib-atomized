/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Dedup
public import Mathlib.Data.List.Infix

/-!
# Preparations for defining operations on `Finset`.

The operations here ignore multiplicities,
and prepare for defining the corresponding operations on `Finset`.
-/

@[expose] public section


-- Assert that we define `Finset` without the material on the set lattice.
-- Note that we cannot put this in `Data.Finset.Basic` because we proved relevant lemmas there.
assert_not_exists Set.sInter

namespace Multiset

open List

variable {α : Type*} [DecidableEq α] {s : Multiset α}

/-! ### finset insert -/


/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `Finset`. -/
/-
**Multiset.ndinsert** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：ndinsert (a : α) (s : Multiset α) : Multiset α
参数：a : α；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `Finset`.
-/
def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]
/-
**Multiset.coe_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α)
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α) :=
  rfl

@[simp]
/-
**Multiset.ndinsert_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinsert_zero (a : α) : ndinsert a 0 = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ndinsert_zero (a : α) : ndinsert a 0 = {a} :=
  rfl

@[simp]
/-
**Multiset.ndinsert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinsert_of_mem {a : α} {s : Multiset α} : a in s -> ndinsert a s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem ndinsert_of_mem {a : α} {s : Multiset α} : a ∈ s → ndinsert a s = s :=
  Quot.inductionOn s fun _ h => congr_arg ((↑) : List α → Multiset α) <| insert_of_mem h

@[simp]
/-
**Multiset.ndinsert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinsert_of_notMem {a : α} {s : Multiset α} : a ∉ s -> ndinsert a s = a ::
ₘ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem ndinsert_of_notMem {a : α} {s : Multiset α} : a ∉ s → ndinsert a s = a ::ₘ s :=
  Quot.inductionOn s fun _ h => congr_arg ((↑) : List α → Multiset α) <| insert_of_not_mem h

@[simp]
/-
**Multiset.mem_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_ndinsert {a b : α} {s : Multiset α} : a in ndinsert b s ↔ a = b ∨ a in
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_insert_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b a 
: α} {l : List α}, a ∈ List.insert b l ↔ a = b ∨ a ∈ l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem mem_ndinsert {a b : α} {s : Multiset α} : a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun _ => mem_insert_iff

@[simp]
/-
**Multiset.le_ndinsert_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_ndinsert_self (a : α) (s : Multiset α) : s <= ndinsert a s
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.sublist_insert`：sublist_insert (a : α) (l : List α) : l <+ l.insert
 a
-/
theorem le_ndinsert_self (a : α) (s : Multiset α) : s ≤ ndinsert a s :=
  Quot.inductionOn s fun _ => (sublist_insert _ _).subperm
/-
**Multiset.mem_ndinsert_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_ndinsert_self (a : α) (s : Multiset α) : a in ndinsert a s
参数：a : α；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem mem_ndinsert_self (a : α) (s : Multiset α) : a ∈ ndinsert a s := by simp
/-
**Multiset.mem_ndinsert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_ndinsert_of_mem {a b : α} {s : Multiset α} (h : a in s) : a in ndinser
t b s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_ndinsert`：mem_ndinsert {a b : α} {s : Multiset α} : a in nd
insert b s ↔ a = b ∨ a in s
-/
theorem mem_ndinsert_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ ndinsert b s :=
  mem_ndinsert.2 (Or.inr h)
/-
**Multiset.length_ndinsert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：length_ndinsert_of_mem {a : α} {s : Multiset α} (h : a in s) : card (ndins
ert a s) = card s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.ndinsert_of_mem`：ndinsert_of_mem {a : α} {s : Multiset α} : a i
n s -> ndinsert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_ndinsert_of_mem {a : α} {s : Multiset α} (h : a ∈ s) :
    card (ndinsert a s) = card s := by simp [h]
/-
**Multiset.length_ndinsert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：length_ndinsert_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) : card (ndi
nsert a s) = card s + 1
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_ndinsert_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) :
    card (ndinsert a s) = card s + 1 := by simp [h]
/-
**Multiset.dedup_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ s) = ndinsert a (dedup 
s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {s : Multiset α} :
 a in s -> dedup (a ::ₘ s) = dedup s
· 使用定理 `Multiset.ndinsert_of_mem`：ndinsert_of_mem {a : α} {s : Multiset α} : a i
n s -> ndinsert a s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {s : Multise
t α} : a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
-/
theorem dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ s) = ndinsert a (dedup s) := by
  by_cases h : a ∈ s <;> simp [h]
/-
**Multiset.Nodup.ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α} (a : α), s.Nodup 
→ (Multiset.ndinsert a s).Nodup
参数：a : α；Multiset.ndinsert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.Nodup.insert`：∀ {α : Type u} {l : List α} {a : α} [inst : BEq α] [L
awfulBEq α], l.Nodup → (List.insert a l).Nodup
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Nodup.ndinsert (a : α) : Nodup s → Nodup (ndinsert a s) :=
  Quot.inductionOn s fun _ => Nodup.insert
/-
**Multiset.ndinsert_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinsert_le {a : α} {s t : Multiset α} : ndinsert a s <= t ↔ s <= t ∧ a in
 t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.le_ndinsert_self`：le_ndinsert_self (a : α) (s : Multiset α) : s
 <= ndinsert a s
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.mem_ndinsert_self`：mem_ndinsert_self (a : α) (s : Multiset α) :
 a in ndinsert a s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.ndinsert_of_mem`：ndinsert_of_mem {a : α} {s : Multiset α} : a i
n s -> ndinsert a s = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.cons_le_cons_iff`：∀ {α : Type u_1} {s t : Multiset α} (a : α), 
a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t
· 使用定理 `Multiset.le_cons_of_notMem`：le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t
 ↔ s <= t
-/
theorem ndinsert_le {a : α} {s t : Multiset α} : ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
  ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a ∈ s then by simp [h, l]
    else by
      rw [ndinsert_of_notMem h, ← cons_erase m, cons_le_cons_iff, ← le_cons_of_notMem h,
          cons_erase m]
      exact l⟩
/-
**Multiset.attach_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_ndinsert (a : α) (s : Multiset α) : (s.ndinsert a).attach = ndinser
t ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.
2⟩)
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Multiset.mem_ndinsert_self`：mem_ndinsert_self (a : α) (s : Multiset α) :
 a in ndinsert a s
· 使用定理 `Multiset.mem_ndinsert_of_mem`：mem_ndinsert_of_mem {a b : α} {s : Multise
t α} (h : a in s) : a in ndinsert b s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Multiset.ndinsert_of_mem`：ndinsert_of_mem {a : α} {s : Multiset α} : a i
n s -> ndinsert a s = s
· 使用定理 `Multiset.mem_attach`：mem_attach (s : Multiset α) : forall x, x in s.atta
ch
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.attach_cons`：attach_cons (a : α) (m : Multiset α) : (a ::ₘ m).a
ttach = ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p
.2⟩
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem attach_ndinsert (a : α) (s : Multiset α) :
    (s.ndinsert a).attach =
      ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
  have eq :
    ∀ h : ∀ p : { x // x ∈ s }, p.1 ∈ s,
      (fun p : { x // x ∈ s } => ⟨p.val, h p⟩ : { x // x ∈ s } → { x // x ∈ s }) = id :=
    fun _ => funext fun _ => Subtype.ext rfl
  have : ∀ (t) (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
      (s.attach.map fun p => ⟨p.1, eq ▸ mem_ndinsert_of_mem p.2⟩) := by
    intro t ht
    by_cases h : a ∈ s
    · rw [ndinsert_of_mem h] at ht
      subst ht
      rw [eq, map_id, ndinsert_of_mem (mem_attach _ _)]
    · rw [ndinsert_of_notMem h] at ht
      subst ht
      simp [attach_cons, h]
  this _ rfl

@[simp]
/-
**Multiset.disjoint_ndinsert_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_ndinsert_left {a : α} {s t : Multiset α} : Disjoint (ndinsert a s
) t ↔ a ∉ t ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.disjoint_cons_left`：disjoint_cons_left {a : α} {s t : Multiset 
α} : Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t
-/
theorem disjoint_ndinsert_left {a : α} {s t : Multiset α} :
    Disjoint (ndinsert a s) t ↔ a ∉ t ∧ Disjoint s t :=
  Iff.trans (by simp [disjoint_left]) disjoint_cons_left

@[simp]
/-
**Multiset.disjoint_ndinsert_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_ndinsert_right {a : α} {s t : Multiset α} : Disjoint s (ndinsert 
a t) ↔ a ∉ s ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Multiset.disjoint_ndinsert_left`：disjoint_ndinsert_left {a : α} {s t : M
ultiset α} : Disjoint (ndinsert a s) t ↔ a ∉ t ∧ Disjoint s t
-/
theorem disjoint_ndinsert_right {a : α} {s t : Multiset α} :
    Disjoint s (ndinsert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm, disjoint_ndinsert_left]; tauto

/-! ### finset union -/


/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `Finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
/-
**Multiset.ndunion** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：ndunion (s t : Multiset α) : Multiset α
参数：s t : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `Finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.)
-/
def ndunion (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.union p₂

@[simp]
/-
**Multiset.coe_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_ndunion (l₁ l₂ : List α) : @ndunion α _ l₁ l₂ = (l₁ union l₂ : List α)
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ndunion (l₁ l₂ : List α) : @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : List α) :=
  rfl

-- `simp` can prove this once we have `ndunion_eq_union`.
/-
**Multiset.zero_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_ndunion (s : Multiset α) : ndunion 0 s = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem zero_ndunion (s : Multiset α) : ndunion 0 s = s :=
  Quot.inductionOn s fun _ => rfl

@[simp]
/-
**Multiset.cons_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_ndunion (s t : Multiset α) (a : α) : ndunion (a ::ₘ s) t = ndinsert a
 (ndunion s t)
参数：s t : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
-/
theorem cons_ndunion (s t : Multiset α) (a : α) : ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => rfl

@[simp]
/-
**Multiset.mem_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_ndunion {s t : Multiset α} {a : α} : a in ndunion s t ↔ a in s ∨ a in 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `List.mem_union_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem mem_ndunion {s t : Multiset α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
  Quot.induction_on₂ s t fun _ _ => List.mem_union_iff
/-
**Multiset.le_ndunion_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_ndunion_right (s t : Multiset α) : t <= ndunion s t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.IsSuffix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
.Sublist l₂
· 使用定理 `List.suffix_union_right`：suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁
 union l₂
-/
theorem le_ndunion_right (s t : Multiset α) : t ≤ ndunion s t :=
  Quot.induction_on₂ s t fun _ _ => (suffix_union_right _ _).sublist.subperm
/-
**Multiset.subset_ndunion_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_ndunion_right (s t : Multiset α) : t subseteq ndunion s t
参数：s t : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.le_ndunion_right`：le_ndunion_right (s t : Multiset α) : t <= nd
union s t
-/
theorem subset_ndunion_right (s t : Multiset α) : t ⊆ ndunion s t :=
  subset_of_le (le_ndunion_right s t)
/-
**Multiset.ndunion_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndunion_le_add (s t : Multiset α) : ndunion s t <= s + t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.union_sublist_append`：union_sublist_append (l₁ l₂ : List α) : l₁ un
ion l₂ <+ l₁ ++ l₂
-/
theorem ndunion_le_add (s t : Multiset α) : ndunion s t ≤ s + t :=
  Quot.induction_on₂ s t fun _ _ => (union_sublist_append _ _).subperm
/-
**Multiset.ndunion_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndunion_le {s t u : Multiset α} : ndunion s t <= u ↔ s subseteq u ∧ t <= u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.zero_ndunion`：zero_ndunion (s : Multiset α) : ndunion 0 s = s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.cons_ndunion`：cons_ndunion (s t : Multiset α) (a : α) : ndunion
 (a ::ₘ s) t = ndinsert a (ndunion s t)
-/
theorem ndunion_le {s t u : Multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
  Multiset.induction_on s (by simp [zero_ndunion])
    (fun _ _ h =>
      by simp only [cons_ndunion, ndinsert_le, and_comm, cons_subset, and_left_comm, h,
        and_assoc])
/-
**Multiset.subset_ndunion_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_ndunion_left (s t : Multiset α) : s subseteq ndunion s t
参数：s t : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_ndunion`：mem_ndunion {s t : Multiset α} {a : α} : a in ndun
ion s t ↔ a in s ∨ a in t
-/
theorem subset_ndunion_left (s t : Multiset α) : s ⊆ ndunion s t := fun _ h =>
  mem_ndunion.2 <| Or.inl h
/-
**Multiset.le_ndunion_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_ndunion_left {s} (t : Multiset α) (d : Nodup s) : s <= ndunion s t
参数：t : Multiset α；d : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Multiset.subset_ndunion_left`：subset_ndunion_left (s t : Multiset α) : s
 subseteq ndunion s t
-/
theorem le_ndunion_left {s} (t : Multiset α) (d : Nodup s) : s ≤ ndunion s t :=
  (le_iff_subset d).2 <| subset_ndunion_left _ _
/-
**Multiset.ndunion_le_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndunion_le_union (s t : Multiset α) : ndunion s t <= s union t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.ndunion_le`：ndunion_le {s t u : Multiset α} : ndunion s t <= u 
↔ s subseteq u ∧ t <= u
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用引理 `Multiset.le_union_left`：le_union_left : s <= s union t
· 使用引理 `Multiset.le_union_right`：le_union_right : t <= s union t
-/
theorem ndunion_le_union (s t : Multiset α) : ndunion s t ≤ s ∪ t :=
  ndunion_le.2 ⟨subset_of_le le_union_left, le_union_right⟩
/-
**Multiset.Nodup.ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset α) {t : Multiset α},
 t.Nodup → (s.ndunion t).Nodup
参数：s : Multiset α；s.ndunion t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `List.Nodup.union`：∀ {α : Type u} {l₂ : List α} [inst : BEq α] [LawfulBEq
 α] (l₁ : List α), l₂.Nodup → (l₁ ∪ l₂).Nodup
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Nodup.ndunion (s : Multiset α) {t : Multiset α} : Nodup t → Nodup (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => List.Nodup.union _

@[simp]
/-
**Multiset.ndunion_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndunion_eq_union {s t : Multiset α} (d : Nodup s) : ndunion s t = s union 
t
参数：d : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Multiset.ndunion_le_union`：ndunion_le_union (s t : Multiset α) : ndunion
 s t <= s union t
· 使用引理 `Multiset.union_le`：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
· 使用定理 `Multiset.le_ndunion_left`：le_ndunion_left {s} (t : Multiset α) (d : Nodu
p s) : s <= ndunion s t
· 使用定理 `Multiset.le_ndunion_right`：le_ndunion_right (s t : Multiset α) : t <= nd
union s t
-/
theorem ndunion_eq_union {s t : Multiset α} (d : Nodup s) : ndunion s t = s ∪ t :=
  le_antisymm (ndunion_le_union _ _) <| union_le (le_ndunion_left _ d) (le_ndunion_right _ _)
/-
**Multiset.dedup_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_add (s t : Multiset α) : dedup (s + t) = ndunion s (dedup t)
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.dedup_append`：dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁
 union dedup l₂
-/
theorem dedup_add (s t : Multiset α) : dedup (s + t) = ndunion s (dedup t) :=
  Quot.induction_on₂ s t fun _ _ => congr_arg ((↑) : List α → Multiset α) <| dedup_append _ _
/-
**Multiset.Disjoint.ndunion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, Disjoint s t →
 s.ndunion t = s.dedup + t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Disjoint.union_eq`：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys :
 List α}, xs.Disjoint ys → xs ∪ ys = xs.dedup ++ ys
-/
theorem Disjoint.ndunion_eq {s t : Multiset α} (h : Disjoint s t) :
    s.ndunion t = s.dedup + t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Disjoint.union_eq <| by simpa using h
/-
**Multiset.Subset.ndunion_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ⊆ t → s.ndun
ion t = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Subset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {xs 
ys : List α}, xs ⊆ ys → xs ∪ ys = ys
-/
theorem Subset.ndunion_eq_right {s t : Multiset α} (h : s ⊆ t) : s.ndunion t = t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Subset.union_eq_right h

/-! ### finset inter -/


/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `Finset`. (`s ∩ t` would also work as an intersection operation
  on finset, but this is more efficient.) -/
/-
**Multiset.ndinter** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：ndinter (s t : Multiset α) : Multiset α
参数：s t : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `Finset`. (`s ∩ t` would also work as an intersec
tion operation
  on finset, but this is more efficient.)
-/
def ndinter (s t : Multiset α) : Multiset α :=
  filter (· ∈ t) s

@[simp]
/-
**Multiset.coe_ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ = (l₁ inter l₂ : List α)
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Multiset.filter_congr`：filter_congr {p q : α -> Prop} [DecidablePred p] 
[DecidablePred q] {s : Multiset α} : (forall x in s, p x ↔ q x) -> filter p s = 
filter q s
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
-/
theorem coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : List α) := by
  simp only [ndinter, mem_coe, filter_coe, coe_eq_coe, ← elem_eq_mem]
  apply Perm.refl

@[simp]
/-
**Multiset.zero_ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_ndinter (s : Multiset α) : ndinter 0 s = 0
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_ndinter (s : Multiset α) : ndinter 0 s = 0 :=
  rfl

@[simp]
/-
**Multiset.cons_ndinter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_ndinter_of_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a in t)
 : ndinter (a ::ₘ s) t = a ::ₘ ndinter s t
参数：s : Multiset α；h : a in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_cons_of_pos`：filter_cons_of_pos {a : α} (s) : p a -> fil
ter p (a ::ₘ s) = a ::ₘ filter p s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_ndinter_of_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∈ t) :
    ndinter (a ::ₘ s) t = a ::ₘ ndinter s t := by simp [ndinter, h]

@[simp]
/-
**Multiset.ndinter_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_cons_of_notMem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ 
t) : ndinter (a ::ₘ s) t = ndinter s t
参数：s : Multiset α；h : a ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_cons_of_neg`：filter_cons_of_neg {a : α} (s) : ¬p a -> fi
lter p (a ::ₘ s) = filter p s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ndinter_cons_of_notMem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t) :
    ndinter (a ::ₘ s) t = ndinter s t := by simp [ndinter, h]

@[simp]
/-
**Multiset.mem_ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_ndinter {s t : Multiset α} {a : α} : a in ndinter s t ↔ a in s ∧ a in 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ndinter {s t : Multiset α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t := by
  simp [ndinter, mem_filter]

-- simp can prove this once we have `ndinter_eq_inter` and `Nodup.inter` a few lines down.
/-
**Multiset.Nodup.ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α} (t : Multiset α),
 s.Nodup → (s.ndinter t).Nodup
参数：t : Multiset α；s.ndinter t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Decidable
Pred p] {s : Multiset α}, s.Nodup → (Multiset.filter p s).Nodup
-/
theorem Nodup.ndinter {s : Multiset α} (t : Multiset α) : Nodup s → Nodup (ndinter s t) :=
  Nodup.filter _
/-
**Multiset.le_ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_ndinter {s t u : Multiset α} : s <= ndinter t u ↔ s <= t ∧ s subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_ndinter {s t u : Multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u := by
  simp [ndinter, le_filter, subset_iff]
/-
**Multiset.ndinter_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_le_left (s t : Multiset α) : ndinter s t <= s
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_ndinter`：le_ndinter {s t u : Multiset α} : s <= ndinter t u 
↔ s <= t ∧ s subseteq u
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ndinter_le_left (s t : Multiset α) : ndinter s t ≤ s :=
  (le_ndinter.1 le_rfl).1
/-
**Multiset.ndinter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_subset_left (s t : Multiset α) : ndinter s t subseteq s
参数：s t : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.ndinter_le_left`：ndinter_le_left (s t : Multiset α) : ndinter s
 t <= s
-/
theorem ndinter_subset_left (s t : Multiset α) : ndinter s t ⊆ s :=
  subset_of_le (ndinter_le_left s t)
/-
**Multiset.ndinter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_subset_right (s t : Multiset α) : ndinter s t subseteq t
参数：s t : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_ndinter`：le_ndinter {s t u : Multiset α} : s <= ndinter t u 
↔ s <= t ∧ s subseteq u
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ndinter_subset_right (s t : Multiset α) : ndinter s t ⊆ t :=
  (le_ndinter.1 le_rfl).2
/-
**Multiset.ndinter_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_le_right {s} (t : Multiset α) (d : Nodup s) : ndinter s t <= t
参数：t : Multiset α；d : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Multiset.Nodup.ndinter`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} (t : Multiset α), s.Nodup → (s.ndinter t).Nodup
· 使用定理 `Multiset.ndinter_subset_right`：ndinter_subset_right (s t : Multiset α) :
 ndinter s t subseteq t
-/
theorem ndinter_le_right {s} (t : Multiset α) (d : Nodup s) : ndinter s t ≤ t :=
  (le_iff_subset <| d.ndinter _).2 <| ndinter_subset_right _ _
/-
**Multiset.inter_le_ndinter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inter_le_ndinter (s t : Multiset α) : s inter t <= ndinter s t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_ndinter`：le_ndinter {s t u : Multiset α} : s <= ndinter t u 
↔ s <= t ∧ s subseteq u
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
-/
theorem inter_le_ndinter (s t : Multiset α) : s ∩ t ≤ ndinter s t :=
  le_ndinter.2 ⟨inter_le_left, subset_of_le inter_le_right⟩

@[simp]
/-
**Multiset.ndinter_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_eq_inter {s t : Multiset α} (d : Nodup s) : ndinter s t = s inter 
t
参数：d : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Multiset.le_inter`：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
· 使用定理 `Multiset.ndinter_le_left`：ndinter_le_left (s t : Multiset α) : ndinter s
 t <= s
· 使用定理 `Multiset.ndinter_le_right`：ndinter_le_right {s} (t : Multiset α) (d : No
dup s) : ndinter s t <= t
· 使用定理 `Multiset.inter_le_ndinter`：inter_le_ndinter (s t : Multiset α) : s inter
 t <= ndinter s t
-/
theorem ndinter_eq_inter {s t : Multiset α} (d : Nodup s) : ndinter s t = s ∩ t :=
  le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

@[simp]
/-
**Multiset.Nodup.inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α} (t : Multiset α),
 s.Nodup → (s ∩ t).Nodup
参数：t : Multiset α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.ndinter_eq_inter`：ndinter_eq_inter {s t : Multiset α} (d : Nodu
p s) : ndinter s t = s inter t
· 使用定理 `Multiset.Nodup.filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Decidable
Pred p] {s : Multiset α}, s.Nodup → (Multiset.filter p s).Nodup
-/
theorem Nodup.inter {s : Multiset α} (t : Multiset α) (d : Nodup s) : Nodup (s ∩ t) := by
  rw [← ndinter_eq_inter d]
  exact d.filter _
/-
**Multiset.ndinter_eq_zero_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ndinter_eq_zero_iff_disjoint {s t : Multiset α} : ndinter s t = 0 ↔ Disjoi
nt s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.subset_zero`：∀ {α : Type u_1} {s : Multiset α}, s ⊆ 0 ↔ s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ndinter_eq_zero_iff_disjoint {s t : Multiset α} : ndinter s t = 0 ↔ Disjoint s t := by
  rw [← subset_zero]; simp [subset_iff, disjoint_left]

alias ⟨_, Disjoint.ndinter_eq_zero⟩ := ndinter_eq_zero_iff_disjoint
/-
**Multiset.Subset.ndinter_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ⊆ t → s.ndin
ter t = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe''`：quot_mk_to_coe'' (l : List α) : @Eq (Multiset
 α) (Quot.mk Setoid.r l) l
· 使用定理 `Multiset.coe_ndinter`：coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ 
= (l₁ inter l₂ : List α)
· 使用定理 `List.Subset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {xs y
s : List α}, xs ⊆ ys → xs ∩ ys = xs
-/
theorem Subset.ndinter_eq_left {s t : Multiset α} (h : s ⊆ t) : s.ndinter t = s := by
  induction s, t using Quot.induction_on₂
  rw [quot_mk_to_coe'', quot_mk_to_coe'', coe_ndinter, List.Subset.inter_eq_left h]

end Multiset

