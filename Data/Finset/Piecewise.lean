/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Order.Interval.Set.Basic

/-!
# Functions defined piecewise on a finset

This file defines `Finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function
which is equal to `f` on `s` and `g` on the complement.

## TODO

Should we deduplicate this from `Set.piecewise`?
-/

@[expose] public section

open Function

namespace Finset
variable {ι : Type*} {π : ι → Sort*} (s : Finset ι) (f g : ∀ i, π i)

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
/-
**Finset.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：piecewise [forall j, Decidable (j in s)] : forall i, π i
参数：j in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on 
its
complement.
-/
def piecewise [∀ j, Decidable (j ∈ s)] : ∀ i, π i := fun i ↦ if i ∈ s then f i else g i
/-
**Finset.piecewise_insert_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_insert_self [DecidableEq ι] {j : ι} [forall i, Decidable (i in i
nsert j s)] : (insert j s).piecewise f g j = f j
参数：i in insert j s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma piecewise_insert_self [DecidableEq ι] {j : ι} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]

@[simp]
/-
**Finset.piecewise_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_empty [forall i : ι, Decidable (i in (∅ : Finset ι))] : piecewis
e ∅ f g = g
参数：i in (∅ : Finset ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_empty [∀ i : ι, Decidable (i ∈ (∅ : Finset ι))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

variable [∀ j, Decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move]
/-
**Finset.piecewise_coe** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_coe : (s : Set ι).piecewise f g = s.piecewise f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
lemma piecewise_coe : (s : Set ι).piecewise f g = s.piecewise f g := by
  ext
  congr

@[simp]
/-
**Finset.piecewise_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_eq_of_mem {i : ι} (hi : i in s) : s.piecewise f g i = f i
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_eq_of_mem {i : ι} (hi : i ∈ s) : s.piecewise f g i = f i := by
  simp [piecewise, hi]

@[simp]
/-
**Finset.piecewise_eq_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_eq_of_notMem {i : ι} (hi : i ∉ s) : s.piecewise f g i = g i
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_eq_of_notMem {i : ι} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [piecewise, hi]
/-
**Finset.piecewise_congr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_congr {f f' g g' : forall i, π i} (hf : forall i in s, f i = f' 
i) (hg : forall i ∉ s, g i = g' i) : s.piecewise f g = s.piecewise f' g'
参数：hf : forall i in s, f i = f' i；hg : forall i ∉ s, g i = g' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_ctx_congr`：if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q ->
 y = v) : ite P x y = ite Q u v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma piecewise_congr {f f' g g' : ∀ i, π i} (hf : ∀ i ∈ s, f i = f' i)
    (hg : ∀ i ∉ s, g i = g' i) : s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]
/-
**Finset.piecewise_insert_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_insert_of_ne [DecidableEq ι] {i j : ι} [forall i, Decidable (i i
n insert j s)] (h : i != j) : (insert j s).piecewise f g i = s.piecewise f g i
参数：i in insert j s；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_insert_of_ne [DecidableEq ι] {i j : ι} [∀ i, Decidable (i ∈ insert j s)]
    (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
/-
**Finset.piecewise_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_insert [DecidableEq ι] (j : ι) [forall i, Decidable (i in insert
 j s)] : (insert j s).piecewise f g = update (s.piecewise f g) j (f j)
参数：j : ι；i in insert j s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_insert [DecidableEq ι] (j : ι) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  simp only [← piecewise_coe, ← Set.piecewise_insert]
  ext
  congr
  simp
/-
**Finset.piecewise_cases** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_cases {i} (p : π i -> Prop) (hf : p (f i)) (hg : p (g i)) : p (s
.piecewise f g i)
参数：p : π i -> Prop；hf : p (f i)；hg : p (g i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma piecewise_cases {i} (p : π i → Prop) (hf : p (f i)) (hg : p (g i)) :
    p (s.piecewise f g i) := by
  by_cases hi : i ∈ s <;> simpa [hi]
/-
**Finset.piecewise_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_singleton [DecidableEq ι] (i : ι) : piecewise {i} f g = update g
 i (f i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
-/
lemma piecewise_singleton [DecidableEq ι] (i : ι) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_empty_eq, piecewise_insert, piecewise_empty]
/-
**Finset.piecewise_piecewise_of_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_piecewise_of_subset_left {s t : Finset ι} [forall i, Decidable (
i in s)] [forall i, Decidable (i in t)] (h : s subseteq t) (f₁ f₂ g : forall a, 
π a) : s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g
参数：i in s；i in t；h : s subseteq t；f₁ f₂ g : forall a, π a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_congr`：piecewise_congr {f f' g g' : forall i, π i} (hf 
: forall i in s, f i = f' i) (hg : forall i ∉ s, g i = g' i) : s.piecewise f g =
 s.piecewise…
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
-/
lemma piecewise_piecewise_of_subset_left {s t : Finset ι} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : ∀ a, π a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]
/-
**Finset.piecewise_idem_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_idem_left (f₁ f₂ g : forall a, π a) : s.piecewise (s.piecewise f
₁ f₂) g = s.piecewise f₁ g
参数：f₁ f₂ g : forall a, π a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_piecewise_of_subset_left`：piecewise_piecewise_of_subset
_left {s t : Finset ι} [forall i, Decidable (i in s)] [forall i, Decidable (i in
 t)] (h : s subseteq t) (f₁ f₂ …
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
lemma piecewise_idem_left (f₁ f₂ g : ∀ a, π a) :
    s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _
/-
**Finset.piecewise_piecewise_of_subset_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_piecewise_of_subset_right {s t : Finset ι} [forall i, Decidable 
(i in s)] [forall i, Decidable (i in t)] (h : t subseteq s) (f g₁ g₂ : forall a,
 π a) : s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂
参数：i in s；i in t；h : t subseteq s；f g₁ g₂ : forall a, π a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_congr`：piecewise_congr {f f' g g' : forall i, π i} (hf 
: forall i in s, f i = f' i) (hg : forall i ∉ s, g i = g' i) : s.piecewise f g =
 s.piecewise…
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
lemma piecewise_piecewise_of_subset_right {s t : Finset ι} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : ∀ a, π a) :
    s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_notMem _ _ (mt (@h _) hi)

@[simp]
/-
**Finset.piecewise_idem_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_idem_right (f g₁ g₂ : forall a, π a) : s.piecewise f (s.piecewis
e g₁ g₂) = s.piecewise f g₂
参数：f g₁ g₂ : forall a, π a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_piecewise_of_subset_right`：piecewise_piecewise_of_subse
t_right {s t : Finset ι} [forall i, Decidable (i in s)] [forall i, Decidable (i 
in t)] (h : t subseteq s) (f g₁ …
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
lemma piecewise_idem_right (f g₁ g₂ : ∀ a, π a) :
    s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂
/-
**Finset.update_eq_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：update_eq_piecewise {β : Type*} [DecidableEq ι] (f : ι -> β) (i : ι) (v : 
β) : update f i v = piecewise (singleton i) (fun _ => v) f
参数：f : ι -> β；i : ι；v : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.piecewise_singleton`：piecewise_singleton [DecidableEq ι] (i : ι) 
: piecewise {i} f g = update g i (f i)
-/
lemma update_eq_piecewise {β : Type*} [DecidableEq ι] (f : ι → β) (i : ι) (v : β) :
    update f i v = piecewise (singleton i) (fun _ => v) f :=
  (piecewise_singleton (fun _ => v) _ _).symm
/-
**Finset.update_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：update_piecewise [DecidableEq ι] (i : ι) (v : π i) : update (s.piecewise f
 g) i v = s.piecewise (update f i v) (update g i v)
参数：i : ι；v : π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
lemma update_piecewise [DecidableEq ι] (i : ι) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) := by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j ∈ s <;> simp [*]
/-
**Finset.update_piecewise_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：update_piecewise_of_mem [DecidableEq ι] {i : ι} (hi : i in s) (v : π i) : 
update (s.piecewise f g) i v = s.piecewise (update f i v) g
参数：hi : i in s；v : π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.update_piecewise`：update_piecewise [DecidableEq ι] (i : ι) (v : π
 i) : update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v)
· 使用引理 `Finset.piecewise_congr`：piecewise_congr {f f' g g' : forall i, π i} (hf 
: forall i in s, f i = f' i) (hg : forall i ∉ s, g i = g' i) : s.piecewise f g =
 s.piecewise…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma update_piecewise_of_mem [DecidableEq ι] {i : ι} (hi : i ∈ s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g := by
  rw [update_piecewise]
  refine s.piecewise_congr (fun _ _ => rfl) fun j hj => update_of_ne ?_ ..
  exact fun h => hj (h.symm ▸ hi)
/-
**Finset.update_piecewise_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：update_piecewise_of_notMem [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i) 
: update (s.piecewise f g) i v = s.piecewise f (update g i v)
参数：hi : i ∉ s；v : π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.update_piecewise`：update_piecewise [DecidableEq ι] (i : ι) (v : π
 i) : update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v)
· 使用引理 `Finset.piecewise_congr`：piecewise_congr {f f' g g' : forall i, π i} (hf 
: forall i in s, f i = f' i) (hg : forall i ∉ s, g i = g' i) : s.piecewise f g =
 s.piecewise…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
lemma update_piecewise_of_notMem [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) := by
  rw [update_piecewise]
  refine s.piecewise_congr (fun j hj => update_of_ne ?_ ..) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)
/-
**Finset.piecewise_same** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_same : s.piecewise f f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma piecewise_same : s.piecewise f f = f := by
  ext i
  by_cases h : i ∈ s <;> simp [h]

section Fintype
variable [Fintype ι]

@[simp]
/-
**Finset.piecewise_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_univ [forall i, Decidable (i in (univ : Finset ι))] (f g : foral
l i, π i) : univ.piecewise f g = f
参数：i in (univ : Finset ι)；f g : forall i, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_univ [∀ i, Decidable (i ∈ (univ : Finset ι))] (f g : ∀ i, π i) :
    univ.piecewise f g = f := by
  ext i
  simp [piecewise]
/-
**Finset.piecewise_compl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_compl [DecidableEq ι] (s : Finset ι) [forall i, Decidable (i in 
s)] [forall i, Decidable (i in sᶜ)] (f g : forall i, π i) : sᶜ.piecewise f g = s
.piecewise g f
参数：s : Finset ι；i in s；i in sᶜ；f g : forall i, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piecewise_compl [DecidableEq ι] (s : Finset ι) [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ sᶜ)] (f g : ∀ i, π i) :
    sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [piecewise]

@[simp]
/-
**Finset.piecewise_erase_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_erase_univ [DecidableEq ι] (i : ι) (f g : forall i, π i) : (Fins
et.univ.erase i).piecewise f g = Function.update f i (g i)
参数：i : ι；f g : forall i, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compl_singleton`：compl_singleton (a : α) : ({a} : Finset α)ᶜ = un
iv.erase a
· 使用引理 `Finset.piecewise_compl`：piecewise_compl [DecidableEq ι] (s : Finset ι) [
forall i, Decidable (i in s)] [forall i, Decidable (i in sᶜ)] (f g : forall i, π
 i) : sᶜ.pie…
· 使用引理 `Finset.piecewise_singleton`：piecewise_singleton [DecidableEq ι] (i : ι) 
: piecewise {i} f g = update g i (f i)
-/
lemma piecewise_erase_univ [DecidableEq ι] (i : ι) (f g : ∀ i, π i) :
    (Finset.univ.erase i).piecewise f g = Function.update f i (g i) := by
  rw [← compl_singleton, piecewise_compl, piecewise_singleton]

end Fintype

variable {π : ι → Type*} {t : Set ι} {t' : ∀ i, Set (π i)} {f g f' g' h : ∀ i, π i}

/-
**Finset.piecewise_mem_set_pi** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_mem_set_pi (hf : f in Set.pi t t') (hg : g in Set.pi t t') : s.p
iecewise f g in Set.pi t t'
参数：hf : f in Set.pi t t'；hg : g in Set.pi t t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.piecewise_coe`：piecewise_coe : (s : Set ι).piecewise f g = s.piec
ewise f g
· 使用定理 `Set.piecewise_mem_pi`：piecewise_mem_pi {δ : α -> Type*} {t : Set α} {t' 
: forall i, Set (δ i)} {f g} (hf : f in pi t t') (hg : g in pi t t') : s.piecewi
se f g in …
-/
lemma piecewise_mem_set_pi (hf : f ∈ Set.pi t t') (hg : g ∈ Set.pi t t') :
    s.piecewise f g ∈ Set.pi t t' := by
  rw [← piecewise_coe]; exact Set.piecewise_mem_pi (↑s) hf hg

variable [∀ i, Preorder (π i)]
/-
**Finset.piecewise_le_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_le_of_le_of_le (hf : f <= h) (hg : g <= h) : s.piecewise f g <= 
h
参数：hf : f <= h；hg : g <= h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_cases`：piecewise_cases {i} (p : π i -> Prop) (hf : p (f
 i)) (hg : p (g i)) : p (s.piecewise f g i)
-/
lemma piecewise_le_of_le_of_le (hf : f ≤ h) (hg : g ≤ h) : s.piecewise f g ≤ h := fun x =>
  piecewise_cases s f g (· ≤ h x) (hf x) (hg x)
/-
**Finset.le_piecewise_of_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_piecewise_of_le_of_le (hf : h <= f) (hg : h <= g) : h <= s.piecewise f 
g
参数：hf : h <= f；hg : h <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_cases`：piecewise_cases {i} (p : π i -> Prop) (hf : p (f
 i)) (hg : p (g i)) : p (s.piecewise f g i)
-/
lemma le_piecewise_of_le_of_le (hf : h ≤ f) (hg : h ≤ g) : h ≤ s.piecewise f g := fun x =>
  piecewise_cases s f g (fun y => h x ≤ y) (hf x) (hg x)
/-
**Finset.piecewise_le_piecewise'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_le_piecewise' (hf : forall x in s, f x <= f' x) (hg : forall x ∉
 s, g x <= g' x) : s.piecewise f g <= s.piecewise f' g'
参数：hf : forall x in s, f x <= f' x；hg : forall x ∉ s, g x <= g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : ι} (hi : i in s) : 
s.piecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finset.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : ι} (hi : i ∉ 
s) : s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma piecewise_le_piecewise' (hf : ∀ x ∈ s, f x ≤ f' x) (hg : ∀ x ∉ s, g x ≤ g' x) :
    s.piecewise f g ≤ s.piecewise f' g' := fun x => by by_cases hx : x ∈ s <;> simp [*]
/-
**Finset.piecewise_le_piecewise** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_le_piecewise (hf : f <= f') (hg : g <= g') : s.piecewise f g <= 
s.piecewise f' g'
参数：hf : f <= f'；hg : g <= g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_le_piecewise'`：piecewise_le_piecewise' (hf : forall x i
n s, f x <= f' x) (hg : forall x ∉ s, g x <= g' x) : s.piecewise f g <= s.piecew
ise f' g'
-/
lemma piecewise_le_piecewise (hf : f ≤ f') (hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => hf x) fun x _ => hg x
/-
**Finset.piecewise_mem_Icc_of_mem_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_mem_Icc_of_mem_of_mem (hf : f in Set.Icc f' g') (hg : g in Set.I
cc f' g') : s.piecewise f g in Set.Icc f' g'
参数：hf : f in Set.Icc f' g'；hg : g in Set.Icc f' g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_piecewise_of_le_of_le`：le_piecewise_of_le_of_le (hf : h <= f) 
(hg : h <= g) : h <= s.piecewise f g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finset.piecewise_le_of_le_of_le`：piecewise_le_of_le_of_le (hf : f <= h) 
(hg : g <= h) : s.piecewise f g <= h
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma piecewise_mem_Icc_of_mem_of_mem (hf : f ∈ Set.Icc f' g') (hg : g ∈ Set.Icc f' g') :
    s.piecewise f g ∈ Set.Icc f' g' :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩
/-
**Finset.piecewise_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_mem_Icc (h : f <= g) : s.piecewise f g in Set.Icc f g
参数：h : f <= g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_mem_Icc_of_mem_of_mem`：piecewise_mem_Icc_of_mem_of_mem 
(hf : f in Set.Icc f' g') (hg : g in Set.Icc f' g') : s.piecewise f g in Set.Icc
 f' g'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
lemma piecewise_mem_Icc (h : f ≤ g) : s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)
/-
**Finset.piecewise_mem_Icc'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piecewise_mem_Icc' (h : g <= f) : s.piecewise f g in Set.Icc g f
参数：h : g <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.piecewise_mem_Icc_of_mem_of_mem`：piecewise_mem_Icc_of_mem_of_mem 
(hf : f in Set.Icc f' g') (hg : g in Set.Icc f' g') : s.piecewise f g in Set.Icc
 f' g'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
lemma piecewise_mem_Icc' (h : g ≤ f) : s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

end Finset

