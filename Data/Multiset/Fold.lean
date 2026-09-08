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

variable (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
/-
**Multiset.fold** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：fold : α -> Multiset α -> α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f

--- 原说明 ---
`fold op b s` folds a commutative associative operation `op` over
  the multiset `s`.
-/
def fold : α → Multiset α → α :=
  foldr op
/-
**Multiset.fold_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_eq_foldr (b : α) (s : Multiset α) : fold op b s = foldr op b s
参数：b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fold_eq_foldr (b : α) (s : Multiset α) :
    fold op b s = foldr op b s :=
  rfl

@[simp]
/-
**Multiset.coe_fold_r** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b
参数：b : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl
/-
**Multiset.coe_fold_l** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b
参数：b : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `Multiset.coe_foldr_swap`：coe_foldr_swap (f : α -> β -> β) [LeftCommutati
ve f] (b : β) (l : List α) : foldr f b l = l.foldl (fun x y => f y x) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op b l).trans <| by simp [hc.comm]
/-
**Multiset.fold_eq_foldl** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_eq_foldl (b : α) (s : Multiset α) : fold op b s = foldl op b s
参数：b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `instRightCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → 
α → α} [hc : Std.Commutative f] [ha : Std.Associative f], RightCommutative f
· 使用定理 `Multiset.coe_fold_l`：coe_fold_l (b : α) (l : List α) : fold op b l = l.f
oldl op b
-/
theorem fold_eq_foldl (b : α) (s : Multiset α) :
    fold op b s = foldl op b s :=
  Quot.inductionOn s fun _ => coe_fold_l _ _ _

@[simp]
/-
**Multiset.fold_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_zero (b : α) : (0 : Multiset α).fold op b = b
参数：b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl

@[simp]
/-
**Multiset.fold_cons_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_cons_left : forall (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = 
a * s.fold op b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.foldr_cons`：foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (fol
dr f b s)
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
-/
theorem fold_cons_left : ∀ (b a : α) (s : Multiset α), (a ::ₘ s).fold op b = a * s.fold op b :=
  foldr_cons _
/-
**Multiset.fold_cons_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold 
op b * a
参数：b a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b * a := by
  simp [hc.comm]
/-
**Multiset.fold_cons'_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Asso
ciative op] (b a : α) (s : Multiset α),   Multiset.fold op b (a ::ₘ s) = Multise
t.fold op (op b a) s
参数：op : α → α → α；b a : α；s : Multiset α；a ::ₘ s；op b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instRightCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → 
α → α} [hc : Std.Commutative f] [ha : Std.Associative f], RightCommutative f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold_eq_foldl`：fold_eq_foldl (b : α) (s : Multiset α) : fold op
 b s = foldl op b s
· 使用定理 `Multiset.foldl_cons`：foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f 
(f b a) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b * a) := by
  rw [fold_eq_foldl, foldl_cons, ← fold_eq_foldl]
/-
**Multiset.fold_cons'_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Asso
ciative op] (b a : α) (s : Multiset α),   Multiset.fold op b (a ::ₘ s) = Multise
t.fold op (op a b) s
参数：op : α → α → α；b a : α；s : Multiset α；a ::ₘ s；op a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold_cons'_right`：∀ {α : Type u_1} (op : α → α → α) [hc : Std.C
ommutative op] [ha : Std.Associative op] (b a : α) (s : Multiset α),   Multiset.
fold op b (a ::…
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
-/
theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a * b) := by
  rw [fold_cons'_right, hc.comm]
/-
**Multiset.fold_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂).fold op (b₁ * b₂) = 
s₁.fold op b₁ * s₂.fold op b₂
参数：b₁ b₂ : α；s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `Multiset.fold_zero`：fold_zero (b : α) : (0 : Multiset α).fold op b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.fold_cons'_right`：∀ {α : Type u_1} (op : α → α → α) [hc : Std.C
ommutative op] [ha : Std.Associative op] (b a : α) (s : Multiset α),   Multiset.
fold op b (a ::…
· 使用定理 `Multiset.fold_cons_right`：fold_cons_right (b a : α) (s : Multiset α) : (
a ::ₘ s).fold op b = s.fold op b * a
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `Multiset.add_cons`：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a
 ::ₘ (s + t)
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
-/
theorem fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) :
    (s₁ + s₂).fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂ :=
  Multiset.induction_on s₂
    (by rw [Multiset.add_zero, fold_zero, ← fold_cons'_right, ← fold_cons_right op])
    (fun a b h => by rw [fold_cons_left, add_cons, fold_cons_left, h, ← ha.assoc, hc.comm a,
      ha.assoc])
/-
**Multiset.fold_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b
参数：b a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.foldr_singleton`：foldr_singleton (b a) : foldr f b ({a} : Multi
set α) = f a b
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
-/
theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a * b :=
  foldr_singleton _ _ _
/-
**Multiset.fold_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_distrib {f g : β -> α} (u₁ u₂ : α) (s : Multiset β) : (s.map fun x =>
 f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂
参数：u₁ u₂ : α；s : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `Multiset.fold_cons_right`：fold_cons_right (b a : α) (s : Multiset α) : (
a ::ₘ s).fold op b = s.fold op b * a
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
-/
theorem fold_distrib {f g : β → α} (u₁ u₂ : α) (s : Multiset β) :
    (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * (s.map g).fold op u₂ :=
  Multiset.induction_on s (by simp) (fun a b h => by
    rw [map_cons, fold_cons_left, h, map_cons, fold_cons_left, map_cons,
      fold_cons_right, ha.assoc, ← ha.assoc (g a), hc.comm (g a),
      ha.assoc, hc.comm (g a), ha.assoc])
/-
**Multiset.fold_hom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_hom {op' : β -> β -> β} [Std.Commutative op'] [Std.Associative op'] {
m : α -> β} (hm : forall x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multise
t α) : (s.map m).fold op' (m b) = m (s.fold op b)
参数：hm : forall x y, m (op x y) = op' (m x) (m y)；b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fold_hom {op' : β → β → β} [Std.Commutative op'] [Std.Associative op'] {m : α → β}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) (b : α) (s : Multiset α) :
    (s.map m).fold op' (m b) = m (s.fold op b) :=
  Multiset.induction_on s (by simp) (by simp +contextual [hm])
/-
**Multiset.fold_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) : ((s₁ u
nion s₂).fold op b₁ * (s₁ inter s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂
参数：s₁ s₂ : Multiset α；b₁ b₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
· 使用引理 `Multiset.union_add_inter`：union_add_inter (s t : Multiset α) : s union t
 + s inter t = s + t
-/
theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
    ((s₁ ∪ s₂).fold op b₁ * (s₁ ∩ s₂).fold op b₂) = s₁.fold op b₁ * s₂.fold op b₂ := by
  rw [← fold_add op, union_add_inter, fold_add op]

@[simp]
/-
**Multiset.fold_dedup_idem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_dedup_idem [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α
) (b : α) : (dedup s).fold op b = s.fold op b
参数：s : Multiset α；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {s : Multiset α} :
 a in s -> dedup (a ::ₘ s) = dedup s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x
· 使用定理 `Multiset.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {s : Multise
t α} : a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem fold_dedup_idem [DecidableEq α] [hi : Std.IdempotentOp op] (s : Multiset α) (b : α) :
    (dedup s).fold op b = s.fold op b :=
  Multiset.induction_on s (by simp) fun a s IH => by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, fold_cons_left]
    show fold op b s = op a (fold op b s)
    rw [← cons_erase h, fold_cons_left, ← ha.assoc, hi.idempotent]

end Fold

end Multiset

