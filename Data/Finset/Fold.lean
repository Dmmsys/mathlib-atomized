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

variable (op : β → β → β) [hc : Std.Commutative op] [ha : Std.Associative op]

local notation a " * " b => op a b

/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`. -/
/-
**Finset.fold** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：fold (b : β) (f : α -> β) (s : Finset α) : β
参数：b : β；f : α -> β；s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`.
-/
def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b

variable {op} {f : α → β} {b : β} {s : Finset α} {a : α}

@[simp]
/-
**Finset.fold_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_empty : (∅ : Finset α).fold op b f = b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fold_empty : (∅ : Finset α).fold op b f = b :=
  rfl

@[simp]
/-
**Finset.fold_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_val`：cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
-/
theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f := by
  dsimp only [fold]
  rw [cons_val, Multiset.map_cons, fold_cons_left]

@[simp]
/-
**Finset.fold_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a s).fold op b f = f a *
 s.fold op b f
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_val`：insert_val (a : α) (s : Finset α) : (insert a s).1 = 
ndinsert a s.1
· 使用定理 `Multiset.ndinsert_of_notMem`：ndinsert_of_notMem {a : α} {s : Multiset α}
 : a ∉ s -> ndinsert a s = a ::ₘ s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
-/
theorem fold_insert [DecidableEq α] (h : a ∉ s) :
    (insert a s).fold op b f = f a * s.fold op b f := by
  unfold fold
  rw [insert_val, ndinsert_of_notMem h, Multiset.map_cons, fold_cons_left]

@[simp]
/-
**Finset.fold_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_singleton : ({a} : Finset α).fold op b f = f a * b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fold_singleton : ({a} : Finset α).fold op b f = f a * b :=
  rfl

@[simp]
/-
**Finset.fold_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b 
(f ∘ g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, map, Multiset.map_map]

@[simp]
/-
**Finset.fold_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_image [DecidableEq α] {g : γ -> α} {s : Finset γ} (H : Set.InjOn g s)
 : (s.image g).fold op b f = s.fold op b (f ∘ g)
参数：H : Set.InjOn g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Finset.image_val_of_injOn`：image_val_of_injOn (H : Set.InjOn f s) : (ima
ge f s).1 = s.1.map f
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_image [DecidableEq α] {g : γ → α} {s : Finset γ}
    (H : Set.InjOn g s) : (s.image g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, image_val_of_injOn H, Multiset.map_map]

@[congr]
/-
**Finset.fold_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_congr {g : α -> β} (H : forall x in s, f x = g x) : s.fold op b f = s
.fold op b g
参数：H : forall x in s, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold.eq_1`：∀ {α : Type u_1} {β : Type u_2} (op : β → β → β) [hc :
 Std.Commutative op] [ha : Std.Associative op] (b : β) (f : α → β)   (s : Finset
 α), F…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
-/
theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g := by
  rw [fold, fold, map_congr rfl H]
/-
**Finset.fold_op_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_op_distrib {f g : α -> β} {b₁ b₂ : β} : (s.fold op (b₁ * b₂) fun x =>
 f x * g x) = s.fold op b₁ f * s.fold op b₂ g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold_distrib`：fold_distrib {f g : β -> α} (u₁ u₂ : α) (s : Mult
iset β) : (s.map fun x => f x * g x).fold op (u₁ * u₂) = (s.map f).fold op u₁ * 
(s.map g).f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
    (s.fold op (b₁ * b₂) fun x => f x * g x) = s.fold op b₁ f * s.fold op b₂ g := by
  simp only [fold, fold_distrib]
/-
**Finset.fold_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_const [hd : Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c) :
 Finset.fold op b (fun _ => c) s = if s = ∅ then b else op b c
参数：s = ∅；c : β；h : op c (op b c) = op b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
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
/-
**Finset.fold_hom** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_hom {op' : γ -> γ -> γ} [Std.Commutative op'] [Std.Associative op'] {
m : β -> γ} (hm : forall x y, m (op x y) = op' (m x) (m y)) : (s.fold op' (m b) 
fun x => m (f x)) = m (s.fold op b f)
参数：hm : forall x y, m (op x y) = op' (m x) (m y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold.eq_1`：∀ {α : Type u_1} {β : Type u_2} (op : β → β → β) [hc :
 Std.Commutative op] [ha : Std.Associative op] (b : β) (f : α → β)   (s : Finset
 α), F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.fold_hom`：fold_hom {op' : β -> β -> β} [Std.Commutative op'] [S
td.Associative op'] {m : α -> β} (hm : forall x y, m (op x y) = op' (m x) (m y))
 (b : α…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_hom {op' : γ → γ → γ} [Std.Commutative op'] [Std.Associative op'] {m : β → γ}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) :
    (s.fold op' (m b) fun x => m (f x)) = m (s.fold op b f) := by
  rw [fold, fold, ← Multiset.fold_hom op hm, Multiset.map_map]
  simp only [Function.comp_apply]
/-
**Finset.fold_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h) : (s₁.disjUnion s₂ h).fo
ld op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f
参数：h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
-/
theorem fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h) :
    (s₁.disjUnion s₂ h).fold op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f :=
  (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)
/-
**Finset.fold_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_union_inter [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β} : ((s₁ uni
on s₂).fold op b₁ f * (s₁ inter s₂).fold op b₂ f) = s₁.fold op b₂ f * s₂.fold op
 b₁ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Finset.union_val`：union_val (s t : Finset α) : (s union t).1 = s.1 union
 t.1
· 使用定理 `Finset.inter_val`：inter_val (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = s₁.1 
inter s₂.1
· 使用引理 `Multiset.union_add_inter`：union_add_inter (s t : Multiset α) : s union t
 + s inter t = s + t
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
-/
theorem fold_union_inter [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β} :
    ((s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f) = s₁.fold op b₂ f * s₂.fold op b₁ f := by
  unfold fold
  rw [← fold_add op, ← Multiset.map_add, union_val, inter_val, union_add_inter, Multiset.map_add,
    hc.comm, fold_add]

@[simp]
/-
**Finset.fold_insert_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_insert_idem [DecidableEq α] [hi : Std.IdempotentOp op] : (insert a s)
.fold op b f = f a * s.fold op b f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.fold.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (op op_1 : β → β
 → β) (e_op : op = op_1) [hc : Std.Commutative op]   [ha : Std.Associative op] (
b b_1 : β), …
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x
-/
theorem fold_insert_idem [DecidableEq α] [hi : Std.IdempotentOp op] :
    (insert a s).fold op b f = f a * s.fold op b f := by
  by_cases h : a ∈ s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h
/-
**Finset.fold_image_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_image_idem [DecidableEq α] {g : γ -> α} {s : Finset γ} [hi : Std.Idem
potentOp op] : (image g s).fold op b f = s.fold op b (f ∘ g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold_empty`：fold_empty : (∅ : Finset α).fold op b f = b
· 使用定理 `Finset.image_empty`：image_empty (f : α -> β) : (∅ : Finset α).image f = 
∅
· 使用定理 `Finset.fold_cons`：fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a
 * s.fold op b f
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Finset.fold_insert_idem`：fold_insert_idem [DecidableEq α] [hi : Std.Idem
potentOp op] : (insert a s).fold op b f = f a * s.fold op b f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fold_image_idem [DecidableEq α] {g : γ → α} {s : Finset γ} [hi : Std.IdempotentOp op] :
    (image g s).fold op b f = s.fold op b (f ∘ g) := by
  induction s using Finset.cons_induction with
  | empty => rw [fold_empty, image_empty, fold_empty]
  | cons x xs hx ih =>
    have := Classical.decEq γ
    rw [fold_cons, cons_eq_insert, image_insert, fold_insert_idem, ih]
    simp only [Function.comp_apply]

/-- A stronger version of `Finset.fold_ite`, but relies on
an explicit proof of idempotency on the seed element, rather
than relying on typeclass idempotency over the whole type. -/
/-
**Finset.fold_ite'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_ite' {g : α -> β} (hb : op b b = b) (p : α -> Prop) [DecidablePred p]
 : Finset.fold op b (fun i => ite (p i) (f i) (g i)) s = op (Finset.fold op b f 
(s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i))
参数：hb : op b b = b；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.fold.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (op op_1 : β → β
 → β) (e_op : op = op_1) [hc : Std.Commutative op]   [ha : Std.Associative op] (
b b_1 : β), …
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a

--- 原说明 ---
A stronger version of `Finset.fold_ite`, but relies on
an explicit proof of idempotency on the seed element, rather
than relying on typeclass idempotency over the whole type.
-/
theorem fold_ite' {g : α → β} (hb : op b b = b) (p : α → Prop) [DecidablePred p] :
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

/-- A weaker version of `Finset.fold_ite'`,
relying on typeclass idempotency over the whole type,
instead of solely on the seed element.
However, this is easier to use because it does not generate side goals. -/
/-
**Finset.fold_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_ite [Std.IdempotentOp op] {g : α -> β} (p : α -> Prop) [DecidablePred
 p] : Finset.fold op b (fun i => ite (p i) (f i) (g i)) s = op (Finset.fold op b
 f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i))
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_ite'`：fold_ite' {g : α -> β} (hb : op b b = b) (p : α -> Pro
p) [DecidablePred p] : Finset.fold op b (fun i => ite (p i) (f i) (g i)) s = op 
(Finse…
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x

--- 原说明 ---
A weaker version of `Finset.fold_ite'`,
relying on typeclass idempotency over the whole type,
instead of solely on the seed element.
However, this is easier to use because it does not generate side goals.
-/
theorem fold_ite [Std.IdempotentOp op] {g : α → β} (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  fold_ite' (Std.IdempotentOp.idempotent _) _
/-
**Finset.fold_op_rel_iff_and** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_op_rel_iff_and {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z
) ↔ r x y ∧ r x z) {c : β} : r c (s.fold op b f) ↔ r c b ∧ forall x in s, r c (f
 x)
参数：hr : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem fold_op_rel_iff_and {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∧ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∧ ∀ x ∈ s, r c (f x) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha, hr, IH, ← and_assoc, @and_comm (r c (f a)), and_assoc]
      simp
/-
**Finset.fold_op_rel_iff_or** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_op_rel_iff_or {r : β -> β -> Prop} (hr : forall {x y z}, r x (op y z)
 ↔ r x y ∨ r x z) {c : β} : r c (s.fold op b f) ↔ r c b ∨ exists x in s, r c (f 
x)
参数：hr : forall {x y z}, r x (op y z) ↔ r x y ∨ r x z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem fold_op_rel_iff_or {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∨ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∨ ∃ x ∈ s, r c (f x) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha IH =>
      rw [Finset.fold_insert ha, hr, IH, ← or_assoc, @or_comm (r c (f a)), or_assoc]
      simp

@[simp]
/-
**Finset.fold_union_empty_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_union_empty_singleton [DecidableEq α] (s : Finset α) : Finset.fold (·
 union ·) ∅ singleton s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Finset.instCommutativeUnion`：∀ {α : Type u_1} [inst : DecidableEq α], St
d.Commutative fun x1 x2 => x1 ∪ x2
· 使用定理 `Finset.instAssociativeUnion`：∀ {α : Type u_1} [inst : DecidableEq α], St
d.Associative fun x1 x2 => x1 ∪ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
-/
theorem fold_union_empty_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ∪ ·) ∅ singleton s = s := by
  induction s using Finset.induction_on with
  | empty => simp only [fold_empty]
  | insert a s has ih => rw [fold_insert has, ih, insert_eq]
/-
**Finset.fold_sup_bot_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_sup_bot_singleton [DecidableEq α] (s : Finset α) : Finset.fold (· ⊔ ·
) ⊥ singleton s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_union_empty_singleton`：fold_union_empty_singleton [Decidable
Eq α] (s : Finset α) : Finset.fold (· union ·) ∅ singleton s = s
-/
theorem fold_sup_bot_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ⊔ ·) ⊥ singleton s = s :=
  fold_union_empty_singleton s

section Order

variable [LinearOrder β] (c : β)

/-
**Finset.le_fold_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_fold_min : c <= s.fold min b f ↔ c <= b ∧ forall x in s, c <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_op_rel_iff_and`：fold_op_rel_iff_and {r : β -> β -> Prop} (hr
 : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z) {c : β} : r c (s.fold op b f) ↔
 r c b ∧ forall …
· 使用定理 `instCommutativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve min
· 使用定理 `instAssociativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve min
· 使用定理 `le_min_iff`：le_min_iff : c <= min a b ↔ c <= a ∧ c <= b
-/
theorem le_fold_min : c ≤ s.fold min b f ↔ c ≤ b ∧ ∀ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_and le_min_iff
/-
**Finset.fold_min_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_min_le : s.fold min b f <= c ↔ b <= c ∨ exists x in s, f x <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve min
· 使用定理 `instAssociativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve min
· 使用定理 `Finset.fold_op_rel_iff_or`：fold_op_rel_iff_or {r : β -> β -> Prop} (hr :
 forall {x y z}, r x (op y z) ↔ r x y ∨ r x z) {c : β} : r c (s.fold op b f) ↔ r
 c b ∨ exists x…
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
-/
theorem fold_min_le : s.fold min b f ≤ c ↔ b ≤ c ∨ ∃ x ∈ s, f x ≤ c := by
  change _ ≥ _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ ≤ _ ↔ _
  exact min_le_iff
/-
**Finset.lt_fold_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_fold_min : c < s.fold min b f ↔ c < b ∧ forall x in s, c < f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_op_rel_iff_and`：fold_op_rel_iff_and {r : β -> β -> Prop} (hr
 : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z) {c : β} : r c (s.fold op b f) ↔
 r c b ∧ forall …
· 使用定理 `instCommutativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve min
· 使用定理 `instAssociativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve min
· 使用定理 `lt_min_iff`：lt_min_iff : a < min b c ↔ a < b ∧ a < c
-/
theorem lt_fold_min : c < s.fold min b f ↔ c < b ∧ ∀ x ∈ s, c < f x :=
  fold_op_rel_iff_and lt_min_iff
/-
**Finset.fold_min_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_min_lt : s.fold min b f < c ↔ b < c ∨ exists x in s, f x < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve min
· 使用定理 `instAssociativeMin`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve min
· 使用定理 `Finset.fold_op_rel_iff_or`：fold_op_rel_iff_or {r : β -> β -> Prop} (hr :
 forall {x y z}, r x (op y z) ↔ r x y ∨ r x z) {c : β} : r c (s.fold op b f) ↔ r
 c b ∨ exists x…
· 使用定理 `min_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c <
 a ↔ b < a ∨ c < a
-/
theorem fold_min_lt : s.fold min b f < c ↔ b < c ∨ ∃ x ∈ s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  change _ < _ ↔ _
  exact min_lt_iff
/-
**Finset.fold_max_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_max_le : s.fold max b f <= c ↔ b <= c ∧ forall x in s, f x <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `Finset.fold_op_rel_iff_and`：fold_op_rel_iff_and {r : β -> β -> Prop} (hr
 : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z) {c : β} : r c (s.fold op b f) ↔
 r c b ∧ forall …
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
-/
theorem fold_max_le : s.fold max b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c := by
  change _ ≥ _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ ≤ _ ↔ _
  exact max_le_iff
/-
**Finset.le_fold_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_fold_max : c <= s.fold max b f ↔ c <= b ∨ exists x in s, c <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_op_rel_iff_or`：fold_op_rel_iff_or {r : β -> β -> Prop} (hr :
 forall {x y z}, r x (op y z) ↔ r x y ∨ r x z) {c : β} : r c (s.fold op b f) ↔ r
 c b ∨ exists x…
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
-/
theorem le_fold_max : c ≤ s.fold max b f ↔ c ≤ b ∨ ∃ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_or le_max_iff
/-
**Finset.fold_max_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_max_lt : s.fold max b f < c ↔ b < c ∧ forall x in s, f x < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `Finset.fold_op_rel_iff_and`：fold_op_rel_iff_and {r : β -> β -> Prop} (hr
 : forall {x y z}, r x (op y z) ↔ r x y ∧ r x z) {c : β} : r c (s.fold op b f) ↔
 r c b ∧ forall …
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
-/
theorem fold_max_lt : s.fold max b f < c ↔ b < c ∧ ∀ x ∈ s, f x < c := by
  change _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  change _ < _ ↔ _
  exact max_lt_iff
/-
**Finset.lt_fold_max** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_fold_max : c < s.fold max b f ↔ c < b ∨ exists x in s, c < f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_op_rel_iff_or`：fold_op_rel_iff_or {r : β -> β -> Prop} (hr :
 forall {x y z}, r x (op y z) ↔ r x y ∨ r x z) {c : β} : r c (s.fold op b f) ↔ r
 c b ∨ exists x…
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
-/
theorem lt_fold_max : c < s.fold max b f ↔ c < b ∨ ∃ x ∈ s, c < f x :=
  fold_op_rel_iff_or lt_max_iff

end Order

end Fold

end Finset

