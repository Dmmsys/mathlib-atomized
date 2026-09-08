/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Algebraic properties of tuples
-/

public section

namespace Fin
variable {n : ℕ} {α : Fin (n + 1) → Type*}

@[to_additive (attr := simp)]
/-
**Fin.insertNth_one_right** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_one_right [forall j, One (α j)] (i : Fin (n + 1)) (x : α i) : i.
insertNth x 1 = Pi.mulSingle i x
参数：α j；i : Fin (n + 1)；x : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.insertNth_eq_iff`：insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : 
forall i, α (p.succAbove i)} {g : forall j, α j} : insertNth p a f = g ↔ a = g p
 ∧ f = rem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma insertNth_one_right [∀ j, One (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 1 = Pi.mulSingle i x :=
  insertNth_eq_iff.2 <| by unfold removeNth; simp [succAbove_ne, Pi.one_def]

@[to_additive (attr := simp)]
/-
**Fin.insertNth_mul** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_mul [forall j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : f
orall j, α (i.succAbove j)) : i.insertNth (x * y) (p * q) = i.insertNth x p * i.
insertNth y q
参数：α j；i : Fin (n + 1)；x y : α i；p q : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.insertNth_binop`：insertNth_binop (op : forall j, α j -> α j -> α j) 
(i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j)) : (i.insertNth
 (op i x …
-/
lemma insertNth_mul [∀ j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· * ·)) i x y p q

@[to_additive (attr := simp)]
/-
**Fin.insertNth_div** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_div [forall j, Div (α j)] (i : Fin (n + 1)) (x y : α i) (p q : f
orall j, α (i.succAbove j)) : i.insertNth (x / y) (p / q) = i.insertNth x p / i.
insertNth y q
参数：α j；i : Fin (n + 1)；x y : α i；p q : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.insertNth_binop`：insertNth_binop (op : forall j, α j -> α j -> α j) 
(i : Fin (n + 1)) (x y : α i) (p q : forall j, α (i.succAbove j)) : (i.insertNth
 (op i x …
-/
lemma insertNth_div [∀ j, Div (α j)] (i : Fin (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· / ·)) i x y p q

@[to_additive (attr := simp)]
/-
**Fin.insertNth_div_same** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_div_same [forall j, Group (α j)] (i : Fin (n + 1)) (x y : α i) (
p : forall j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSin
gle i (x / y)
参数：α j；i : Fin (n + 1)；x y : α i；p : forall j, α (i.succAbove j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma insertNth_div_same [∀ j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSingle i (x / y) := by
  simp_rw [← insertNth_div, ← insertNth_one_right, Pi.div_def, div_self', Pi.one_def]

end Fin

namespace Matrix

variable {α M : Type*} {n : ℕ}

section SMul
variable [SMul M α]

/-
**Matrix.smul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x : M) (v : Fin 0 → α),
 x • v = ![]
参数：x : M；v : Fin 0 → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
@[simp] lemma smul_empty (x : M) (v : Fin 0 → α) : x • v = ![] := empty_eq _
/-
**Matrix.smul_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M α] (x : M) (y : α) 
(v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (x • y) (x • v)
参数：x : M；y : α；v : Fin n → α；x • y；x • v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma smul_cons (x : M) (y : α) (v : Fin n → α) :
    x • vecCons y v = vecCons (x • y) (x • v) := by ext i; refine i.cases ?_ ?_ <;> simp

end SMul

section Add
variable [Add α]

/-
**Matrix.empty_add_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} [inst : Add α] (v w : Fin 0 → α), v + w = ![]
参数：v w : Fin 0 → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
@[simp] lemma empty_add_empty (v w : Fin 0 → α) : v + w = ![] := empty_eq _
/-
**Matrix.cons_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (x : α) (v : Fin n → α) (w : Fin n
.succ → α),   Matrix.vecCons x v + w = Matrix.vecCons (x + Matrix.vecHead w) (v 
+ Matrix.vecTail w)
参数：x : α；v : Fin n → α；w : Fin n.succ → α；x + Matrix.vecHead w；v + Matrix.vecTai
l w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma cons_add (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v + w = vecCons (x + vecHead w) (v + vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
/-
**Matrix.add_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ → α) (y : α) (w : 
Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix.vecHead v + y) (Ma
trix.vecTail v + w)
参数：v : Fin n.succ → α；y : α；w : Fin n → α；Matrix.vecHead v + y；Matrix.vecTail v 
+ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma add_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v + vecCons y w = vecCons (vecHead v + y) (vecTail v + w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
/-
**Matrix.cons_add_cons** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_add_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) : vecCons 
x v + vecCons y w = vecCons (x + y) (v + w)
参数：x : α；v : Fin n -> α；y : α；w : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.add_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v + Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_add_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by simp
/-
**Matrix.head_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (a b : Fin n.succ → α),   Matrix.v
ecHead (a + b) = Matrix.vecHead a + Matrix.vecHead b
参数：a b : Fin n.succ → α；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_add (a b : Fin n.succ → α) : vecHead (a + b) = vecHead a + vecHead b := rfl
/-
**Matrix.tail_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Add α] (a b : Fin n.succ → α),   Matrix.v
ecTail (a + b) = Matrix.vecTail a + Matrix.vecTail b
参数：a b : Fin n.succ → α；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tail_add (a b : Fin n.succ → α) : vecTail (a + b) = vecTail a + vecTail b := rfl

end Add

section Sub
variable [Sub α]

/-
**Matrix.empty_sub_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} [inst : Sub α] (v w : Fin 0 → α), v - w = ![]
参数：v w : Fin 0 → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
@[simp] lemma empty_sub_empty (v w : Fin 0 → α) : v - w = ![] := empty_eq _
/-
**Matrix.cons_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Sub α] (x : α) (v : Fin n → α) (w : Fin n
.succ → α),   Matrix.vecCons x v - w = Matrix.vecCons (x - Matrix.vecHead w) (v 
- Matrix.vecTail w)
参数：x : α；v : Fin n → α；w : Fin n.succ → α；x - Matrix.vecHead w；v - Matrix.vecTai
l w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma cons_sub (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v - w = vecCons (x - vecHead w) (v - vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
/-
**Matrix.sub_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Sub α] (v : Fin n.succ → α) (y : α) (w : 
Fin n → α),   v - Matrix.vecCons y w = Matrix.vecCons (Matrix.vecHead v - y) (Ma
trix.vecTail v - w)
参数：v : Fin n.succ → α；y : α；w : Fin n → α；Matrix.vecHead v - y；Matrix.vecTail v 
- w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma sub_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v - vecCons y w = vecCons (vecHead v - y) (vecTail v - w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
/-
**Matrix.cons_sub_cons** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_sub_cons (x : α) (v : Fin n -> α) (y : α) (w : Fin n -> α) : vecCons 
x v - vecCons y w = vecCons (x - y) (v - w)
参数：x : α；v : Fin n -> α；y : α；w : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.sub_cons`：∀ {α : Type u_1} {n : ℕ} [inst : Sub α] (v : Fin n.succ
 → α) (y : α) (w : Fin n → α),   v - Matrix.vecCons y w = Matrix.vecCons (Matrix
.vecH…
· 使用定理 `Matrix.tail_cons`：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons 
x u) = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cons_sub_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp
/-
**Matrix.head_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Sub α] (a b : Fin n.succ → α),   Matrix.v
ecHead (a - b) = Matrix.vecHead a - Matrix.vecHead b
参数：a b : Fin n.succ → α；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_sub (a b : Fin n.succ → α) : vecHead (a - b) = vecHead a - vecHead b := rfl
/-
**Matrix.tail_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Sub α] (a b : Fin n.succ → α),   Matrix.v
ecTail (a - b) = Matrix.vecTail a - Matrix.vecTail b
参数：a b : Fin n.succ → α；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tail_sub (a b : Fin n.succ → α) : vecTail (a - b) = vecTail a - vecTail b := rfl

end Sub

section Zero
variable [Zero α]

/-
**Matrix.zero_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
@[simp] lemma zero_empty : (0 : Fin 0 → α) = ![] := empty_eq _
/-
**Matrix.finZeroElim_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} [inst : Zero α], finZeroElim = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
-/
@[simp] lemma finZeroElim_eq_zero : (@finZeroElim fun _ ↦ α) = 0 := by
  rw [Matrix.empty_eq finZeroElim, Matrix.zero_empty]
/-
**Matrix.cons_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Zero α], Matrix.vecCons 0 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma cons_zero_zero : vecCons (0 : α) (0 : Fin n → α) = 0 := by
  ext i; exact i.cases rfl (by simp)
/-
**Matrix.head_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Zero α], Matrix.vecHead 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_zero : vecHead (0 : Fin n.succ → α) = 0 := rfl
/-
**Matrix.tail_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Zero α], Matrix.vecTail 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tail_zero : vecTail (0 : Fin n.succ → α) = 0 := rfl
/-
**Matrix.cons_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Zero α] {v : Fin n → α} {x : α}, Matrix.v
ecCons x v = 0 ↔ x = 0 ∧ v = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_zero_zero`：∀ {α : Type u_1} {n : ℕ} [inst : Zero α], Matrix.
vecCons 0 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma cons_eq_zero_iff {v : Fin n → α} {x : α} : vecCons x v = 0 ↔ x = 0 ∧ v = 0 where
  mp h := ⟨congr_fun h 0, by convert! congr_arg vecTail h⟩
  mpr := fun ⟨hx, hv⟩ ↦ by simp [hx, hv]
/-
**Matrix.cons_nonzero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_nonzero_iff {v : Fin n -> α} {x : α} : vecCons x v != 0 ↔ x != 0 ∨ v 
!= 0 where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.cons_eq_zero_iff`：∀ {α : Type u_1} {n : ℕ} [inst : Zero α] {v : F
in n → α} {x : α}, Matrix.vecCons x v = 0 ↔ x = 0 ∧ v = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
lemma cons_nonzero_iff {v : Fin n → α} {x : α} : vecCons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 where
  mp h := not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)

end Zero

section Neg
variable [Neg α]

/-
**Matrix.neg_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} [inst : Neg α] (v : Fin 0 → α), -v = ![]
参数：v : Fin 0 → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
@[simp] lemma neg_empty (v : Fin 0 → α) : -v = ![] := empty_eq _
/-
**Matrix.neg_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Neg α] (x : α) (v : Fin n → α), -Matrix.v
ecCons x v = Matrix.vecCons (-x) (-v)
参数：x : α；v : Fin n → α；-x；-v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma neg_cons (x : α) (v : Fin n → α) : -vecCons x v = vecCons (-x) (-v) := by
  ext i; refine i.cases ?_ ?_ <;> simp
/-
**Matrix.head_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Neg α] (a : Fin n.succ → α), Matrix.vecHe
ad (-a) = -Matrix.vecHead a
参数：a : Fin n.succ → α；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma head_neg (a : Fin n.succ → α) : vecHead (-a) = -vecHead a := rfl
/-
**Matrix.tail_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} [inst : Neg α] (a : Fin n.succ → α), Matrix.vecTa
il (-a) = -Matrix.vecTail a
参数：a : Fin n.succ → α；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma tail_neg (a : Fin n.succ → α) : vecTail (-a) = -vecTail a := rfl

end Neg
end Matrix

