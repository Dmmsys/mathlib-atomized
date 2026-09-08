/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` too much because it can't map `Multiplicative ℕ` to `ℕ`.
-/

@[expose] public section

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeMonoid
/-- `List.countP` lifted to free monoids -/
@[to_additive /-- `List.countP` lifted to free additive monoids -/]
/-
**FreeMonoid.countP'** 是 Mathlib 中的一个定义，位于命名空间 `FreeMonoid`。
形式化陈述：countP' (l : FreeMonoid α) : Nat
参数：l : FreeMonoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.countP` lifted to free monoids
-/
def countP' (l : FreeMonoid α) : ℕ := l.toList.countP p

@[to_additive]
/-
**FreeMonoid.countP'_one** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p], FreeMonoid.count
P' p 1 = 0
参数：p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma countP'_one : (1 : FreeMonoid α).countP' p = 0 := rfl

@[to_additive]
/-
**FreeMonoid.countP'_mul** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p] (l₁ l₂ : FreeMono
id α),   FreeMonoid.countP' p (l₁ * l₂) = FreeMonoid.countP' p l₁ + FreeMonoid.c
ountP' p l₂
参数：p : α → Prop；l₁ l₂ : FreeMonoid α；l₁ * l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_append`：∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}, Li
st.countP p (l₁ ++ l₂) = List.countP p l₁ + List.countP p l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  dsimp [countP']
  simp only [List.countP_append]

/-- `List.countP` as a bundled multiplicative monoid homomorphism. -/
/-
**FreeMonoid.countP** 是 Mathlib 中的一个定义，位于命名空间 `FreeMonoid`。
形式化陈述：countP : FreeMonoid α ->* Multiplicative Nat where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.countP` as a bundled multiplicative monoid homomorphism.
-/
def countP : FreeMonoid α →* Multiplicative ℕ where
  toFun := .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]
/-
**FreeMonoid.countP_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p)
参数：l : FreeMonoid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p) := rfl
/-
**FreeMonoid.countP_of** 是 Mathlib 中的一个引理，位于命名空间 `FreeMonoid`。
形式化陈述：countP_of (x : α) : (of x).countP p = if p x then Multiplicative.ofAdd 1 e
lse Multiplicative.ofAdd 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeMonoid.countP_apply`：countP_apply (l : FreeMonoid α) : l.countP p = 
.ofAdd (l.toList.countP p)
· 使用定理 `FreeMonoid.toList_of`：toList_of (x : α) : toList (of x) = [x]
· 使用定理 `List.countP_singleton`：∀ {α : Type u_1} {p : α → Bool} {a : α}, List.cou
ntP p [a] = if p a = true then 1 else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma countP_of (x : α) : (of x).countP p =
    if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
  rw [countP_apply, toList_of, List.countP_singleton, apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]


/-- `List.count` as a bundled additive monoid homomorphism. -/
/-
**FreeMonoid.count** 是 Mathlib 中的一个定义，位于命名空间 `FreeMonoid`。
形式化陈述：count [DecidableEq α] (x : α) : FreeMonoid α ->* Multiplicative Nat
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.count` as a bundled additive monoid homomorphism.
-/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)
/-
**FreeMonoid.count_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : count x l = Mu
ltiplicative.ofAdd (l.toList.count x)
参数：x : α；l : FreeAddMonoid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (l.toList.count x) := rfl
/-
**FreeMonoid.count_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeMonoid`。
形式化陈述：count_of [DecidableEq α] (x y : α) : count x (of y) = Pi.mulSingle (M
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FreeMonoid.countP_of`：countP_of (x : α) : (of x).countP p = if p x then 
Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Pi.mulSingle_apply`：mulSingle_apply (i : ι) (x : M) (i' : ι) : (mulSingl
e i x : ι -> M) i' = if i' = i then x else 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = Pi.mulSingle (M := fun _ ↦ Multiplicative ℕ) x (Multiplicative.ofAdd 1) y := by
  simp [count, countP_of, Pi.mulSingle_apply]

end FreeMonoid

namespace FreeAddMonoid

/-- `List.countP` as a bundled additive monoid homomorphism. -/
/-
**FreeAddMonoid.countP** 是 Mathlib 中的一个定义，位于命名空间 `FreeAddMonoid`。
形式化陈述：countP : FreeAddMonoid α ->+ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FreeAddMonoid.countP'_zero`：∀ {α : Type u_1} (p : α → Prop) [inst : Deci
dablePred p], FreeAddMonoid.countP' p 0 = 0
· 使用定理 `FreeAddMonoid.countP'_add`：∀ {α : Type u_1} (p : α → Prop) [inst : Decid
ablePred p] (l₁ l₂ : FreeAddMonoid α),   FreeAddMonoid.countP' p (l₁ + l₂) = Fre
eAddMonoid.coun…

--- 原说明 ---
`List.countP` as a bundled additive monoid homomorphism.
-/
def countP : FreeAddMonoid α →+ ℕ where
  toFun := FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p
/-
**FreeAddMonoid.countP_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeAddMonoid`。
形式化陈述：countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p
参数：l : FreeAddMonoid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p := rfl
/-
**FreeAddMonoid.countP_of** 是 Mathlib 中的一个定理，位于命名空间 `FreeAddMonoid`。
形式化陈述：countP_of (x : α) : countP p (of x) = if p x then 1 else 0
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAddMonoid.countP_apply`：countP_apply (l : FreeAddMonoid α) : l.count
P p = l.toList.countP p
· 使用定理 `FreeAddMonoid.toList_of`：∀ {α : Type u_1} (x : α), FreeAddMonoid.toList 
(FreeAddMonoid.of x) = [x]
· 使用定理 `List.countP_singleton`：∀ {α : Type u_1} {p : α → Bool} {a : α}, List.cou
ntP p [a] = if p a = true then 1 else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem countP_of (x : α) : countP p (of x) = if p x then 1 else 0 := by
  rw [countP_apply, toList_of, List.countP_singleton]
  simp only [decide_eq_true_eq]

/-- `List.count` as a bundled additive monoid homomorphism. -/
-- Porting note: was (x = ·)
/-
**FreeAddMonoid.count** 是 Mathlib 中的一个定义，位于命名空间 `FreeAddMonoid`。
形式化陈述：count [DecidableEq α] (x : α) : FreeAddMonoid α ->+ Nat
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)
/-
**FreeAddMonoid.count_of** 是 Mathlib 中的一个引理，位于命名空间 `FreeAddMonoid`。
形式化陈述：count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α -
> Nat) y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FreeAddMonoid.countP_of`：countP_of (x : α) : countP p (of x) = if p x th
en 1 else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]
/-
**FreeAddMonoid.count_apply** 是 Mathlib 中的一个定理，位于命名空间 `FreeAddMonoid`。
形式化陈述：count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.
toList.count x
参数：x : α；l : FreeAddMonoid α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.toList.count x :=
  rfl

end FreeAddMonoid

