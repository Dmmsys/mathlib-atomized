/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Data.Nat.Notation

/-!
# Iterations of a function

In this file we prove simple properties of `Nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `Injective.iterate`, `Surjective.iterate`, `Bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `LeftInverse.iterate`, `RightInverse.iterate`, `Commute.iterate_left`, `Commute.iterate_right`,
  `Commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `Function.Semiconj.iterate_*`, `Function.Semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operations), then so does `f^[n]`.

-/

@[expose] public section


universe u v

variable {α : Type u} {β : Type v}

/-- Iterate a function. -/
/-
**Nat.iterate** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：{α : Sort u} → (α → α) → ℕ → α → α
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Iterate a function.
-/
def Nat.iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)

@[inherit_doc Nat.iterate]
notation:max f "^[" n "]" => Nat.iterate f n

namespace Function

open Function (Commute)

variable (f : α → α)

@[simp]
/-
**Function.iterate_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_zero : f^[0] = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_zero : f^[0] = id :=
  rfl
/-
**Function.iterate_zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_zero_apply (x : α) : f^[0] x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_zero_apply (x : α) : f^[0] x = x :=
  rfl

@[simp]
/-
**Function.iterate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_succ (n : ℕ) : f^[n.succ] = f^[n] ∘ f :=
  rfl
/-
**Function.iterate_succ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_succ_apply (n : Nat) (x : α) : f^[n.succ] x = f^[n] (f x)
参数：n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_succ_apply (n : ℕ) (x : α) : f^[n.succ] x = f^[n] (f x) :=
  rfl

@[simp]
/-
**Function.iterate_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_id (n : Nat) : (id : α -> α)^[n] = id
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
theorem iterate_id (n : ℕ) : (id : α → α)^[n] = id :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ, ihn, id_comp]
/-
**Function.iterate_add** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = f^[m] ∘ f^[n]
参数：f : α → α；m n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_add (m : ℕ) : ∀ n : ℕ, f^[m + n] = f^[m] ∘ f^[n]
  | 0 => rfl
  | Nat.succ n => by rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add m n]; rfl
/-
**Function.iterate_add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_add_apply (m n : Nat) (x : α) : f^[m + n] x = f^[m] (f^[n] x)
参数：m n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
-/
theorem iterate_add_apply (m n : ℕ) (x : α) : f^[m + n] x = f^[m] (f^[n] x) := by
  rw [iterate_add f m n]
  rfl

-- can be proved by simp but this is shorter and more natural
@[simp high]
/-
**Function.iterate_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_one : f^[1] = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem iterate_one : f^[1] = f :=
  funext fun _ ↦ rfl
/-
**Function.iterate_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = f^[m] ^[n]
参数：f : α → α；m n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_mul (m : ℕ) : ∀ n, f^[m * n] = f^[m]^[n]
  | 0 => by simp only [Nat.mul_zero, iterate_zero]
  | n + 1 => by simp only [Nat.mul_succ, iterate_one, iterate_add, iterate_mul m n]

variable {f}
/-
**Function.iterate_fixed** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n] x = x
参数：h : f x = x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
-/
theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : f^[n] x = x :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ_apply, h, ihn]

/-- If a function `g` is invariant under composition with a function `f` (i.e., `g ∘ f = g`), then
`g` is invariant under composition with any iterate of `f`. -/
/-
**Function.iterate_invariant** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_invariant {g : α -> β} (h : g ∘ f = g) (n : Nat) : g ∘ f^[n] = g
参数：h : g ∘ f = g；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `g` is invariant under composition with a function `f` (i.e., `g ∘
 f = g`), then
`g` is invariant under composition with any iterate of `f`.
-/
theorem iterate_invariant {g : α → β} (h : g ∘ f = g) (n : ℕ) : g ∘ f^[n] = g := match n with
  | 0 => by rw [iterate_zero, comp_id]
  | m + 1 => by rwa [iterate_succ, ← comp_assoc, iterate_invariant h m]
/-
**Function.Injective.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u} {f : α → α}, Function.Injective f → ∀ (n : ℕ), Function.Inj
ective f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
-/
theorem Injective.iterate (Hinj : Injective f) (n : ℕ) : Injective f^[n] :=
  Nat.recOn n injective_id fun _ ihn ↦ ihn.comp Hinj
/-
**Function.Surjective.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Type u} {f : α → α}, Function.Surjective f → ∀ (n : ℕ), Function.Su
rjective f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
-/
theorem Surjective.iterate (Hsurj : Surjective f) (n : ℕ) : Surjective f^[n] :=
  Nat.recOn n surjective_id fun _ ihn ↦ ihn.comp Hsurj
/-
**Function.Bijective.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Type u} {f : α → α}, Function.Bijective f → ∀ (n : ℕ), Function.Bij
ective f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.iterate`：∀ {α : Type u} {f : α → α}, Function.Surjec
tive f → ∀ (n : ℕ), Function.Surjective f^[n]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Bijective.iterate (Hbij : Bijective f) (n : ℕ) : Bijective f^[n] :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

namespace Semiconj

/-
**Function.Semiconj.iterate_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：iterate_right {f : α -> β} {ga : α -> α} {gb : β -> β} (h : Semiconj f ga 
gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
参数：h : Semiconj f ga gb；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.id_right`：id_right : Semiconj f id id
· 使用定理 `Function.Semiconj.comp_right`：comp_right (h : Semiconj f ga gb) (h' : Se
miconj f ga' gb') : Semiconj f (ga ∘ ga') (gb ∘ gb')
-/
theorem iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) (n : ℕ) :
    Semiconj f ga^[n] gb^[n] :=
  Nat.recOn n id_right fun _ ihn ↦ ihn.comp_right h
/-
**Function.Semiconj.iterate_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Semiconj`。
形式化陈述：iterate_left {g : Nat -> α -> α} (H : forall n, Semiconj f (g n) (g <| n +
 1)) (n k : Nat) : Semiconj f^[n] (g k) (g <| n + k)
参数：H : forall n, Semiconj f (g n) (g <| n + 1)；n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Function.Semiconj.id_left`：id_left : Semiconj id ga ga
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Function.Semiconj.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{fab : α → β} {fbc : β → γ} {ga : α → α} {gb : β → β} {gc : γ → γ},   Function.S
emiconj fab g…
-/
theorem iterate_left {g : ℕ → α → α} (H : ∀ n, Semiconj f (g n) (g <| n + 1)) (n k : ℕ) :
    Semiconj f^[n] (g k) (g <| n + k) := by
  induction n generalizing k with
  | zero =>
    rw [Nat.zero_add]
    exact id_left
  | succ n ihn =>
    rw [Nat.add_right_comm, Nat.add_assoc]
    exact (H k).trans (ihn (k + 1))

end Semiconj

namespace Commute

variable {g : α → α}

/-
**Function.Commute.iterate_right** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：iterate_right (h : Commute f g) (n : Nat) : Commute f g^[n]
参数：h : Commute f g；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.iterate_right`：iterate_right {f : α -> β} {ga : α -> α
} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
-/
theorem iterate_right (h : Commute f g) (n : ℕ) : Commute f g^[n] :=
  Semiconj.iterate_right h n
/-
**Function.Commute.iterate_left** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：iterate_left (h : Commute f g) (n : Nat) : Commute f^[n] g
参数：h : Commute f g；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
-/
theorem iterate_left (h : Commute f g) (n : ℕ) : Commute f^[n] g :=
  (h.symm.iterate_right n).symm
/-
**Function.Commute.iterate_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：iterate_iterate (h : Commute f g) (m n : Nat) : Commute f^[m] g^[n]
参数：h : Commute f g；m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
-/
theorem iterate_iterate (h : Commute f g) (m n : ℕ) : Commute f^[m] g^[n] :=
  (h.iterate_left m).iterate_right n
/-
**Function.Commute.iterate_eq_of_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Comm
ute`。
形式化陈述：iterate_eq_of_map_eq (h : Commute f g) (n : Nat) {x} (hx : f x = g x) : f^
[n] x = g^[n] x
参数：h : Commute f g；n : Nat；hx : f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `Function.Commute.refl`：refl (f : α -> α) : Commute f f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iterate_eq_of_map_eq (h : Commute f g) (n : ℕ) {x} (hx : f x = g x) :
    f^[n] x = g^[n] x :=
  Nat.recOn n rfl fun n ihn ↦ by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]
/-
**Function.Commute.comp_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：comp_iterate (h : Commute f g) (n : Nat) : (f ∘ g)^[n] = f^[n] ∘ g^[n]
参数：h : Commute f g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_iterate (h : Commute f g) (n : ℕ) : (f ∘ g)^[n] = f^[n] ∘ g^[n] := by
  induction n with
  | zero => rfl
  | succ n ihn =>
    funext x
    simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]

variable (f)
/-
**Function.Commute.iterate_self** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：iterate_self (n : Nat) : Commute f^[n] f
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_left`：iterate_left (h : Commute f g) (n : Nat) 
: Commute f^[n] g
· 使用定理 `Function.Commute.refl`：refl (f : α -> α) : Commute f f
-/
theorem iterate_self (n : ℕ) : Commute f^[n] f :=
  (refl f).iterate_left n
/-
**Function.Commute.self_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.Commute`。
形式化陈述：self_iterate (n : Nat) : Commute f f^[n]
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `Function.Commute.refl`：refl (f : α -> α) : Commute f f
-/
theorem self_iterate (n : ℕ) : Commute f f^[n] :=
  (refl f).iterate_right n
/-
**Function.Commute.iterate_iterate_self** 是 Mathlib 中的一个定理，位于命名空间 `Function.Comm
ute`。
形式化陈述：iterate_iterate_self (m n : Nat) : Commute f^[m] f^[n]
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.iterate_iterate`：iterate_iterate (h : Commute f g) (m n
 : Nat) : Commute f^[m] g^[n]
· 使用定理 `Function.Commute.refl`：refl (f : α -> α) : Commute f f
-/
theorem iterate_iterate_self (m n : ℕ) : Commute f^[m] f^[n] :=
  (refl f).iterate_iterate m n

end Commute

/-
**Function.Semiconj** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Semiconj (f : α -> β) (ga : α -> α) (gb : β -> β) : Prop
参数：f : α -> β；ga : α -> α；gb : β -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Semiconj₂.iterate {f : α → α} {op : α → α → α} (hf : Semiconj₂ f op op) (n : ℕ) :
    Semiconj₂ f^[n] op op :=
  Nat.recOn n (Semiconj₂.id_left op) fun _ ihn ↦ ihn.comp hf

variable (f)
/-
**Function.iterate_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.Semiconj.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
ga : α → α} {gb : β → β}, Function.Semiconj f ga gb → f ∘ ga = gb ∘ f
· 使用定理 `Function.Commute.self_iterate`：self_iterate (n : Nat) : Commute f f^[n]
-/
theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ f^[n] := by
  rw [iterate_succ, (Commute.self_iterate f n).comp_eq]
/-
**Function.iterate_succ_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_succ_apply' (n : Nat) (x : α) : f^[n.succ] x = f (f^[n] x)
参数：n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem iterate_succ_apply' (n : ℕ) (x : α) : f^[n.succ] x = f (f^[n] x) := by
  rw [iterate_succ']
  rfl
/-
**Function.iterate_pred_comp_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_pred_comp_of_pos {n : Nat} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n]
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem iterate_pred_comp_of_pos {n : ℕ} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] := by
  rw [← iterate_succ, Nat.succ_pred_eq_of_pos hn]
/-
**Function.comp_iterate_pred_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：comp_iterate_pred_of_pos {n : Nat} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n]
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem comp_iterate_pred_of_pos {n : ℕ} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] := by
  rw [← iterate_succ', Nat.succ_pred_eq_of_pos hn]

/-- A recursor for the iterate of a function. -/
@[elab_as_elim]
/-
**Function.Iterate.rec** 是 Mathlib 中的一个定义，位于命名空间 `Function.Iterate`。
形式化陈述：{α : Type u} →   (motive : α → Sort u_1) →     {a : α} → motive a → {f : α
 → α} → ((a : α) → motive a → motive (f a)) → (n : ℕ) → motive (f^[n] a)
参数：motive : α → Sort u_1；(a : α) → motive a → motive (f a)；n : ℕ；f^[n] a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for the iterate of a function.
-/
def Iterate.rec (motive : α → Sort*) {a : α} (arg : motive a)
    {f : α → α} (app : ∀ a, motive a → motive (f a)) (n : ℕ) : motive (f^[n] a) :=
  match n with
  | 0 => arg
  | m + 1 => Iterate.rec motive (app _ arg) app m
/-
**Function.Iterate.rec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Function.Iterate`。
形式化陈述：∀ {α : Type u} (motive : α → Sort u_1) {f : α → α} (app : (a : α) → motive
 a → motive (f a)) {a : α} (arg : motive a),   Function.Iterate.rec motive arg a
pp 0 = arg
参数：motive : α → Sort u_1；app : (a : α) → motive a → motive (f a)；arg : motive a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iterate.rec_zero (motive : α → Sort*) {f : α → α} (app : ∀ a, motive a → motive (f a))
    {a : α} (arg : motive a) : Iterate.rec motive arg app 0 = arg :=
  rfl

variable {f} {m n : ℕ} {a : α}
/-
**Function.LeftInverse.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse`。
形式化陈述：∀ {α : Type u} {f g : α → α}, Function.LeftInverse g f → ∀ (n : ℕ), Functi
on.LeftInverse g^[n] f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.LeftInverse.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β},   Function.LeftInverse f g → 
Function.LeftIn…
-/
theorem LeftInverse.iterate {g : α → α} (hg : LeftInverse g f) (n : ℕ) :
    LeftInverse g^[n] f^[n] :=
  Nat.recOn n (fun _ ↦ rfl) fun n ihn ↦ by
    rw [iterate_succ', iterate_succ]
    exact ihn.comp hg
/-
**Function.RightInverse.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInverse
`。
形式化陈述：∀ {α : Type u} {f g : α → α}, Function.RightInverse g f → ∀ (n : ℕ), Funct
ion.RightInverse g^[n] f^[n]
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.iterate`：∀ {α : Type u} {f g : α → α}, Function.Lef
tInverse g f → ∀ (n : ℕ), Function.LeftInverse g^[n] f^[n]
-/
theorem RightInverse.iterate {g : α → α} (hg : RightInverse g f) (n : ℕ) :
    RightInverse g^[n] f^[n] :=
  LeftInverse.iterate hg n
/-
**Function.iterate_comm** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_comm (f : α -> α) (m n : Nat) : f^[n]^[m] = f^[m]^[n]
参数：f : α -> α；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
-/
theorem iterate_comm (f : α → α) (m n : ℕ) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))
/-
**Function.iterate_commute** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：iterate_commute (m n : Nat) : Commute (fun f : α -> α => f^[m]) fun f => f
^[n]
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_comm`：iterate_comm (f : α -> α) (m n : Nat) : f^[n]^[m]
 = f^[m]^[n]
-/
theorem iterate_commute (m n : ℕ) : Commute (fun f : α → α ↦ f^[m]) fun f ↦ f^[n] :=
  fun f ↦ iterate_comm f m n
/-
**Function.iterate_add_eq_iterate** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：iterate_add_eq_iterate (hf : Injective f) : f^[m + n] a = f^[n] a ↔ f^[m] 
a = a
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_add_apply`：iterate_add_apply (m n : Nat) (x : α) : f^[m
 + n] x = f^[m] (f^[n] x)
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
-/
lemma iterate_add_eq_iterate (hf : Injective f) : f^[m + n] a = f^[n] a ↔ f^[m] a = a :=
  Iff.trans (by rw [← iterate_add_apply, Nat.add_comm]) (hf.iterate n).eq_iff

alias ⟨iterate_cancel_of_add, _⟩ := iterate_add_eq_iterate
/-
**Function.iterate_cancel** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：iterate_cancel (hf : Injective f) (ha : f^[m] a = f^[n] a) : f^[m - n] a =
 a
参数：hf : Injective f；ha : f^[m] a = f^[n] a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_total`：∀ (m n : ℕ), m ≤ n ∨ n ≤ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_cancel_of_add`：∀ {α : Type u} {f : α → α} {m n : ℕ} {a 
: α}, Function.Injective f → f^[m + n] a = f^[n] a → f^[m] a = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma iterate_cancel (hf : Injective f) (ha : f^[m] a = f^[n] a) : f^[m - n] a = a := by
  obtain h | h := Nat.le_total m n
  { simp [Nat.sub_eq_zero_of_le h] }
  { exact iterate_cancel_of_add hf (by rwa [Nat.sub_add_cancel h]) }
/-
**Function.involutive_iff_iter_2_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：involutive_iff_iter_2_eq_id {α} {f : α -> α} : Involutive f ↔ f^[2] = id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem involutive_iff_iter_2_eq_id {α} {f : α → α} : Involutive f ↔ f^[2] = id :=
  funext_iff.symm

end Function

namespace List

open Function

/-
**List.foldl_const** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_const (f : α -> α) (a : α) (l : List β) : l.foldl (fun b _ => f b) a
 = f^[l.length] a
参数：f : α -> α；a : α；l : List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).length
 = as.length + 1
· 使用定理 `List.foldl.eq_2`：∀ {α : Type u} {β : Type v} (f : α → β → α) (x : α) (b 
: β) (l : List β),   List.foldl f x (b :: l) = List.foldl f (f x b) l
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
-/
theorem foldl_const (f : α → α) (a : α) (l : List β) :
    l.foldl (fun b _ ↦ f b) a = f^[l.length] a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l H => rw [length_cons, foldl, iterate_succ_apply, H]
/-
**List.foldr_const** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : β → β) (b : β) (l : List α), List.foldr (
fun x => f) b l = f^[l.length] b
参数：f : β → β；b : β；l : List α；fun x => f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_const (f : β → β) (b : β) : ∀ l : List α, l.foldr (fun _ ↦ f) b = f^[l.length] b
  | [] => rfl
  | a :: l => by rw [length_cons, foldr, foldr_const f b l, iterate_succ_apply']

end List

namespace Pi

variable {ι : Type*}

@[simp]
/-
**Pi.map_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：map_iterate {α : ι -> Type*} (f : forall i, α i -> α i) (n : Nat) : (Pi.ma
p f)^[n] = Pi.map fun i => (f i)^[n]
参数：f : forall i, α i -> α i；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_iterate {α : ι → Type*} (f : ∀ i, α i → α i) (n : ℕ) :
    (Pi.map f)^[n] = Pi.map fun i => (f i)^[n] := by
  induction n <;> simp [*, map_comp_map]

end Pi

