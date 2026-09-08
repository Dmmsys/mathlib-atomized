/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about pointwise operations in the presence of `Multiplicative` and `Additive`.
-/

public section

open scoped Pointwise

variable {M : Type*}

namespace Multiplicative

variable [AddMonoid M]

@[simp]
/-
**Multiplicative.ofAdd_image_setAdd** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd_image_setAdd (s t : Set M) : ofAdd '' (s + t) = ofAdd '' s * ofAdd '
' t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, Set.image
2 (fun x1 x2 => x1 + x2) s t = s + t
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `ofAdd_add`：ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd
 y
· 使用定理 `Set.image2_mul`：image2_mul : image2 (· * ·) s t = s * t
-/
lemma ofAdd_image_setAdd (s t : Set M) :
    ofAdd '' (s + t) = ofAdd '' s * ofAdd '' t := by
  rw [← Set.image2_add, Set.image_image2_distrib ofAdd_add, Set.image2_mul]

@[simp]
/-
**Multiplicative.ofAdd_image_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd_image_nsmul (n : Nat) (s : Set M) : ofAdd '' (n • s) = (ofAdd '' s) 
^ n
参数：n : Nat；s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Set.image_zero`：∀ {α : Type u_2} {β : Type u_3} [inst : Zero α] {f : α →
 β}, f '' 0 = {f 0}
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用引理 `Multiplicative.ofAdd_image_setAdd`：ofAdd_image_setAdd (s t : Set M) : of
Add '' (s + t) = ofAdd '' s * ofAdd '' t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofAdd_image_nsmul (n : ℕ) (s : Set M) :
    ofAdd '' (n • s) = (ofAdd '' s) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

@[simp]
/-
**Multiplicative.toAdd_image_setMul** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
形式化陈述：toAdd_image_setMul (s t : Set (Multiplicative M)) : toAdd '' (s * t) = (to
Add '' s) + (toAdd '' t)
参数：s t : Set (Multiplicative M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_mul`：image2_mul : image2 (· * ·) s t = s * t
· 使用定理 `Set.image_image2_distrib`：image_image2_distrib {g : γ -> δ} {f' : α' -> 
β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f' (
g₁ a) (g₂ b)) …
· 使用定理 `toAdd_mul`：toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = 
x.toAdd + y.toAdd
· 使用定理 `Set.image2_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, Set.image
2 (fun x1 x2 => x1 + x2) s t = s + t
-/
lemma toAdd_image_setMul (s t : Set (Multiplicative M)) :
    toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t) := by
  rw [← Set.image2_mul, Set.image_image2_distrib toAdd_mul, Set.image2_add]

@[simp]
/-
**Multiplicative.toAdd_image_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
形式化陈述：toAdd_image_nsmul (n : Nat) (s : Set (Multiplicative M)) : toAdd '' (s ^ n
) = n • (toAdd '' s)
参数：n : Nat；s : Set (Multiplicative M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Set.image_one`：image_one {f : α -> β} : f '' 1 = {f 1}
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `Multiplicative.toAdd_image_setMul`：toAdd_image_setMul (s t : Set (Multip
licative M)) : toAdd '' (s * t) = (toAdd '' s) + (toAdd '' t)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAdd_image_nsmul (n : ℕ) (s : Set (Multiplicative M)) :
    toAdd '' (s ^ n) = n • (toAdd '' s) := by
  induction n with
  | zero => simp; rfl
  | succ n IH => simp [succ_nsmul, pow_succ, IH]

end Multiplicative

