/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Regular.SMul

/-!
# Results about `IsRegular` and pi types
-/

public section

variable {ι α : Type*} {R : ι → Type*}

namespace Pi

section
variable [∀ i, Mul (R i)]

@[to_additive (attr := simp)]
/-
**Pi.isLeftRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isLeftRegular_iff {a : forall i, R i} : IsLeftRegular a ↔ forall i, IsLeft
Regular (a i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.map_injective`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → Sort u_3}
 [∀ (i : ι), Nonempty (α i)] {f : (i : ι) → α i → β i},   Function.Injective (Pi
.map f…
-/
theorem isLeftRegular_iff {a : ∀ i, R i} : IsLeftRegular a ↔ ∀ i, IsLeftRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; Pi.map_injective

@[to_additive (attr := simp)]
/-
**Pi.isRightRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isRightRegular_iff {a : forall i, R i} : IsRightRegular a ↔ forall i, IsRi
ghtRegular (a i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Pi.map_injective`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → Sort u_3}
 [∀ (i : ι), Nonempty (α i)] {f : (i : ι) → α i → β i},   Function.Injective (Pi
.map f…
-/
theorem isRightRegular_iff {a : ∀ i, R i} : IsRightRegular a ↔ ∀ i, IsRightRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm <| Pi.map_injective.symm

@[to_additive (attr := simp)]
/-
**Pi.isRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isRegular_iff {a : forall i, R i} : IsRegular a ↔ forall i, IsRegular (a i
)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isRegular_iff {a : ∀ i, R i} : IsRegular a ↔ ∀ i, IsRegular (a i) := by
  simp [_root_.isRegular_iff, forall_and]

end

@[simp]
/-
**Pi.isSMulRegular_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：isSMulRegular_iff [forall i, SMul α (R i)] {r : α} [forall i, Nonempty (R 
i)] : IsSMulRegular (forall i, R i) r ↔ forall i, IsSMulRegular (R i) r
参数：R i；R i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.map_injective`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {β : ι → Sort u_3}
 [∀ (i : ι), Nonempty (α i)] {f : (i : ι) → α i → β i},   Function.Injective (Pi
.map f…
-/
theorem isSMulRegular_iff [∀ i, SMul α (R i)] {r : α} [∀ i, Nonempty (R i)] :
    IsSMulRegular (∀ i, R i) r ↔ ∀ i, IsSMulRegular (R i) r :=
  Pi.map_injective

end Pi

