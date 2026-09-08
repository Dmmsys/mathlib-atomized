/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.Algebra.Group.Center

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

public section

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

/-
**Set.star_mem_center** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.star_mem_center (ha : a in Set.center R) : star a in Set.center R wher
e comm
参数：ha : a in Set.center R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_center_iff`：mem_center_iff {z : M} : z in center M ↔ IsMulCentra
l z
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
-/
theorem Set.star_mem_center (ha : a ∈ Set.center R) : star a ∈ Set.center R where
  comm := by simpa only [star_mul, star_star] using! fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.right_assoc (star c) (star b))
  right_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.left_assoc (star c) (star b))
/-
**Set.star_centralizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.star_centralizer : star s.centralizer = (star s).centralizer
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Set.star_centralizer : star s.centralizer = (star s).centralizer := by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_ofPred_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]
/-
**Set.union_star_self_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.union_star_self_comm (hcomm : forall x in s, forall y in s, y * x = x 
* y) (hcomm_star : forall x in s, forall y in s, y * star x = star x * y) : fora
ll x in s union star s, forall y in s union star s, y * x = x * y
参数：hcomm : forall x in s, forall y in s, y * x = x * y；hcomm_star : forall x in 
s, forall y in s, y * star x = star x * y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.centralizer_union`：centralizer_union : centralizer (S union T) = cen
tralizer S inter centralizer T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Set.union_star_self_comm (hcomm : ∀ x ∈ s, ∀ y ∈ s, y * x = x * y)
    (hcomm_star : ∀ x ∈ s, ∀ y ∈ s, y * star x = star x * y) :
    ∀ x ∈ s ∪ star s, ∀ y ∈ s ∪ star s, y * x = x * y := by
  change s ∪ star s ⊆ (s ∪ star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩
/-
**Set.star_mem_centralizer'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.star_mem_centralizer' (h : forall a : R, a in s -> star a in s) (ha : 
a in Set.centralizer s) : star a in Set.centralizer s
参数：h : forall a : R, a in s -> star a in s；ha : a in Set.centralizer s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Set.star_mem_centralizer' (h : ∀ a : R, a ∈ s → star a ∈ s) (ha : a ∈ Set.centralizer s) :
    star a ∈ Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise
/-
**Set.star_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.star_mem_centralizer (ha : a in Set.centralizer (s union star s)) : st
ar a in Set.centralizer (s union star s)
参数：ha : a in Set.centralizer (s union star s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.star_mem_centralizer'`：Set.star_mem_centralizer' (h : forall a : R, 
a in s -> star a in s) (ha : a in Set.centralizer s) : star a in Set.centralizer
 s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.star_mem_star`：star_mem_star [InvolutiveStar α] : a⋆ in s⋆ ↔ a in s
-/
theorem Set.star_mem_centralizer (ha : a ∈ Set.centralizer (s ∪ star s)) :
    star a ∈ Set.centralizer (s ∪ star s) :=
  Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha
