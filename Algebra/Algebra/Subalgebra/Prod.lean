/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Products of subalgebras

In this file we define the product of two subalgebras as a subalgebra of the product algebra.

## Main definitions

* `Subalgebra.prod`: the product of two subalgebras.
-/

@[expose] public section


namespace Subalgebra

open Algebra

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
         [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]

variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
/-
**Subalgebra.prod** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：prod : Subalgebra R (A × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two subalgebras is a subalgebra.
-/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }

@[simp, norm_cast]
/-
**Subalgebra.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl

open Subalgebra in
/-
**Subalgebra.prod_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmo
dule S₁)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁) := rfl

@[simp]
/-
**Subalgebra.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} : x in pro
d S S₁ ↔ x.1 in S ∧ x.2 in S₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod

@[simp]
/-
**Subalgebra.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp
/-
**Subalgebra.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S <= T -> S₁ <
= T₁ -> prod S S₁ <= prod T T₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono

@[simp]
/-
**Subalgebra.prod_inf_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} : S.prod S₁ 
⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod
/-
**Subalgebra.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] [inst_4 : Alge
bra R B],   Subalgebra.center R (A × B) = (Subalgebra.center R A).prod (Subalgeb
ra.center R B)
参数：A × B；Subalgebra.center R A；Subalgebra.center R B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center R (A × B) = prod (center R A) (center R B) :=
  SetLike.coe_injective Set.center_prod

@[simp]
/-
**Subalgebra._root_.AlgHom.range_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.range_prodMap (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

end Subalgebra

