/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Equiv

/-!
# If a semiring is a field, any isomorphic semiring is also a field.

This is in a separate file to avoid needing to import `Field` in `Mathlib/Algebra/Ring/Equiv.lean`
-/

public section

variable {A B F : Type*} [Semiring A] [Semiring B]

/-
**IsLocalHom.isField** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalHom`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} {F : Type u_3} [inst : Semiring A] [inst_1
 : Semiring B] [inst_2 : FunLike F A B]   [MonoidWithZeroHomClass F A B] {f : F}
 [IsLocalHom f], Function.Injective ⇑f → IsField B → IsField A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsField.exists_pair_ne`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∃ x y, x ≠ y
· 使用定理 `Nontrivial.exists_pair_ne`：∀ {α : Type u_3} [self : Nontrivial α], ∃ x y
, x ≠ y
· 使用定理 `domain_nontrivial`：domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' -> M₀
) (zero : f 0 = 0) (one : f 1 = 1) : Nontrivial M₀'
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsField.mul_comm`：∀ {R : Type u} [inst : Semiring R], IsField R → ∀ (x y
 : R), x * y = y * x
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `Ne.trans_eq`：∀ {α : Sort u_1} {a b c : α}, a ≠ b → b = c → a ≠ c
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `IsUnit.exists_right_inv`：IsUnit.exists_right_inv (h : IsUnit a) : exists
 b, a * b = 1
· 使用定理 `IsUnit.of_map`：IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit 
(f a)) : IsUnit a
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
protected theorem IsLocalHom.isField [FunLike F A B] [MonoidWithZeroHomClass F A B] {f : F}
    [IsLocalHom f] (inj : Function.Injective f) (hB : IsField B) : IsField A where
  exists_pair_ne := have : Nontrivial B := ⟨hB.1⟩; (domain_nontrivial f (map_zero f) (map_one f)).1
  mul_comm x y := inj <| by rw [map_mul, map_mul, hB.mul_comm]
  mul_inv_cancel h :=
    have ⟨a', he⟩ := hB.mul_inv_cancel ((inj.ne h).trans_eq <| map_zero f)
    let _ := hB.toSemifield
    (IsUnit.of_mul_eq_one _ he).of_map.exists_right_inv
/-
**MulEquiv.isField** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [inst_1 : Semiring B],
 IsField B → ∀ (e : A ≃* B), IsField A
参数：e : A ≃* B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHom.isField`：∀ {A : Type u_1} {B : Type u_2} {F : Type u_3} [inst
 : Semiring A] [inst_1 : Semiring B] [inst_2 : FunLike F A B]   [MonoidWithZeroH
omClass …
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
protected theorem MulEquiv.isField (hB : IsField B) (e : A ≃* B) : IsField A :=
  IsLocalHom.isField e.injective hB
/-
**MulEquiv.isField_congr** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [inst_1 : Semiring B] 
(e : A ≃* B), IsField A ↔ IsField B
参数：e : A ≃* B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
-/
protected theorem MulEquiv.isField_congr (e : A ≃* B) : IsField A ↔ IsField B :=
  ⟨e.symm.isField, e.isField⟩
