/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Endomorphisms of a module

In this file we define the type of linear endomorphisms of a module over a ring (`Module.End`).
We set up the basic theory,
including the action of `Module.End` on the module we are considering endomorphisms of.

## Main results

* `Module.End.instSemiring` and `Module.End.instRing`: the (semi)ring of endomorphisms formed by
  taking the additive structure above with composition as multiplication.
-/

@[expose] public section

universe u v

/-- Linear endomorphisms of a module, with associated ring structure
`Module.End.semiring` and algebra structure `Module.End.algebra`. -/
/-
**Module.End** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Modul
e R M]
参数：R : Type u；M : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear endomorphisms of a module, with associated ring structure
`Module.End.semiring` and algebra structure `Module.End.algebra`.
-/
abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

open Function LinearMap

/-!
## Monoid structure of endomorphisms
-/

namespace Module.End

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

/-
**Module.End.** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (Module.End R M) := ⟨LinearMap.id⟩
/-
**Module.End.** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (Module.End R M) := ⟨fun f g => LinearMap.comp f g⟩
/-
**Module.End.one_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：one_eq_id : (1 : Module.End R M) = .id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_id : (1 : Module.End R M) = .id := rfl
/-
**Module.End.mul_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mul_eq_comp (f g : Module.End R M) : f * g = f.comp g
参数：f g : Module.End R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq_comp (f g : Module.End R M) : f * g = f.comp g := rfl

@[simp]
/-
**Module.End.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：one_apply (x : M) : (1 : Module.End R M) x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : M) : (1 : Module.End R M) x = x := rfl

@[simp]
/-
**Module.End.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x)
参数：f g : Module.End R M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl
/-
**Module.End.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：coe_one : ⇑(1 : Module.End R M) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : Module.End R M) = _root_.id := rfl
/-
**Module.End.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g
参数：f g : Module.End R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g := rfl
/-
**Module.End.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instNontrivial [Nontrivial M] : Nontrivial (Module.End R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
instance instNontrivial [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)
/-
**Module.End.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instMonoid : Monoid (Module.End R M) where mul_assoc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (Module.End R M) where
  mul_assoc _ _ _ := LinearMap.ext fun _ ↦ rfl
  mul_one := comp_id
  one_mul := id_comp
/-
**Module.End.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instSemiring : Semiring (Module.End R M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring : Semiring (Module.End R M) where
  __ := AddMonoidWithOne.unary
  __ := instMonoid
  __ := addCommMonoid
  mul_zero := comp_zero
  zero_mul := zero_comp
  left_distrib := fun _ _ _ ↦ comp_add _ _ _
  right_distrib := fun _ _ _ ↦ add_comp _ _ _
  natCast := fun n ↦ n • (1 : M →ₗ[R] M)
  natCast_zero := zero_smul ℕ (1 : M →ₗ[R] M)
  natCast_succ := fun n ↦ AddMonoid.nsmul_succ n (1 : M →ₗ[R] M)

/-- See also `Module.End.natCast_def`. -/
@[simp]
/-
**Module.End.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：natCast_apply (n : Nat) (m : M) : (↑n : Module.End R M) m = n • m
参数：n : Nat；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Module.End.natCast_def`.
-/
theorem natCast_apply (n : ℕ) (m : M) : (↑n : Module.End R M) m = n • m := rfl

@[simp]
/-
**Module.End.ofNat_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：ofNat_apply (n : Nat) [n.AtLeastTwo] (m : M) : (ofNat(n) : Module.End R M)
 m = ofNat(n) • m
参数：n : Nat；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : Module.End R M) m = ofNat(n) • m := rfl
/-
**Module.End.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instRing : Ring (Module.End R N₁) where intCast z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing : Ring (Module.End R N₁) where
  intCast z := z • (1 : N₁ →ₗ[R] N₁)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

/-- See also `Module.End.intCast_def`. -/
@[simp]
/-
**Module.End.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：intCast_apply (z : Int) (m : N₁) : (z : Module.End R N₁) m = z • m
参数：z : Int；m : N₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See also `Module.End.intCast_def`.
-/
theorem intCast_apply (z : ℤ) (m : N₁) : (z : Module.End R N₁) m = z • m :=
  rfl

section

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

/-
**Module.End.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instIsScalarTower : IsScalarTower S (Module.End R M) (Module.End R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.smul_comp`：smul_comp (a : S₃) (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛ
ₗ[σ₁₂] M₂) : (a • g).comp f = a • g.comp f
-/
instance instIsScalarTower :
    IsScalarTower S (Module.End R M) (Module.End R M) :=
  ⟨smul_comp⟩
/-
**Module.End.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instSMulCommClass [SMul S R] [IsScalarTower S R M] : SMulCommClass S (Modu
le.End R M) (Module.End R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_smul`：comp_smul [Module R M₂] [Module R M₃] [SMulCommClas
s R S M₂] [DistribMulAction S M₃] [SMulCommClass R S M₃] [CompatibleSMul M₃ M₂ S
 R] (g : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance instSMulCommClass [SMul S R] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) (Module.End R M) :=
  ⟨fun s _ _ ↦ (comp_smul _ s _).symm⟩
/-
**Module.End.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：instSMulCommClass' [SMul S R] [IsScalarTower S R M] : SMulCommClass (Modul
e.End R M) S (Module.End R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass' [SMul S R] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S (Module.End R M) :=
  SMulCommClass.symm _ _ _
/-
**Module.End.isUnit_apply_inv_apply_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End`。
形式化陈述：isUnit_apply_inv_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) : f 
(h.unit.inv x) = x
参数：h : IsUnit f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isUnit_apply_inv_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) :
    f (h.unit.inv x) = x :=
  show (f * h.unit.inv) x = x by simp
/-
**Module.End.isUnit_inv_apply_apply_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End`。
形式化陈述：isUnit_inv_apply_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) : h.
unit.inv (f x) = x
参数：h : IsUnit f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isUnit_inv_apply_apply_of_isUnit {f : End R M} (h : IsUnit f) (x : M) :
    h.unit.inv (f x) = x :=
  (by simp : (h.unit.inv * f) x = x)
/-
**Module.End.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
参数：f : End R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hom_coe_pow`：∀ {M : Type u_4} {F : Type u_5} [inst : Monoid F] (c : F → 
M → M),   c 1 = id → (∀ (f g : F), c (f * g) = c f ∘ c g) → ∀ (f : F) (n : ℕ), c
 …
-/
theorem coe_pow (f : End R M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
/-
**Module.End.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n) m = f^[n] m
参数：f : End R M；n : Nat；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Module.End.coe_pow`：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
-/
theorem pow_apply (f : End R M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m
/-
**Module.End.pow_map_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：pow_map_zero_of_le {f : End R M} {m : M} {k l : Nat} (hk : k <= l) (hm : (
f ^ k) m = 0) : (f ^ l) m = 0
参数：hk : k <= l；hm : (f ^ k) m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem pow_map_zero_of_le {f : End R M} {m : M} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← Nat.sub_add_cancel hk, pow_add, mul_apply, hm, map_zero]
/-
**Module.End.commute_pow_left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：commute_pow_left_of_commute [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂
] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R
₂ M₂} (h : g₂.comp f = f.comp g) (k : Nat) : (g₂ ^ k).comp f = f.comp (g ^ k)
参数：h : g₂.comp f = f.comp g；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem commute_pow_left_of_commute
    [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction k with
  | zero => simp [one_eq_id]
  | succ k ih => rw [pow_succ', pow_succ', mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, mul_eq_comp]

@[simp]
/-
**Module.End.id_pow** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：id_pow (n : Nat) : (id : End R M) ^ n = .id
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem id_pow (n : ℕ) : (id : End R M) ^ n = .id :=
  one_pow n

variable {f' : End R M}
/-
**Module.End.iterate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (f' ^ n) f'
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
-/
theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = .comp (f' ^ n) f' := by rw [pow_succ, mul_eq_comp]
/-
**Module.End.iterate_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：iterate_succ' (n : Nat) : f' ^ (n + 1) = .comp f' (f' ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
-/
theorem iterate_succ' (n : ℕ) : f' ^ (n + 1) = .comp f' (f' ^ n) := by rw [pow_succ', mul_eq_comp]
/-
**Module.End.iterate_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {f' : Module.End R M}, Function.Surjective ⇑
f' → ∀ (n : ℕ), Function.Surjective ⇑(f' ^ n)
参数：n : ℕ；f' ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h
/-
**Module.End.iterate_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {f' : Module.End R M}, Function.Injective ⇑f
' → ∀ (n : ℕ), Function.Injective ⇑(f' ^ n)
参数：n : ℕ；f' ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h
/-
**Module.End.iterate_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {f' : Module.End R M}, Function.Bijective ⇑f
' → ∀ (n : ℕ), Function.Bijective ⇑(f' ^ n)
参数：n : ℕ；f' ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h
/-
**Module.End.injective_of_iterate_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d`。
形式化陈述：injective_of_iterate_injective {n : Nat} (hn : n != 0) (h : Injective (f' 
^ n)) : Injective f'
参数：hn : n != 0；h : Injective (f' ^ n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Module.End.iterate_succ`：iterate_succ (n : Nat) : f' ^ (n + 1) = .comp (
f' ^ n) f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (show 0 < n by lia), iterate_succ, coe_comp] at h
  exact h.of_comp
/-
**Module.End.surjective_of_iterate_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End`。
形式化陈述：surjective_of_iterate_surjective {n : Nat} (hn : n != 0) (h : Surjective (
f' ^ n)) : Surjective f'
参数：hn : n != 0；h : Surjective (f' ^ n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.coe_mul`：coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
-/
theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hn), pow_succ', coe_mul] at h
  exact Surjective.of_comp h

/-- Scalar multiplication on the left, as a linear map. -/
/-
**Module.End.smulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：{R : Type u_1} →   {M : Type u_4} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → (α : R) → α ∈ Set.center R
 → Module.End R M
参数：α : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication on the left, as a linear map.
-/
@[simps] def smulLeft (α : R) (hα : α ∈ Set.center R) : End R M where
  toFun x := α • x
  map_add' := smul_add _
  map_smul' β _ := by simp [smul_smul, ((Set.mem_center_iff.mp hα).comm β).eq]
/-
**Module.End.smulLeft_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {M : Type u_4} [inst : AddCommMonoid M] {R : Type u_9} [inst_1 : CommSem
iring R] [inst_2 : _root_.Module R M] (α : R)   (hα : autoParam (α ∈ Set.center 
R) Module.End.smulLeft_eq._auto_1), Module.End.smulLeft α hα = α • LinearMap.id
参数：α : R；hα : autoParam (α ∈ Set.center R) Module.End.smulLeft_eq._auto_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smulLeft_eq {R : Type*} [CommSemiring R] [Module R M] (α : R)
    (hα : α ∈ Set.center R := by simp) : smulLeft α hα = α • .id (M := M) := rfl

end

/-! ## Action by a module endomorphism. -/


/-- The tautological action by `Module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `Function.End.applyMulAction`. -/
/-
**Module.End.applyModule** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：applyModule : Module (Module.End R M) M where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by `Module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `Function.End.applyMulAction`.
-/
instance applyModule : Module (Module.End R M) M where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**Module.End.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) (a : M), f • a = f a
参数：f : Module.End R M；a : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem smul_def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl

/-- `LinearMap.applyModule` is faithful. -/
/-
**Module.End.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (Module.End R M) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
`LinearMap.applyModule` is faithful.
-/
instance apply_faithfulSMul : FaithfulSMul (Module.End R M) M :=
  ⟨LinearMap.ext⟩
/-
**Module.End.apply_smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] : SMulComm
Class S (Module.End R M) M where smul_comm r e m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
instance apply_smulCommClass [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) M where
  smul_comm r e m := (e.map_smul_of_tower r m).symm
/-
**Module.End.apply_smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] : SMulCom
mClass (Module.End R M) S M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance apply_smulCommClass' [SMul S R] [SMul S M] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S M :=
  SMulCommClass.symm _ _ _
/-
**Module.End.apply_isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
形式化陈述：apply_isScalarTower [Monoid S] [DistribMulAction S M] [SMulCommClass R S M
] : IsScalarTower S (Module.End R M) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance apply_isScalarTower [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] :
    IsScalarTower S (Module.End R M) M :=
  ⟨fun _ _ _ ↦ rfl⟩

end Module.End

section

/-! ## Actions as module endomorphisms -/

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Monoid S]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `DistribSMul.toAddMonoidHom`. -/
@[simps]
/-
**DistribSMul.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribSMul.toLinearMap [DistribSMul S M] [SMulCommClass S R M] (s : S) : 
M ->ₗ[R] M where toFun
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines a linear map.

This is a stronger version of `DistribSMul.toAddMonoidHom`.
-/
def DistribSMul.toLinearMap [DistribSMul S M] [SMulCommClass S R M] (s : S) : M →ₗ[R] M where
  toFun := HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`. -/
@[simps]
/-
**DistribMulAction.toModuleEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DistribMulAction.toModuleEnd [DistribMulAction S M] [SMulCommClass S R M] 
: S ->* Module.End R M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines a module endomorphism.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`.
-/
def DistribMulAction.toModuleEnd [DistribMulAction S M] [SMulCommClass S R M] :
    S →* Module.End R M where
  toFun := DistribSMul.toLinearMap R M
  map_one' := LinearMap.ext <| one_smul _
  map_mul' _ _ := LinearMap.ext <| mul_smul _ _

@[deprecated (since := "2026-01-07")] alias DistribMulAction.toLinearMap := DistribSMul.toLinearMap

end

section Module

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring S] [Module S M] [SMulCommClass S R M]

/-- Each element of the semiring defines a module endomorphism.

This is a stronger version of `DistribMulAction.toModuleEnd`. -/
@[simps]
/-
**Module.toModuleEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.toModuleEnd : S ->+* Module.End R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the semiring defines a module endomorphism.

This is a stronger version of `DistribMulAction.toModuleEnd`.
-/
def Module.toModuleEnd : S →+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with
    toFun := DistribSMul.toLinearMap R M
    map_zero' := LinearMap.ext <| zero_smul S
    map_add' := fun _ _ ↦ LinearMap.ext <| add_smul _ _ }

/-- The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `Module.End R R` induced by the right
multiplication. -/
@[simps]
/-
**RingEquiv.moduleEndSelf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `Module.End R R` induced by 
the right
multiplication.
-/
def RingEquiv.moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with
    toFun := DistribSMul.toLinearMap R R
    invFun := fun f ↦ MulOpposite.op (f 1)
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring <| one_mul _ }

/-- The canonical (semi)ring isomorphism from `R` to `Module.End Rᵐᵒᵖ R` induced by the left
multiplication. -/
@[simps]
/-
**RingEquiv.moduleEndSelfOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical (semi)ring isomorphism from `R` to `Module.End Rᵐᵒᵖ R` induced by 
the left
multiplication.
-/
def RingEquiv.moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with
    toFun := DistribSMul.toLinearMap _ _
    invFun := fun f ↦ f 1
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring_op <| mul_one _ }
/-
**Module.End.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.natCast_def (n : Nat) [AddCommMonoid N₁] [Module R N₁] : (↑n : 
Module.End R N₁) = Module.toModuleEnd R N₁ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Module.End.natCast_def (n : ℕ) [AddCommMonoid N₁] [Module R N₁] :
    (↑n : Module.End R N₁) = Module.toModuleEnd R N₁ n :=
  rfl
/-
**Module.End.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.intCast_def (z : Int) [AddCommGroup N₁] [Module R N₁] : (z : Mo
dule.End R N₁) = Module.toModuleEnd R N₁ z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Module.End.intCast_def (z : ℤ) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z :=
  rfl

end Module

namespace LinearMap

section AddCommMonoid

section SMulRight

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]
variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun b ↦ f b • x` is an `R`-linear
map. -/
/-
**LinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：smulRight (f : M₁ ->ₗ[R] S) (x : M) : M₁ ->ₗ[R] M where toFun b
参数：f : M₁ ->ₗ[R] S；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f` is an `R`-linear map taking values in `S`, then `fun b ↦ f b • x` is an
 `R`-linear
map.
-/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by rw [f.map_add, add_smul]
  map_smul' b y := by rw [RingHom.id_apply, map_smul, smul_assoc]

@[simp]
/-
**LinearMap.coe_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_smulRight (f : M₁ ->ₗ[R] S) (x : M) : (smulRight f x : M₁ -> M) = fun 
c => f c • x
参数：f : M₁ ->ₗ[R] S；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smulRight (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl
/-
**LinearMap.smulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smulRight_apply (f : M₁ ->ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c
 • x
参数：f : M₁ ->ₗ[R] S；x : M；c : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRight_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl

@[simp]
/-
**LinearMap.smulRight_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：smulRight_zero (f : M₁ ->ₗ[R] S) : f.smulRight (0 : M) = 0
参数：f : M₁ ->ₗ[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smulRight_zero (f : M₁ →ₗ[R] S) : f.smulRight (0 : M) = 0 := by ext; simp

@[simp]
/-
**LinearMap.zero_smulRight** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：zero_smulRight (x : M) : (0 : M₁ ->ₗ[R] S).smulRight x = 0
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_smulRight (x : M) : (0 : M₁ →ₗ[R] S).smulRight x = 0 := by ext; simp

@[simp]
/-
**LinearMap.smulRight_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：smulRight_apply_eq_zero_iff [IsDomain S] {f : M₁ ->ₗ[R] S} {x : M} [Module
.IsTorsionFree S M] : f.smulRight x = 0 ↔ f = 0 ∨ x = 0
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
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smulRight_apply_eq_zero_iff [IsDomain S] {f : M₁ →ₗ[R] S} {x : M} [Module.IsTorsionFree S M] :
    f.smulRight x = 0 ↔ f = 0 ∨ x = 0 := by simp [DFunLike.ext_iff, forall_or_right]

end SMulRight

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module R M₁] [Module R M₂] [Module S M₁] [Module S M₂]
variable [SMulCommClass R S M₁] [SMulCommClass R S M₂]
variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
/-
**LinearMap.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M
₂`.

See `LinearMap.applyₗ` for a version where `S = R`.
-/
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _

variable [CompatibleSMul M₁ M₂ S R]

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M → M₃`. -/
/-
**LinearMap.compRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compRight (f : M₁ ->ₗ[R] M₂) : (M ->ₗ[R] M₁) ->ₗ[S] M ->ₗ[R] M₂ where toFu
n g
参数：f : M₁ ->ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → 
M₂`
to the space of linear maps `M → M₃`.
-/
def compRight (f : M₁ →ₗ[R] M₂) : (M →ₗ[R] M₁) →ₗ[S] M →ₗ[R] M₂ where
  toFun g := f.comp g
  map_add' _ _ := LinearMap.ext fun _ ↦ map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ ↦ map_smul_of_tower ..

@[simp]
/-
**LinearMap.compRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：compRight_apply (f : M₁ ->ₗ[R] M₂) (g : M ->ₗ[R] M₁) : compRight S f g = f
.comp g
参数：f : M₁ ->ₗ[R] M₂；g : M ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRight_apply (f : M₁ →ₗ[R] M₂) (g : M →ₗ[R] M₁) : compRight S f g = f.comp g :=
  rfl

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f : M →ₗ[R] M₂)

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
/-
**LinearMap.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`
.
See also `LinearMap.applyₗ'` for a version that works with two different semirin
gs.

This is the `LinearMap` version of `toAddMonoidHom.eval`.
-/
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.

This is also known as a rank-one operator.
See `ContinuousLinearMap.smulRightL` for the continuous version of this, and see
`InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces. -/
/-
**LinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：smulRight (f : M₁ ->ₗ[R] S) (x : M) : M₁ ->ₗ[R] M where toFun b
参数：f : M₁ ->ₗ[R] S；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is li
near in `f`, `x`.

This is also known as a rank-one operator.
See `ContinuousLinearMap.smulRightL` for the continuous version of this, and see
`InnerProductSpace.rankOne` for the rank-one operator on Hilbert spaces.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul

@[simp]
/-
**LinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：smulRight (f : M₁ ->ₗ[R] S) (x : M) : M₁ ->ₗ[R] M where toFun b
参数：f : M₁ ->ₗ[R] S；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x = smulRight f x :=
  rfl
/-
**LinearMap.smulRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：smulRight (f : M₁ ->ₗ[R] S) (x : M) : M₁ ->ₗ[R] M where toFun b
参数：f : M₁ ->ₗ[R] S；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smulRightₗ_apply_apply (f : M₂ →ₗ[R] R) (x : M) (y : M₂) :
    smulRightₗ f x y = f y • x := rfl

end CommSemiring

end LinearMap

namespace Module.End

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : Module.End R M)

/-
**Module.End.commute_id_left** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：commute_id_left : Commute LinearMap.id f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commute_id_left : Commute LinearMap.id f := by ext; simp
/-
**Module.End.commute_id_right** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：commute_id_right : Commute f LinearMap.id
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commute_id_right : Commute f LinearMap.id := by ext; simp

end Module.End

