/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Attr.Register

/-!
# Monoids of endomorphisms, groups of automorphisms

This file defines
* the endomorphism monoid structure on `Function.End α := α → α`
* the endomorphism monoid structure on `Monoid.End M := M →* M` and `AddMonoid.End M := M →+ M`
* the automorphism group structure on `Equiv.Perm α := α ≃ α`
* the automorphism group structure on `MulAut M := M ≃* M` and `AddAut M := M ≃+ M`.

## Implementation notes

The definition of multiplication in the endomorphism monoids and automorphism groups agrees with
function composition, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

end monoid, aut group
-/

@[expose] public section

assert_not_exists HeytingAlgebra MonoidWithZero MulAction RelIso

variable {A M G α β γ : Type*}

/-! ### Type endomorphisms -/

variable (α) in
/-- The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`. -/
/-
**Function.End** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：Type u_4 → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `
Type u`.
-/
protected def Function.End := α → α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Function.End α) := ⟨1⟩

/-! ### Monoid endomorphisms -/

namespace Equiv.Perm

attribute [to_additive_dont_translate] Perm Equiv

/-
**Equiv.Perm.instOne** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：instOne : One (Perm α) where one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
instance instOne : One (Perm α) where one := Equiv.refl _
/-
**Equiv.Perm.instMul** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：instMul : Mul (Perm α) where mul f g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
instance instMul : Mul (Perm α) where mul f g := Equiv.trans g f
/-
**Equiv.Perm.instInv** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：instInv : Inv (Perm α) where inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instInv : Inv (Perm α) where inv := Equiv.symm
/-
**Equiv.Perm.instPowNat** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：instPowNat : Pow (Perm α) Nat where pow f n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance instPowNat : Pow (Perm α) ℕ where
  pow f n := ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩
/-
**Equiv.Perm.permGroup** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
形式化陈述：permGroup : Group (Perm α) where mul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
· 使用定理 `Equiv.refl_trans`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), (Equiv.refl α
).trans e = e
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
-/
instance permGroup : Group (Perm α) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
  npow_succ _ _ := coe_fn_injective <| Function.iterate_succ _ _
  zpow := zpowRec fun n f ↦ f ^ n
  zpow_succ' _ _ := coe_fn_injective <| Function.iterate_succ _ _

@[simp]
/-
**Equiv.Perm.default_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：default_eq : (default : Perm α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_eq : (default : Perm α) = 1 :=
  rfl

/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps]
/-
**Equiv.Perm.equivUnitsEnd** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：equivUnitsEnd : Perm α ≃* Units (Function.End α) where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id

--- 原说明 ---
The permutation of a type is equivalent to the units group of the endomorphisms 
monoid of this
type.
-/
def equivUnitsEnd : Perm α ≃* Units (Function.End α) where
  toFun e := ⟨⇑e, ⇑e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  map_mul' _ _ := rfl

/-- Lift a monoid homomorphism `f : G →* Function.End α` to a monoid homomorphism
`f : G →* Equiv.Perm α`. -/
@[simps!]
/-
**Equiv.Perm._root_.MonoidHom.toHomPerm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a monoid homomorphism `f : G →* Function.End α` to a monoid homomorphism
`f : G →* Equiv.Perm α`.
-/
def _root_.MonoidHom.toHomPerm {G : Type*} [Group G] (f : G →* Function.End α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits
/-
**Equiv.Perm.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
参数：f g : Perm α；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  rfl
/-
**Equiv.Perm.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：one_apply (x) : (1 : Perm α) x = x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl

@[pull_end, push_end← ]
/-
**Equiv.Perm.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：one_def : (1 : Perm α) = Equiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl

@[pull_end, push_end← ]
/-
**Equiv.Perm.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mul_def (f g : Perm α) : f * g = g.trans f
参数：f g : Perm α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl

@[pull_end, push_end← ]
/-
**Equiv.Perm.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：inv_def (f : Perm α) : f⁻¹ = f.symm
参数：f : Perm α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl
/-
**Equiv.Perm.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_4} (f : Equiv.Perm α), ⇑f⁻¹ = ⇑(Equiv.symm f)
参数：f : Equiv.Perm α；Equiv.symm f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_inv (f : Perm α) : ⇑f⁻¹ = ⇑f.symm := rfl
/-
**Equiv.Perm.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_4}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : Perm α) = id := rfl
/-
**Equiv.Perm.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_4} (f g : Equiv.Perm α), ⇑(f * g) = ⇑f ∘ ⇑g
参数：f g : Equiv.Perm α；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g := rfl
/-
**Equiv.Perm.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：∀ {α : Type u_4} (f : Equiv.Perm α) (n : ℕ), ⇑(f ^ n) = (⇑f)^[n]
参数：f : Equiv.Perm α；n : ℕ；f ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_pow (f : Perm α) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[pull_end← , push_end]
/-
**Equiv.Perm.iterate_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：iterate_eq_pow (f : Perm α) (n : Nat) : f^[n] = ⇑(f ^ n)
参数：f : Perm α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iterate_eq_pow (f : Perm α) (n : ℕ) : f^[n] = ⇑(f ^ n) := rfl
/-
**Equiv.Perm.eq_inv_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply
/-
**Equiv.Perm.inv_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq
/-
**Equiv.Perm.zpow_apply_comm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：zpow_apply_comm {α : Type*} (σ : Perm α) (m n : Int) {x : α} : (σ ^ m) ((σ
 ^ n) x) = (σ ^ n) ((σ ^ m) x)
参数：σ : Perm α；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `zpow_mul_comm`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ 
m * a ^ n = a ^ n * a ^ m
-/
theorem zpow_apply_comm {α : Type*} (σ : Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]

/-! Lemmas about mixing `Perm` with `Equiv`. Because we have multiple ways to express
`Equiv.refl`, `Equiv.symm`, and `Equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.trans_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Perm β) = e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e

--- 原说明 ---
Lemmas about mixing `Perm` with `Equiv`. Because we have multiple ways to expres
s
`Equiv.refl`, `Equiv.symm`, and `Equiv.trans`, we want simp lemmas for every com
bination.
The assumption made here is that if you're using the group structure, you want t
o preserve it after
simp.
-/
theorem trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.mul_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mul_refl (e : Perm α) : e * Equiv.refl α = e
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
-/
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.one_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：one_symm : (1 : Perm α).symm = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem one_symm : (1 : Perm α).symm = 1 :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.refl_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.one_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Perm α).trans e = e
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.refl_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：refl_mul (e : Perm α) : Equiv.refl α * e = e
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  rfl

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.inv_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：inv_trans_self (e : Perm α) : e⁻¹.trans e = 1
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
-/
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.mul_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mul_symm (e : Perm α) : e * e.symm = 1
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_trans_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.t
rans e = Equiv.refl β
-/
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.self_trans_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
-/
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  Equiv.self_trans_symm e

@[deprecated "use `pull_end` simpset instead" (since := "2026-05-13")]
/-
**Equiv.Perm.symm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：symm_mul (e : Perm α) : e.symm * e = 1
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.self_trans_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans 
e.symm = Equiv.refl α
-/
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e

/-! Lemmas about `Equiv.Perm.sumCongr` re-expressed via the group structure. -/


@[simp]
/-
**Equiv.Perm.sumCongr_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_mul {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Per
m β) : sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h)
参数：e : Perm α；f : Perm β；g : Perm α；h : Perm β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sumCongr_trans`：sumCongr_trans {α β} (e : Equiv.Perm α) (f : 
Equiv.Perm β) (g : Equiv.Perm α) (h : Equiv.Perm β) : (sumCongr e f).trans (sumC
ongr g h) = sum…

--- 原说明 ---
Lemmas about `Equiv.Perm.sumCongr` re-expressed via the group structure.
-/
theorem sumCongr_mul {α β : Type*} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sumCongr_trans g h e f

@[simp]
/-
**Equiv.Perm.sumCongr_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_inv {α β : Type*} (e : Perm α) (f : Perm β) : (sumCongr e f)⁻¹ = 
sumCongr e⁻¹ f⁻¹
参数：e : Perm α；f : Perm β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumCongr_inv {α β : Type*} (e : Perm α) (f : Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  rfl

@[simp]
/-
**Equiv.Perm.sumCongr_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_one {α β : Type*} : sumCongr (1 : Perm α) (1 : Perm β) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sumCongr_refl`：sumCongr_refl {α β} : sumCongr (Equiv.refl α) 
(Equiv.refl β) = Equiv.refl (α oplus β)
-/
theorem sumCongr_one {α β : Type*} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sumCongr_refl

/-- `Equiv.Perm.sumCongr` as a `MonoidHom`, with its two arguments bundled into a single `Prod`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
/-
**Equiv.Perm.sumCongrHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongrHom (α β : Type*) : Perm α × Perm β ->* Perm (α oplus β) where toF
un a
参数：α β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sumCongr_one`：sumCongr_one {α β : Type*} : sumCongr (1 : Perm
 α) (1 : Perm β) = 1

--- 原说明 ---
`Equiv.Perm.sumCongr` as a `MonoidHom`, with its two arguments bundled into a si
ngle `Prod`.

This is particularly useful for its `MonoidHom.range` projection, which is the s
ubgroup of
permutations which do not exchange elements between `α` and `β`.
-/
def sumCongrHom (α β : Type*) : Perm α × Perm β →* Perm (α ⊕ β) where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' _ _ := (sumCongr_mul _ _ _ _).symm
/-
**Equiv.Perm.sumCongrHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongrHom_injective {α β : Type*} : Function.Injective (sumCongrHom α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sumCongrHom_apply`：∀ (α : Type u_7) (β : Type u_8) (a : Equiv
.Perm α × Equiv.Perm β), (Equiv.Perm.sumCongrHom α β) a = a.1.sumCongr a.2
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
-/
theorem sumCongrHom_injective {α β : Type*} : Function.Injective (sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

@[simp]
/-
**Equiv.Perm.sumCongr_swap_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) 
: sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j)
参数：i j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sumCongr_swap_refl`：sumCongr_swap_refl {α β : Sort _} [Decida
bleEq α] [DecidableEq β] (i j : α) : Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv
.refl β) = Equiv.sw…
-/
theorem sumCongr_swap_one {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sumCongr_swap_refl i j

@[simp]
/-
**Equiv.Perm.sumCongr_one_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) 
: sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j)
参数：i j : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sumCongr_refl_swap`：sumCongr_refl_swap {α β : Sort _} [Decida
bleEq α] [DecidableEq β] (i j : β) : Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.s
wap i j) = Equiv.sw…
-/
theorem sumCongr_one_swap {α β : Type*} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sumCongr_refl_swap i j

/-! Lemmas about `Equiv.Perm.sigmaCongrRight` re-expressed via the group structure. -/


@[simp]
/-
**Equiv.Perm.sigmaCongrRight_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sigmaCongrRight_mul {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a)
) (G : forall a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCong
rRight (F * G)
参数：F : forall a, Perm (β a)；G : forall a, Perm (β a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lemmas about `Equiv.Perm.sigmaCongrRight` re-expressed via the group structure.
-/
theorem sigmaCongrRight_mul {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a))
    (G : ∀ a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  rfl

@[simp]
/-
**Equiv.Perm.sigmaCongrRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sigmaCongrRight_inv {α : Type*} {β : α -> Type*} (F : forall a, Perm (β a)
) : (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹
参数：F : forall a, Perm (β a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaCongrRight_inv {α : Type*} {β : α → Type*} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  rfl

@[simp]
/-
**Equiv.Perm.sigmaCongrRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sigmaCongrRight_one {α : Type*} {β : α -> Type*} : sigmaCongrRight (1 : fo
rall a, Equiv.Perm <| β a) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaCongrRight_one {α : Type*} {β : α → Type*} :
    sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 :=
  rfl

/-- `Equiv.Perm.sigmaCongrRight` as a `MonoidHom`.

This is particularly useful for its `MonoidHom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
/-
**Equiv.Perm.sigmaCongrRightHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：sigmaCongrRightHom {α : Type*} (β : α -> Type*) : (forall a, Perm (β a)) -
>* Perm (Σ a, β a) where toFun
参数：β : α -> Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.sigmaCongrRight_one`：sigmaCongrRight_one {α : Type*} {β : α -
> Type*} : sigmaCongrRight (1 : forall a, Equiv.Perm <| β a) = 1

--- 原说明 ---
`Equiv.Perm.sigmaCongrRight` as a `MonoidHom`.

This is particularly useful for its `MonoidHom.range` projection, which is the s
ubgroup of
permutations which do not exchange elements between fibers.
-/
def sigmaCongrRightHom {α : Type*} (β : α → Type*) : (∀ a, Perm (β a)) →* Perm (Σ a, β a) where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' _ _ := (sigmaCongrRight_mul _ _).symm
/-
**Equiv.Perm.sigmaCongrRightHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：sigmaCongrRightHom_injective {α : Type*} {β : α -> Type*} : Function.Injec
tive (sigmaCongrRightHom β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.sigmaCongrRightHom_apply`：∀ {α : Type u_7} (β : α → Type u_8)
 (F : (a : α) → Equiv.Perm (β a)),   (Equiv.Perm.sigmaCongrRightHom β) F = Equiv
.Perm.sigmaCongrRight F
· 使用定理 `Equiv.sigmaCongrRight_apply`：∀ {α : Type u_3} {β₁ : α → Type u_1} {β₂ : 
α → Type u_2} (F : (a : α) → β₁ a ≃ β₂ a) (a : (a : α) × β₁ a),   (Equiv.sigmaCo
ngrRight F) a = ⟨…
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
-/
theorem sigmaCongrRightHom_injective {α : Type*} {β : α → Type*} :
    Function.Injective (sigmaCongrRightHom β) := by
  intro x y h
  ext a b
  simpa using Equiv.congr_fun h ⟨a, b⟩

/-- `Equiv.Perm.subtypeCongr` as a `MonoidHom`. -/
@[simps]
/-
**Equiv.Perm.subtypeCongrHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypeCongrHom (p : α -> Prop) [DecidablePred p] : Perm { a // p a } × Pe
rm { a // ¬p a } ->* Perm α where toFun pair
参数：p : α -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.subtypeCongr.refl`：∀ {ε : Type u_9} {p : ε → Prop} [inst : De
cidablePred p],   Equiv.Perm.subtypeCongr (Equiv.refl { a // p a }) (Equiv.refl 
{ a // ¬p a }) = E…

--- 原说明 ---
`Equiv.Perm.subtypeCongr` as a `MonoidHom`.
-/
def subtypeCongrHom (p : α → Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } →* Perm α where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm
/-
**Equiv.Perm.subtypeCongrHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypeCongrHom_injective (p : α -> Prop) [DecidablePred p] : Function.Inj
ective (subtypeCongrHom p)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.subtypeCongrHom_apply`：∀ {α : Type u_4} (p : α → Prop) [inst 
: DecidablePred p] (pair : Equiv.Perm { a // p a } × Equiv.Perm { a // ¬p a }), 
  (Equiv.Perm.subtypeC…
· 使用定理 `Equiv.Perm.subtypeCongr.left_apply_subtype`：∀ {ε : Type u_9} {p : ε → Pr
op} [inst : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { a
 // ¬p a })   (a : { a // p a })…
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
· 使用定理 `Equiv.Perm.subtypeCongr.right_apply_subtype`：∀ {ε : Type u_9} {p : ε → P
rop} [inst : DecidablePred p] (ep : Equiv.Perm { a // p a }) (en : Equiv.Perm { 
a // ¬p a })   (a : { a // ¬p a }…
-/
theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (subtypeCongrHom p) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i

/-- If `e` is also a permutation, we can write `permCongr`
completely in terms of the group structure. -/
@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongr_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e` is also a permutation, we can write `permCongr`
completely in terms of the group structure.
-/
theorem _root_.Equiv.permCongr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  rfl

@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongr_mul** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.permCongr_mul (e : α ≃ β) (p q : Perm α) :
    e.permCongr (p * q) = e.permCongr p * e.permCongr q :=
  permCongr_trans e q p |>.symm
/-
**Equiv.Perm._root_.Equiv.permCongrHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Equiv.permCongrHom (e : α ≃ β) : Perm α ≃* Perm β where
  toEquiv := e.permCongr
  map_mul' p q := e.permCongr_mul p q

attribute [inherit_doc Equiv.permCongr] Equiv.permCongrHom
extend_docs Equiv.permCongrHom after "This is `Equiv.permCongr` as a `MulEquiv`."

@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongrHom_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.permCongrHom_symm (e : α ≃ β) :
    e.permCongrHom.symm = e.symm.permCongrHom :=
  rfl

@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongrHom_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Equiv.permCongrHom_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.permCongrHom.trans e'.permCongrHom = (e.trans e').permCongrHom :=
  rfl

@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongrHom_coe_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Equi
v.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.permCongrHom_coe_equiv (e : α ≃ β) :
    (↑e.permCongrHom : Perm α ≃ Perm β) = e.permCongr :=
  rfl

@[simp]
/-
**Equiv.Perm._root_.Equiv.permCongrHom_coe** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Equiv.permCongrHom_coe (e : α ≃ β) : ⇑e.permCongrHom = ⇑e.permCongr :=
  rfl

section ExtendDomain

/-! Lemmas about `Equiv.Perm.extendDomain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

@[simp]
/-
**Equiv.Perm.extendDomain_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_one : extendDomain 1 f = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_refl`：∀ {α' : Type u_9} {β' : Type u_10} {p : β'
 → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p),   Equiv.Perm.extendDomai
n (Equiv.refl α') …
-/
theorem extendDomain_one : extendDomain 1 f = 1 :=
  extendDomain_refl f

@[simp]
/-
**Equiv.Perm.extendDomain_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl

@[simp]
/-
**Equiv.Perm.extendDomain_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_mul (e e' : Perm α) : e.extendDomain f * e'.extendDomain f = 
(e * e').extendDomain f
参数：e e' : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_trans`：∀ {α' : Type u_9} {β' : Type u_10} {p : β
' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p) (e e' : Equiv.Perm α'), 
  Equiv.trans (e.ex…
-/
theorem extendDomain_mul (e e' : Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extendDomain_trans _ _ _

/-- `extendDomain` as a group homomorphism -/
@[simps]
/-
**Equiv.Perm.extendDomainHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomainHom : Perm α ->* Perm β where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_one`：extendDomain_one : extendDomain 1 f = 1

--- 原说明 ---
`extendDomain` as a group homomorphism
-/
def extendDomainHom : Perm α →* Perm β where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm
/-
**Equiv.Perm.extendDomainHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomainHom_injective : Function.Injective (extendDomainHom f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
-/
theorem extendDomainHom_injective : Function.Injective (extendDomainHom f) :=
  (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
    ext fun x => f.injective <|
      Subtype.ext ((extendDomain_apply_image e f x).symm.trans (Perm.ext_iff.mp he (f x)))

@[simp]
/-
**Equiv.Perm.extendDomain_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain 
f = 1 ↔ e = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_one'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHo
mClass F G H] (…
· 使用定理 `Equiv.Perm.extendDomainHom_injective`：extendDomainHom_injective : Functi
on.Injective (extendDomainHom f)
-/
theorem extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e

@[simp]
/-
**Equiv.Perm.extendDomain_pow** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_pow (n : Nat) : (e ^ n).extendDomain f = e.extendDomain f ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
lemma extendDomain_pow (n : ℕ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_pow (extendDomainHom f) _ _

@[simp]
/-
**Equiv.Perm.extendDomain_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：extendDomain_zpow (n : Int) : (e ^ n).extendDomain f = e.extendDomain f ^ 
n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
-/
lemma extendDomain_zpow (n : ℤ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_zpow (extendDomainHom f) _ _

end ExtendDomain

section Subtype

variable {p : α → Prop} {f : Perm α}

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
/-
**Equiv.Perm.subtypePerm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm (f : Perm α) (h : forall x, p (f x) ↔ p x) : Perm { x // p x }
 where toFun
参数：f : Perm α；h : forall x, p (f x) ↔ p x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the permutation `f` fixes the subtype `{x // p x}`, then this returns the per
mutation
  on `{x // p x}` induced by `f`.
-/
def subtypePerm (f : Perm α) (h : ∀ x, p (f x) ↔ p x) : Perm { x // p x } where
  toFun := fun x => ⟨f x, (h _).2 x.2⟩
  invFun := fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).1 <| by simpa using x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
/-
**Equiv.Perm.subtypePerm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_apply (f : Perm α) (h : forall x, p (f x) ↔ p x) (x : { x // p
 x }) : subtypePerm f h x = ⟨f x, (h _).2 x.2⟩
参数：f : Perm α；h : forall x, p (f x) ↔ p x；x : { x // p x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypePerm_apply (f : Perm α) (h : ∀ x, p (f x) ↔ p x) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).2 x.2⟩ :=
  rfl

@[simp]
/-
**Equiv.Perm.subtypePerm_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_one (p : α -> Prop) (h
参数：p : α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypePerm_one (p : α → Prop) (h := fun _ => Iff.rfl) : @subtypePerm α p 1 h = 1 :=
  rfl

@[simp]
/-
**Equiv.Perm.subtypePerm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_mul (f g : Perm α) (hf hg) : (f.subtypePerm hf * g.subtypePerm
 hg : Perm { x // p x }) = (f * g).subtypePerm fun _ => (hf _).trans hg _
参数：f g : Perm α；hf hg。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypePerm_mul (f g : Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Perm { x // p x }) =
      (f * g).subtypePerm fun _ => (hf _).trans <| hg _ :=
  rfl

set_option backward.privateInPublic true in
/-
**Equiv.Perm.inv_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem inv_aux : (∀ x, p (f x) ↔ p x) ↔ ∀ x, p (f⁻¹ x) ↔ p x :=
  f⁻¹.surjective.forall.trans <| by simp [Iff.comm]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- See `Equiv.Perm.inv_subtypePerm`. -/
/-
**Equiv.Perm.subtypePerm_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_inv (f : Perm α) (hf) : f⁻¹.subtypePerm hf = (f.subtypePerm <|
 inv_aux.2 hf : Perm { x // p x })⁻¹
参数：f : Perm α；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Equiv.Perm.inv_subtypePerm`.
-/
theorem subtypePerm_inv (f : Perm α) (hf) :
    f⁻¹.subtypePerm hf = (f.subtypePerm <| inv_aux.2 hf : Perm { x // p x })⁻¹ :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- See `Equiv.Perm.subtypePerm_inv`. -/
@[simp]
/-
**Equiv.Perm.inv_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：inv_subtypePerm (f : Perm α) (hf) : (f.subtypePerm hf : Perm { x // p x })
⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf)
参数：f : Perm α；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `Equiv.Perm.subtypePerm_inv`.
-/
theorem inv_subtypePerm (f : Perm α) (hf) :
    (f.subtypePerm hf : Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) :=
  rfl

set_option backward.privateInPublic true in
/-
**Equiv.Perm.pow_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pow_aux (hf : ∀ x, p (f x) ↔ p x) : ∀ {n : ℕ} (x), p ((f ^ n) x) ↔ p x
  | 0, _ => Iff.rfl
  | _ + 1, _ => (pow_aux hf (f _)).trans (hf _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Equiv.Perm.subtypePerm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_pow (f : Perm α) (n : Nat) (hf) : (f.subtypePerm hf : Perm { x
 // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf)
参数：f : Perm α；n : Nat；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.pow_aux`：∀ {α : Type u_4
} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℕ} (x :
 α), p ((f ^ n) x) ↔ p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Equiv.Perm.subtypePerm.congr_simp`：∀ {α : Type u_4} {p : α → Prop} (f f_
1 : Equiv.Perm α) (e_f : f = f_1) (h : ∀ (x : α), p (f x) ↔ p x),   f.subtypePer
m h = f_1.subtypePerm ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem subtypePerm_pow (f : Perm α) (n : ℕ) (hf) :
    (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [pow_succ', ih, subtypePerm_mul]

set_option backward.privateInPublic true in
/-
**Equiv.Perm.zpow_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem zpow_aux (hf : ∀ x, p (f x) ↔ p x) : ∀ {n : ℤ} (x), p ((f ^ n) x) ↔ p x
  | Int.ofNat _ => pow_aux hf
  | Int.negSucc n => by
    rw [zpow_negSucc]
    exact pow_aux (inv_aux.1 hf)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
/-
**Equiv.Perm.subtypePerm_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_zpow (f : Perm α) (n : Int) (hf) : (f.subtypePerm hf ^ n : Per
m { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf)
参数：f : Perm α；n : Int；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.zpow_aux`：∀ {α : Type u_
4} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℤ} (x 
: α), p ((f ^ n) x) ↔ p x
· 使用定理 `Equiv.Perm.subtypePerm_pow`：subtypePerm_pow (f : Perm α) (n : Nat) (hf) 
: (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.pow_aux`：∀ {α : Type u_4
} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℕ} (x :
 α), p ((f ^ n) x) ↔ p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.inv_aux`：∀ {α : Type u_4
} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) ↔ ∀ (x : α), p (
f⁻¹ x) ↔ p x
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypePerm.congr_simp`：∀ {α : Type u_4} {p : α → Prop} (f f_
1 : Equiv.Perm α) (e_f : f = f_1) (h : ∀ (x : α), p (f x) ↔ p x),   f.subtypePer
m h = f_1.subtypePerm ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subtypePerm_zpow (f : Perm α) (n : ℤ) (hf) :
    (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf) := by
  cases n with
  | ofNat n => exact subtypePerm_pow _ _ _
  | negSucc n => simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]

variable [DecidablePred p] {a : α}

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
/-
**Equiv.Perm.ofSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype : Perm (Subtype p) ->* Perm α where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points.
-/
def ofSubtype : Perm (Subtype p) →* Perm α where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm
/-
**Equiv.Perm.ofSubtype_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_subtypePerm {f : Perm α} (h₁ : forall x, p (f x) ↔ p x) (h₂ : fo
rall x, f x != x -> p x) : ofSubtype (subtypePerm f h₁) = f
参数：h₁ : forall x, p (f x) ↔ p x；h₂ : forall x, f x != x -> p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.ofSubtype.eq_1`：∀ {α : Type u_4} {p : α → Prop} [inst : Decid
ablePred p],   Equiv.Perm.ofSubtype = { toFun := fun f => f.extendDomain (Equiv.
refl (Subtype p…
· 使用定理 `MonoidHom.coe_mk`：MonoidHom.coe_mk [MulOne M] [MulOne N] (f hmul) : (Mon
oidHom.mk f hmul : M -> N) = f
· 使用定理 `OneHom.coe_mk`：OneHom.coe_mk [One M] [One N] (f : M -> N) (h1) : (OneHom
.mk f h1 : M -> N) = f
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem ofSubtype_subtypePerm {f : Perm α} (h₁ : ∀ x, p (f x) ↔ p x) (h₂ : ∀ x, f x ≠ x → p x) :
    ofSubtype (subtypePerm f h₁) = f :=
  Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
        Equiv.Perm.extendDomain_apply_not_subtype _ _ hx]
      exact not_not.mp fun h => hx (h₂ x (Ne.symm h))
/-
**Equiv.Perm.ofSubtype_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a =
 f ⟨a, ha⟩
参数：f : Perm (Subtype p)；ha : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_apply_subtype`：∀ {α' : Type u_9} {β' : Type u_10
} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype
 p)   {b : β'} (h : p b), (…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩ :=
  extendDomain_apply_subtype _ _ ha

@[simp]
/-
**Equiv.Perm.ofSubtype_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x
 = f x
参数：f : Perm (Subtype p)；x : Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
-/
theorem ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x = f x :=
  Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f
/-
**Equiv.Perm.ofSubtype_apply_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype 
f a = a
参数：f : Perm (Subtype p)；ha : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a :=
  extendDomain_apply_not_subtype _ _ ha
/-
**Equiv.Perm.ofSubtype_apply_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_apply_mem_iff_mem (f : Perm (Subtype p)) (x : α) : p ((ofSubtype
 f : α -> α) x) ↔ p x
参数：f : Perm (Subtype p)；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofSubtype_apply_mem_iff_mem (f : Perm (Subtype p)) (x : α) :
    p ((ofSubtype f : α → α) x) ↔ p x :=
  if h : p x then by
    simpa only [h, iff_true, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.ofSubtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：ofSubtype_injective : Function.Injective (ofSubtype : Perm (Subtype p) -> 
Perm α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
· 使用定理 `SetCoe.ext_iff`：SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a
 = b
· 使用定理 `Equiv.Perm.ofSubtype_apply_coe`：ofSubtype_apply_coe (f : Perm (Subtype p
)) (x : Subtype p) : ofSubtype f x = f x
-/
theorem ofSubtype_injective : Function.Injective (ofSubtype : Perm (Subtype p) → Perm α) := by
  intro x y h
  rw [Perm.ext_iff] at h ⊢
  intro a
  specialize h a
  rwa [ofSubtype_apply_coe, ofSubtype_apply_coe, SetCoe.ext_iff] at h

@[simp]
/-
**Equiv.Perm.subtypePerm_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_ofSubtype (f : Perm (Subtype p)) : subtypePerm (ofSubtype f) (
ofSubtype_apply_mem_iff_mem f) = f
参数：f : Perm (Subtype p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.Perm.ofSubtype_apply_mem_iff_mem`：ofSubtype_apply_mem_iff_mem (f :
 Perm (Subtype p)) (x : α) : p ((ofSubtype f : α -> α) x) ↔ p x
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Equiv.Perm.ofSubtype_apply_coe`：ofSubtype_apply_coe (f : Perm (Subtype p
)) (x : Subtype p) : ofSubtype f x = f x
-/
theorem subtypePerm_ofSubtype (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (ofSubtype_apply_mem_iff_mem f) = f :=
  Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)
/-
**Equiv.Perm.ofSubtype_subtypePerm_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：ofSubtype_subtypePerm_of_mem {p : α -> Prop} [DecidablePred p] {g : Perm α
} (hg : forall (x : α), p (g x) ↔ p x) {a : α} (ha : p a) : (ofSubtype (g.subtyp
ePerm hg)) a = g a
参数：hg : forall (x : α), p (g x) ↔ p x；ha : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
-/
theorem ofSubtype_subtypePerm_of_mem {p : α → Prop} [DecidablePred p]
    {g : Perm α} (hg : ∀ (x : α), p (g x) ↔ p x)
    {a : α} (ha : p a) : (ofSubtype (g.subtypePerm hg)) a = g a :=
  ofSubtype_apply_of_mem (g.subtypePerm hg) ha
/-
**Equiv.Perm.ofSubtype_subtypePerm_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm`。
形式化陈述：ofSubtype_subtypePerm_of_not_mem {p : α -> Prop} [DecidablePred p] {g : Pe
rm α} (hg : forall (x : α), p (g x) ↔ p x) {a : α} (ha : ¬ p a) : (ofSubtype (g.
subtypePerm hg)) a = a
参数：hg : forall (x : α), p (g x) ↔ p x；ha : ¬ p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
-/
theorem ofSubtype_subtypePerm_of_not_mem {p : α → Prop} [DecidablePred p]
    {g : Perm α} (hg : ∀ (x : α), p (g x) ↔ p x)
    {a : α} (ha : ¬ p a) : (ofSubtype (g.subtypePerm hg)) a = a :=
  ofSubtype_apply_of_not_mem (g.subtypePerm hg) ha

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
/-
**Equiv.Perm.subtypeEquivSubtypePerm** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：{α : Type u_4} → (p : α → Prop) → [DecidablePred p] → Equiv.Perm (Subtype 
p) ≃ { f // ∀ (a : α), ¬p a → f a = a }
参数：p : α → Prop；Subtype p；a : α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Equiv.Perm.subtypePerm_ofSubtype`：subtypePerm_ofSubtype (f : Perm (Subty
pe p)) : subtypePerm (ofSubtype f) (ofSubtype_apply_mem_iff_mem f) = f

--- 原说明 ---
Permutations on a subtype are equivalent to permutations on the original type th
at fix pointwise
the rest.
-/
protected def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a } where
  toFun f := ⟨ofSubtype f, fun _ => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun _ =>
      ⟨Decidable.not_imp_not.1 fun hfa => (f.prop _ hfa).symm ▸ hfa,
        Decidable.not_imp_not.1 fun hfa ha => hfa <| f.val.injective (f.prop _ hfa).symm ▸ ha⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext ((Equiv.Perm.ofSubtype_subtypePerm _) fun a => Not.decidable_imp_symm <| f.prop a)
/-
**Equiv.Perm.subtypeEquivSubtypePerm_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm`。
形式化陈述：subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) : (P
erm.subtypeEquivSubtypePerm p f).1 a = f ⟨a, h⟩
参数：f : Perm (Subtype p)；h : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
-/
theorem subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) :
    (Perm.subtypeEquivSubtypePerm p f).1 a = f ⟨a, h⟩ :=
  f.ofSubtype_apply_of_mem h
/-
**Equiv.Perm.subtypeEquivSubtypePerm_apply_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm`。
形式化陈述：subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a)
 : ((Perm.subtypeEquivSubtypePerm p) f).1 a = a
参数：f : Perm (Subtype p)；h : ¬p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
-/
theorem subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a) :
    ((Perm.subtypeEquivSubtypePerm p) f).1 a = a :=
  f.ofSubtype_apply_of_not_mem h

end Subtype

end Perm

section Swap

variable [DecidableEq α]

@[simp]
/-
**Equiv.swap_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (x y : α), (Equiv.swap x y)⁻¹ = Eq
uiv.swap x y
参数：x y : α；Equiv.swap x y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl

@[simp]
/-
**Equiv.swap_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), Equiv.swap i j * Equiv.
swap i j = 1
参数：i j : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.swap_swap`：swap_swap (a b : α) : (swap a b).trans (swap a b) = Equ
iv.refl _
-/
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j
/-
**Equiv.swap_mul_eq_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (f : Equiv.Perm α) (x y : α),   Eq
uiv.swap x y * f = f * Equiv.swap (f⁻¹ x) (f⁻¹ y)
参数：f : Equiv.Perm α；x y : α；f⁻¹ x；f⁻¹ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]; split_ifs <;> simp_all [eq_symm_apply]
/-
**Equiv.mul_swap_eq_swap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (f : Equiv.Perm α) (x y : α), f * 
Equiv.swap x y = Equiv.swap (f x) (f y) * f
参数：f : Equiv.Perm α；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_mul_eq_mul_swap`：∀ {α : Type u_4} [inst : DecidableEq α] (f :
 Equiv.Perm α) (x y : α),   Equiv.swap x y * f = f * Equiv.swap (f⁻¹ x) (f⁻¹ y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  simp [swap_mul_eq_mul_swap]
/-
**Equiv.swap_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (f : Equiv.Perm α) (x y : α), Equi
v.swap (f x) (f y) = f * Equiv.swap x y * f⁻¹
参数：f : Equiv.Perm α；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.mul_swap_eq_swap_mul`：∀ {α : Type u_4} [inst : DecidableEq α] (f :
 Equiv.Perm α) (x y : α), f * Equiv.swap x y = Equiv.swap (f x) (f y) * f
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
/-
**Equiv.swap_mul_self_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α) (σ : Equiv.Perm α), Equi
v.swap i j * (Equiv.swap i j * σ) = σ
参数：i j : α；σ : Equiv.Perm α；Equiv.swap i j * σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), 
Equiv.swap i j * Equiv.swap i j = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Left-multiplying a permutation with `swap i j` twice gives the original permutat
ion.

  This specialization of `swap_mul_self` is useful when using cosets of permutat
ions.
-/
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ := by
  simp [← mul_assoc]

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
/-
**Equiv.mul_swap_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α) (σ : Equiv.Perm α), σ * 
Equiv.swap i j * Equiv.swap i j = σ
参数：i j : α；σ : Equiv.Perm α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Equiv.swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), 
Equiv.swap i j * Equiv.swap i j = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Right-multiplying a permutation with `swap i j` twice gives the original permuta
tion.

  This specialization of `swap_mul_self` is useful when using cosets of permutat
ions.
-/
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by
  rw [mul_assoc, swap_mul_self, mul_one]

/-- A stronger version of `mul_right_injective` -/
@[simp]
/-
**Equiv.swap_mul_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), Function.Involutive fun
 x => Equiv.swap i j * x
参数：i j : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.swap_mul_self_mul`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : 
α) (σ : Equiv.Perm α), Equiv.swap i j * (Equiv.swap i j * σ) = σ

--- 原说明 ---
A stronger version of `mul_right_injective`
-/
theorem swap_mul_involutive (i j : α) : Function.Involutive (Equiv.swap i j * ·) :=
  swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
/-
**Equiv.mul_swap_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] (i j : α), Function.Involutive fun
 x => x * Equiv.swap i j
参数：i j : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.mul_swap_mul_self`：∀ {α : Type u_4} [inst : DecidableEq α] (i j : 
α) (σ : Equiv.Perm α), σ * Equiv.swap i j * Equiv.swap i j = σ

--- 原说明 ---
A stronger version of `mul_left_injective`
-/
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j

@[simp]
/-
**Equiv.swap_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α}, Equiv.swap i j = 1 ↔ i 
= j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.swap_eq_refl_iff`：swap_eq_refl_iff {x y : α} : swap x y = Equiv.re
fl _ ↔ x = y
-/
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  swap_eq_refl_iff
/-
**Equiv.swap_mul_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α} {σ : Equiv.Perm α}, Equi
v.swap i j * σ = σ ↔ i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_right`：mul_eq_right : a * b = b ↔ a = 1
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Equiv.swap_eq_one_iff`：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α}
, Equiv.swap i j = 1 ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j := by
  rw [mul_eq_right, swap_eq_one_iff]
/-
**Equiv.mul_swap_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α} {σ : Equiv.Perm α}, σ * 
Equiv.swap i j = σ ↔ i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_left`：mul_eq_left : a * b = a ↔ b = 1
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Equiv.swap_eq_one_iff`：∀ {α : Type u_4} [inst : DecidableEq α] {i j : α}
, Equiv.swap i j = 1 ↔ i = j
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j := by
  rw [mul_eq_left, swap_eq_one_iff]
/-
**Equiv.swap_mul_swap_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {x y z : α},   x ≠ y → x ≠ z → Equ
iv.swap y z * Equiv.swap x y * Equiv.swap y z = Equiv.swap z x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.swap_inv`：∀ {α : Type u_4} [inst : DecidableEq α] (x y : α), (Equi
v.swap x y)⁻¹ = Equiv.swap x y
· 使用定理 `Equiv.swap_apply_apply`：∀ {α : Type u_4} [inst : DecidableEq α] (f : Equ
iv.Perm α) (x y : α), Equiv.swap (f x) (f y) = f * Equiv.swap x y * f⁻¹
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
-/
theorem swap_mul_swap_mul_swap {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) :
    swap y z * swap x y * swap y z = swap z x := by
  nth_rewrite 3 [← swap_inv]
  rw [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hxy hxz, swap_comm]

end Swap

section Group
variable [Group α] (a b : α)

@[to_additive (attr := simp)]
/-
**Equiv.mulLeft_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α], Equiv.mulLeft 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma mulLeft_one : Equiv.mulLeft (1 : α) = 1 := ext one_mul

@[to_additive (attr := simp)]
/-
**Equiv.mulRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α], Equiv.mulRight 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma mulRight_one : Equiv.mulRight (1 : α) = 1 := ext mul_one

@[to_additive (attr := simp)]
/-
**Equiv.mulLeft_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a b : α), Equiv.mulLeft (a * b) = Equiv
.mulLeft a * Equiv.mulLeft b
参数：a b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
  ext <| mul_assoc _ _

@[to_additive (attr := simp)]
/-
**Equiv.mulRight_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a b : α), Equiv.mulRight (a * b) = Equi
v.mulRight b * Equiv.mulRight a
参数：a b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mulRight_mul : Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a :=
  ext fun _ ↦ (mul_assoc _ _ _).symm

@[to_additive (attr := simp)]
/-
**Equiv.inv_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α), (Equiv.mulLeft a)⁻¹ = Equiv.mul
Left a⁻¹
参数：a : α；Equiv.mulLeft a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.coe_inj`：∀ {α : Sort u} {β : Sort v} {e₁ e₂ : α ≃ β}, ⇑e₁ = ⇑e₂ ↔ 
e₁ = e₂
-/
lemma inv_mulLeft : (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]
/-
**Equiv.inv_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α), (Equiv.mulRight a)⁻¹ = Equiv.mu
lRight a⁻¹
参数：a : α；Equiv.mulRight a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.coe_inj`：∀ {α : Sort u} {β : Sort v} {e₁ e₂ : α ≃ β}, ⇑e₁ = ⇑e₂ ↔ 
e₁ = e₂
-/
lemma inv_mulRight : (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹ := Equiv.coe_inj.1 rfl

@[to_additive (attr := simp)]
/-
**Equiv.pow_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℕ), Equiv.mulLeft a ^ n = E
quiv.mulLeft (a ^ n)
参数：a : α；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_mulLeft (n : ℕ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]
/-
**Equiv.pow_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℕ), Equiv.mulRight a ^ n = 
Equiv.mulRight (a ^ n)
参数：a : α；n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_right_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (
fun x => x * a)^[n] = fun x => x * a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_mulRight (n : ℕ) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) := by
  ext; simp [Perm.coe_pow]

@[to_additive (attr := simp)]
/-
**Equiv.zpow_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℤ), Equiv.mulLeft a ^ n = E
quiv.mulLeft (a ^ n)
参数：a : α；n : ℤ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.pow_mulLeft`：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℕ), Eq
uiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Equiv.inv_mulLeft`：∀ {α : Type u_4} [inst : Group α] (a : α), (Equiv.mul
Left a)⁻¹ = Equiv.mulLeft a⁻¹
-/
lemma zpow_mulLeft : ∀ n : ℤ, Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

@[to_additive (attr := simp)]
/-
**Equiv.zpow_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℤ), Equiv.mulRight a ^ n = 
Equiv.mulRight (a ^ n)
参数：a : α；n : ℤ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.pow_mulRight`：∀ {α : Type u_4} [inst : Group α] (a : α) (n : ℕ), E
quiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Equiv.inv_mulRight`：∀ {α : Type u_4} [inst : Group α] (a : α), (Equiv.mu
lRight a)⁻¹ = Equiv.mulRight a⁻¹
-/
lemma zpow_mulRight : ∀ n : ℤ, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  | Int.ofNat n => by simp
  | Int.negSucc n => by simp

end Group
end Equiv

/-- The group of multiplicative automorphisms. -/
@[to_additive /-- The group of additive automorphisms. -/]
/-
**MulAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(M : Type u_7) → [Mul M] → Type u_7
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of multiplicative automorphisms.
-/
abbrev MulAut (M : Type*) [Mul M] :=
  M ≃* M

namespace MulAut

variable (M) [Mul M]

/-- If `M` is a type with multiplicative, then multiplicative automorphisms of `M` have the
/-
**MulAut.of** 是 Mathlib 中的一个结构，位于命名空间 `MulAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure of a group. -/
@[to_additive /-- If `M` is a type with addition, then additive automorphisms of `M` have the
/-
**MulAut.of** 是 Mathlib 中的一个结构，位于命名空间 `MulAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a type with multiplicative, then multiplicative automorphisms of `M` h
ave the
structure of a group.
-/
structure of a group.

We give `AddAut M` the structure of an additive group rather than a multiplicative group to help
with `to_additive` translation. Without this, any proof in group theory making use of the
conjugation action `G →* MulAut G` would be impossible to `to_additive`-ize because a correct
additivization would require inserting `Additive` around `AddAut G` and dealing with these extra
`Additive`s in the proof, but `to_additive` is unable to do this automatically. -/]
/-
**MulAut.** 是 Mathlib 中的一个实例，位于命名空间 `MulAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (MulAut M) where
  mul g h := MulEquiv.trans h g
  one := MulEquiv.refl _
  inv := MulEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := MulEquiv.self_trans_symm

@[to_additive]
/-
**MulAut.** 是 Mathlib 中的一个实例，位于命名空间 `MulAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MulAut M) :=
  ⟨1⟩

@[to_additive (attr := simp)]
/-
**MulAut.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e₁ e₂ : MulAut M), ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑e₂
参数：M : Type u_2；e₁ e₂ : MulAut M；e₁ * e₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAut.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M], ⇑1 = id
参数：M : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAut.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M), ⇑e⁻¹ = ⇑(MulEquiv.symm e)
参数：M : Type u_2；e : MulAut M；MulEquiv.symm e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv (e : MulAut M) : ⇑e⁻¹ = e.symm := rfl

@[to_additive]
/-
**MulAut.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e₁ e₂ : MulAut M), e₁ * e₂ = MulEquiv.tra
ns e₂ e₁
参数：M : Type u_2；e₁ e₂ : MulAut M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

@[to_additive]
/-
**MulAut.one_def** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M], 1 = MulEquiv.refl M
参数：M : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl

@[to_additive]
/-
**MulAut.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e₁ : MulAut M), e₁⁻¹ = MulEquiv.symm e₁
参数：M : Type u_2；e₁ : MulAut M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAut.inv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M), MulEquiv.symm e⁻¹ = e
参数：M : Type u_2；e : MulAut M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_symm (e : MulAut M) : e⁻¹.symm = e := rfl

@[to_additive (attr := simp)]
/-
**MulAut.symm_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M), (MulEquiv.symm e)⁻¹ = e
参数：M : Type u_2；e : MulAut M；MulEquiv.symm e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_inv (e : MulAut M) : (e.symm)⁻¹ = e := rfl

@[to_additive (attr := simp)]
/-
**MulAut.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M), e⁻¹ m = (MulEquiv.
symm e) m
参数：M : Type u_2；e : MulAut M；m : M；MulEquiv.symm e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAut.inv_def`：∀ (M : Type u_2) [inst : Mul M] (e₁ : MulAut M), e₁⁻¹ = 
MulEquiv.symm e₁
-/
theorem inv_apply (e : MulAut M) (m : M) : e⁻¹ m = e.symm m := by
  rw [inv_def]

@[to_additive (attr := simp)]
/-
**MulAut.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e₁ e₂ : MulAut M) (m : M), (e₁ * e₂) m = 
e₁ (e₂ m)
参数：M : Type u_2；e₁ e₂ : MulAut M；m : M；e₁ * e₂；e₂ m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAut.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (m : M), 1 m = m
参数：M : Type u_2；m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl

@[to_additive]
/-
**MulAut.apply_inv_self** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M), e (e⁻¹ m) = m
参数：M : Type u_2；e : MulAut M；m : M；e⁻¹ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _

@[to_additive]
/-
**MulAut.inv_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ (M : Type u_2) [inst : Mul M] (e : MulAut M) (m : M), e⁻¹ (e m) = m
参数：M : Type u_2；e : MulAut M；m : M；e m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
/-
**MulAut.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `MulAut`。
形式化陈述：(M : Type u_2) → [inst : Mul M] → MulAut M →* Equiv.Perm M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid hom from the group of multiplicative automorphisms to the group of permut
ations.
-/
def toPerm : MulAut M →* Equiv.Perm M where
  toFun := MulEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Group conjugation, `MulAut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `MulAut G`.
See also the type `ConjAct G` for any group `G`, which has a `MulAction (ConjAct G) G` instance
where `conj G` acts on `G` by conjugation. -/
@[to_additive /-- Group conjugation, `AddAut.addConj g h = g + h + -g`, as an additive homomorphism
mapping addition in `G` into addition in the additive automorphism group `AddAut G`. -/]
/-
**MulAut.conj** 是 Mathlib 中的一个定义，位于命名空间 `MulAut`。
形式化陈述：{G : Type u_3} → [inst : Group G] → G →* MulAut G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conj [Group G] : G →* MulAut G where
  toFun g :=
    { toFun h := g * h * g⁻¹
      invFun h := g⁻¹ * h * g
      left_inv _ := by simp [mul_assoc]
      right_inv _ := by simp [mul_assoc]
      map_mul' := by simp [mul_assoc] }
  map_mul' _ _ := by ext; simp [mul_assoc]
  map_one' := by ext; simp

@[to_additive (attr := simp)]
/-
**MulAut.conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (g h : G), (MulAut.conj g) h = g * h * g
⁻¹
参数：g h : G；MulAut.conj g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_apply [Group G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAut.conj_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (g h : G), (MulEquiv.symm (MulAut.conj g
)) h = g⁻¹ * h * g
参数：g h : G；MulEquiv.symm (MulAut.conj g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_symm_apply [Group G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl

@[to_additive]
/-
**MulAut.conj_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulAut`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] (g h : G), (MulAut.conj g)⁻¹ h = g⁻¹ * h
 * g
参数：g h : G；MulAut.conj g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conj_inv_apply [Group G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl

/-- Isomorphic groups have isomorphic automorphism groups. -/
@[to_additive (attr := simps) /-- Isomorphic groups have isomorphic automorphism groups. -/]
/-
**MulAut.congr** 是 Mathlib 中的一个定义，位于命名空间 `MulAut`。
形式化陈述：{G : Type u_3} → [inst : Group G] → {H : Type u_7} → [inst_1 : Group H] → 
G ≃* H → MulAut G ≃* MulAut H
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic groups have isomorphic automorphism groups.
-/
def congr [Group G] {H : Type*} [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

end MulAut

namespace AddAut

variable (A) [Add A]

@[deprecated (since := "2026-05-26")] alias coe_mul := coe_add
@[deprecated (since := "2026-05-26")] alias coe_one := coe_zero
@[deprecated (since := "2026-05-26")] alias coe_inv := coe_neg
@[deprecated (since := "2026-05-26")] alias mul_def := add_def
@[deprecated (since := "2026-05-26")] alias one_def := zero_def
@[deprecated (since := "2026-05-26")] alias inv_def := neg_def
@[deprecated (since := "2026-05-26")] alias mul_apply := add_apply
@[deprecated (since := "2026-05-26")] alias one_apply := zero_apply
@[deprecated (since := "2026-05-26")] alias inv_symm := neg_symm
@[deprecated (since := "2026-05-26")] alias symm_inv := symm_neg
@[deprecated (since := "2026-05-26")] alias inv_apply := neg_apply
@[deprecated (since := "2026-05-26")] alias inv_apply_self := neg_apply_self
@[deprecated (since := "2026-05-26")] alias apply_inv_self := apply_neg_self

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
/-
**AddAut.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `AddAut`。
形式化陈述：(A : Type u_1) → [inst : Add A] → AddAut A →+ Additive (Equiv.Perm A)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid hom from the group of multiplicative automorphisms to the group of permut
ations.
-/
def toPerm : AddAut A →+ Additive (Equiv.Perm A) where
  toFun := AddEquiv.toEquiv
  map_zero' := rfl
  map_add' _ _ := rfl

@[deprecated (since := "2026-05-26")] alias conj := addConj
@[deprecated (since := "2026-05-26")] alias conj_apply := addConj_apply
@[deprecated (since := "2026-05-26")] alias conj_symm_apply := addConj_symm_apply
@[deprecated (since := "2026-05-26")] alias conj_inv_apply := addConj_neg_apply

@[deprecated "use `addConj_neg_apply` instead" (since := "2026-05-26")]
/-
**AddAut.neg_conj_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddAut`。
形式化陈述：∀ {G : Type u_3} [inst : AddGroup G] (g h : G), (-AddAut.addConj g) h = -g
 + h + g
参数：g h : G；-AddAut.addConj g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddAut.neg_apply`：∀ (M : Type u_2) [inst : Add M] (e : AddAut M) (m : M)
, (-e) m = (AddEquiv.symm e) m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_conj_apply [AddGroup G] (g h : G) : (-addConj g) h = -g + h + g := by
  simp

end AddAut

variable (G)

/-- `Multiplicative G` and `G` have isomorphic automorphism groups. -/
@[simps!]
/-
**MulAutMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(G : Type u_3) → [inst : AddGroup G] → MulAut (Multiplicative G) ≃* Multip
licative (AddAut G)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Multiplicative G` and `G` have isomorphic automorphism groups.
-/
def MulAutMultiplicative [AddGroup G] : MulAut (Multiplicative G) ≃* Multiplicative (AddAut G) :=
  { AddEquiv.toMultiplicative.symm with map_mul' := fun _ _ ↦ rfl }

/-- `Additive G` and `G` have isomorphic automorphism groups. -/
@[simps!]
/-
**AddAutAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(G : Type u_3) → [inst : Group G] → AddAut (Additive G) ≃+ Additive (MulAu
t G)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Additive G` and `G` have isomorphic automorphism groups.
-/
def AddAutAdditive [Group G] : AddAut (Additive G) ≃+ Additive (MulAut G) :=
  { MulEquiv.toAdditive.symm with map_add' := fun _ _ ↦ rfl }
