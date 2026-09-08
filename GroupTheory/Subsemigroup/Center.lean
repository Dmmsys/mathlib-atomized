/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Subsemigroup.Defs

/-!
# Centers of semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
-/

@[expose] public section

assert_not_exists RelIso Finset

/-! ### `Set.center` as a `Subsemigroup`. -/

variable (M)
namespace Subsemigroup

section Mul
variable [Mul M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive /-- The center of an additive semigroup `M` is the set of elements that commute with
everything in `M` -/]
/-
**Subsemigroup.center** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：center : Subsemigroup M where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mul_mem_center`：mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ in Set.center M
) (hz₂ : z₂ in Set.center M) : z₁ * z₂ in Set.center M
-/
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center

variable {M}

/-- The center of a magma is commutative and associative. -/
@[to_additive /-- The center of an additive magma is commutative and associative. -/]
/-
**Subsemigroup.center.commSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup.cent
er`。
形式化陈述：{M : Type u_1} → [inst : Mul M] → CommSemigroup ↥(Subsemigroup.center M)
参数：Subsemigroup.center M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M

--- 原说明 ---
The center of a magma is commutative and associative.
-/
instance center.commSemigroup : CommSemigroup (center M) where
  mul_assoc _ b _ := Subtype.ext <| b.2.mid_assoc _ _
  mul_comm a _ := Subtype.ext <| a.2.comm _

end Mul

section Semigroup
variable {M} [Semigroup M]

@[to_additive]
/-
**Subsemigroup.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_center_iff {z : M} : z in center M ↔ forall g, g * z = z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]
/-
**Subsemigroup.decidableMemCenter** 是 Mathlib 中的一个实例，位于命名空间 `Subsemigroup`。
形式化陈述：decidableMemCenter (a) [Decidable <| forall b : M, b * a = a * b] : Decida
ble (a in center M)
参数：a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
-/
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] :
    Decidable (a ∈ center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

@[to_additive (attr := simp)]
/-
**Subsemigroup.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：center_eq_top : center M = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end CommSemigroup

end Subsemigroup

