/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Ring.Subring.Defs

/-! # Subrings invariant under an action

If a monoid acts on a ring via a `MulSemiringAction`, then `IsInvariantSubring` is
a predicate on subrings asserting that the subring is fixed elementwise by the
action.

-/

@[expose] public section

assert_not_exists RelIso

section Ring

variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]
variable (S : Subring R)

open MulAction

variable {R}

/-- A typeclass for subrings invariant under a `MulSemiringAction`. -/
/-
**IsInvariantSubring** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → {R : Type u_2} → [inst : Monoid M] → [inst_1 : Ring R] → 
[MulSemiringAction M R] → Subring R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for subrings invariant under a `MulSemiringAction`.
-/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S
/-
**IsInvariantSubring.toMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] : MulSemir
ingAction M S where smul m x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • ↑x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.ext <| one_smul M (s : R)
  mul_smul m₁ m₂ s := Subtype.ext <| mul_smul m₁ m₂ (s : R)
  smul_add m s₁ s₂ := Subtype.ext <| smul_add m (s₁ : R) (s₂ : R)
  smul_zero m := Subtype.ext <| smul_zero m
  smul_one m := Subtype.ext <| smul_one m
  smul_mul m s₁ s₂ := Subtype.ext <| smul_mul' m (s₁ : R) (s₂ : R)

end Ring

section

variable (M : Type*) [Monoid M]
variable {R' : Type*} [Ring R'] [MulSemiringAction M R']
variable (U : Subring R') [IsInvariantSubring M U]

/-- The canonical inclusion from an invariant subring. -/
/-
**IsInvariantSubring.subtypeHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsInvariantSubring.subtypeHom : U ->+*[M] R'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from an invariant subring.
-/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ ↦ rfl }

@[simp]
/-
**IsInvariantSubring.coe_subtypeHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInvariantSubring.coe_subtypeHom : (IsInvariantSubring.subtypeHom M U : U
 -> R') = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsInvariantSubring.coe_subtypeHom :
    (IsInvariantSubring.subtypeHom M U : U → R') = Subtype.val := rfl

@[simp]
/-
**IsInvariantSubring.coe_subtypeHom'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInvariantSubring.coe_subtypeHom' : ((IsInvariantSubring.subtypeHom M U) 
: U ->+* R') = U.subtype
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulSemiringActionSemiHomClass.toRingHomClass`：∀ {F : Type u_15} {M : out
Param (Type u_16)} {N : outParam (Type u_17)} [inst : Monoid M] [inst_1 : Monoid
 N]   (φ : outParam (M → N)) {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
theorem IsInvariantSubring.coe_subtypeHom' :
    ((IsInvariantSubring.subtypeHom M U) : U →+* R') = U.subtype := rfl

end

