/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `ContinuousMap α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | Continuous f }`. For example, when `β` is a group, a subgroup
`continuousSubgroup α β` of `α → β` is constructed with carrier `{ f : α → β | Continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuousSubgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/

@[expose] public section

assert_not_exists StoneCech

--attribute [elab_without_expected_type] Continuous.comp

namespace ContinuousFunctions

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : { f : α → β | Continuous f }}

/-
**ContinuousFunctions.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousFunctions`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-! ### `mul` and `add` -/

@[to_additive]
/-
**ContinuousMap.instMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instMul [Mul β] [ContinuousMul β] : Mul C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `mul` and `add`
-/
instance instMul [Mul β] [ContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.continuous.prodMk g.continuous :)⟩⟩

@[to_additive (attr := norm_cast, simp)]
/-
**ContinuousMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g
参数：f g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = 
f x * g x
参数：f g : C(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.mul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) : (f₁ *
 f₂).comp g = f₁.comp g * f₂.comp g
参数：f₁ f₂ : C(β, γ)；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl

/-! ### `one` -/

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `one`
-/
instance [One β] : One C(α, β) :=
  ⟨const α 1⟩

@[to_additive (attr := norm_cast, simp)]
/-
**ContinuousMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_one [One β] : ⇑(1 : C(α, β)) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one [One β] : ⇑(1 : C(α, β)) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：one_apply [One β] (x : α) : (1 : C(α, β)) x = 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.one_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1
参数：g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.comp_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：comp_one [One β] (g : C(β, γ)) : g.comp (1 : C(α, β)) = const α (g 1)
参数：g : C(β, γ)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_one [One β] (g : C(β, γ)) : g.comp (1 : C(α, β)) = const α (g 1) := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.const_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：const_one [One β] : const α (1 : β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_one [One β] : const α (1 : β) = 1 := rfl

/-! ### `Nat.cast` -/

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Nat.cast`
-/
instance [NatCast β] : NatCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
/-
**ContinuousMap.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_natCast [NatCast β] (n : Nat) : ((n : C(α, β)) : α -> β) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast [NatCast β] (n : ℕ) : ((n : C(α, β)) : α → β) = n :=
  rfl

@[simp]
/-
**ContinuousMap.natCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：natCast_apply [NatCast β] (n : Nat) (x : α) : (n : C(α, β)) x = n
参数：n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_apply [NatCast β] (n : ℕ) (x : α) : (n : C(α, β)) x = n :=
  rfl

/-! ### `Int.cast` -/

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `Int.cast`
-/
instance [IntCast β] : IntCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
/-
**ContinuousMap.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_intCast [IntCast β] (n : Int) : ((n : C(α, β)) : α -> β) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast [IntCast β] (n : ℤ) : ((n : C(α, β)) : α → β) = n :=
  rfl

@[simp]
/-
**ContinuousMap.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：intCast_apply [IntCast β] (n : Int) (x : α) : (n : C(α, β)) x = n
参数：n : Int；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_apply [IntCast β] (n : ℤ) (x : α) : (n : C(α, β)) x = n :=
  rfl

/-! ### `nsmul` and `pow` -/

@[to_additive]
/-
**ContinuousMap.instPow** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instPow [Monoid β] [ContinuousMul β] : Pow C(α, β) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `nsmul` and `pow`
-/
instance instPow [Monoid β] [ContinuousMul β] : Pow C(α, β) ℕ :=
  ⟨fun f n => ⟨(⇑f) ^ n, f.continuous.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
/-
**ContinuousMap.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat) : ⇑(f ^ n) = 
(⇑f) ^ n
参数：f : C(α, β)；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
/-
**ContinuousMap.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat) (x : α) : (
f ^ n) x = f x ^ n
参数：f : C(α, β)；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl

-- Don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_pow pow_apply

@[to_additive]
/-
**ContinuousMap.pow_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : Nat) (g : C(α, β)
) : (f ^ n).comp g = f.comp g ^ n
参数：f : C(β, γ)；n : Nat；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl

-- Don't make `nsmul_comp` simp as the linter complains it's redundant w.r.t. `smul_comp`
attribute [simp] pow_comp

/-! ### `inv` and `neg` -/

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `inv` and `neg`
-/
instance [Inv β] [ContinuousInv β] : Inv C(α, β) where inv f := ⟨f⁻¹, f.continuous.inv⟩

@[to_additive (attr := simp)]
/-
**ContinuousMap.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_inv [Inv β] [ContinuousInv β] (f : C(α, β)) : ⇑f⁻¹ = (⇑f)⁻¹
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv [Inv β] [ContinuousInv β] (f : C(α, β)) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：inv_apply [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻
¹
参数：f : C(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.inv_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：inv_comp [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β)) : f⁻¹.comp 
g = (f.comp g)⁻¹
参数：f : C(β, γ)；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_comp [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β)) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl

/-! ### `div` and `sub` -/

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `div` and `sub`
-/
instance [Div β] [ContinuousDiv β] : Div C(α, β) where
  div f g := ⟨f / g, f.continuous.div' g.continuous⟩

@[to_additive (attr := norm_cast, simp)]
/-
**ContinuousMap.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g
参数：f g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.div_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = 
f x / g x
参数：f g : C(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.div_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) : (f / g)
.comp h = f.comp h / g.comp h
参数：f g : C(β, γ)；h : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl

/-! ### `zpow` and `zsmul` -/

@[to_additive]
/-
**ContinuousMap.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instZPow [Group β] [IsTopologicalGroup β] : Pow C(α, β) Int where pow f z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `zpow` and `zsmul`
-/
instance instZPow [Group β] [IsTopologicalGroup β] : Pow C(α, β) ℤ where
  pow f z := ⟨(⇑f) ^ z, f.continuous.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
/-
**ContinuousMap.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_zpow [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int) : ⇑(f ^ 
z) = (⇑f) ^ z
参数：f : C(α, β)；z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zpow [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : ℤ) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

@[to_additive]
/-
**ContinuousMap.zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：zpow_apply [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int) (x : α
) : (f ^ z) x = f x ^ z
参数：f : C(α, β)；z : Int；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zpow_apply [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : ℤ) (x : α) :
    (f ^ z) x = f x ^ z :=
  rfl

-- Don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_zpow zpow_apply

@[to_additive]
/-
**ContinuousMap.zpow_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：zpow_comp [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : Int) (g : C(
α, β)) : (f ^ z).comp g = f.comp g ^ z
参数：f : C(β, γ)；z : Int；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zpow_comp [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) :
    (f ^ z).comp g = f.comp g ^ z :=
  rfl

-- Don't make `zsmul_comp` simp as the linter complains it's redundant w.r.t. `smul_comp`
attribute [simp] zpow_comp

end ContinuousMap

section GroupStructure

/-!
### Group structure

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/-- The `Submonoid` of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubmonoid` of continuous maps `α → β`. -/]
/-
**continuousSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [Topologi
calSpace β] [MulOneClass β] [ContinuousMul β] : Submonoid (α -> β) where carrier
参数：α : Type*；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Submonoid` of continuous maps `α → β`.
-/
def continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β) where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubgroup` of continuous maps `α → β`. -/]
/-
**continuousSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [Topologic
alSpace β] [Group β] [IsTopologicalGroup β] : Subgroup (α -> β)
参数：α : Type*；β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G

--- 原说明 ---
The subgroup of continuous maps `α → β`.
-/
def continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [IsTopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup β] [ContinuousMul β] : Semigroup C(α, β) := fast_instance%
  coe_injective.semigroup _ coe_mul

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemigroup β] [ContinuousMul β] : CommSemigroup C(α, β) := fast_instance%
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass β] [ContinuousMul β] : MulOneClass C(α, β) := fast_instance%
  coe_injective.mulOneClass _ coe_one coe_mul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C(α, β) := fast_instance%
  coe_injective.mulZeroClass _ coe_zero coe_mul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C(α, β) := fast_instance%
  coe_injective.semigroupWithZero _ coe_zero coe_mul

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] [ContinuousMul β] : Monoid C(α, β) := fast_instance%
  coe_injective.monoid _ coe_one coe_mul coe_pow
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MonoidWithZero β] [ContinuousMul β] : MonoidWithZero C(α, β) := fast_instance%
  coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid β] [ContinuousMul β] : CommMonoid C(α, β) := fast_instance%
  coe_injective.commMonoid _ coe_one coe_mul coe_pow
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoidWithZero β] [ContinuousMul β] : CommMonoidWithZero C(α, β) := fast_instance%
  coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallyCompactSpace α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β) :=
  ⟨by
    refine continuous_of_continuous_uncurry _ ?_
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval.comp (continuous_fst.prodMap continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval.comp (continuous_snd.prodMap continuous_id)
    exact h1.mul h2⟩

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps)
  /-- Coercion to a function as an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/]
/-
**ContinuousMap.coeFnMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) ->* α -> β where toF
un f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) →* α → β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

variable (α) in
/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeft`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (continuous) homomorphism of topological `AddMonoid`s, as an
`AddMonoidHom`. Similar to `AddMonoidHom.comp_left`. -/]
/-
**ContinuousMap._root_.MonoidHom.compLeftContinuous** 是 Mathlib 中的一个定义，位于命名空间 `C
ontinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.MonoidHom.compLeftContinuous {γ : Type*} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β →* γ) (hg : Continuous g) :
    C(α, β) →* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

/-- Composition on the right as a `MonoidHom`. Similar to `MonoidHom.compHom'`. -/
@[to_additive (attr := simps)
      /-- Composition on the right as an `AddMonoidHom`. Similar to `AddMonoidHom.compHom'`. -/]
/-
**ContinuousMap.compMonoidHom'** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：compMonoidHom' {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [Continuou
sMul γ] (g : C(α, β)) : C(β, γ) ->* C(α, γ) where toFun f
参数：g : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compMonoidHom' {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) →* C(α, γ) where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g

@[to_additive (attr := simp)]
/-
**ContinuousMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : 
ι -> C(α, β)) : ⇑(∏ i in s, f i) = ∏ i in s, (f i : α -> β)
参数：s : Finset ι；f : ι -> C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι → C(α, β)) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : α → β) :=
  map_prod coeFnMonoidHom f s

@[to_additive]
/-
**ContinuousMap.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f 
: ι -> C(α, β)) (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a
参数：s : Finset ι；f : ι -> C(α, β)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.coe_prod`：coe_prod [CommMonoid β] [ContinuousMul β] {ι : T
ype*} (s : Finset ι) (f : ι -> C(α, β)) : ⇑(∏ i in s, f i) = ∏ i in s, (f i : α 
-> β)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι → C(α, β))
    (a : α) : (∏ i ∈ s, f i) a = ∏ i ∈ s, f i a := by simp

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group β] [IsTopologicalGroup β] : Group C(α, β) := fast_instance%
  coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
/-
**ContinuousMap.instCommGroupContinuousMap** 是 Mathlib 中的一个实例，位于命名空间 `Continuous
Map`。
形式化陈述：instCommGroupContinuousMap [CommGroup β] [IsTopologicalGroup β] : CommGrou
p C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroupContinuousMap [CommGroup β] [IsTopologicalGroup β] :
    CommGroup C(α, β) := fast_instance%
  coe_injective.commGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommGroup β] [IsTopologicalGroup β] : IsTopologicalGroup C(α, β) where
  continuous_mul := by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt, tendsto_iff_forall_isCompact_tendstoUniformlyOn, nhds_prod_eq]
    exact fun K hK =>
      uniformContinuous_mul.comp_tendstoUniformlyOn
        ((tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK).prodMk
          (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK))
  continuous_inv := by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    exact fun K hK =>
      uniformContinuous_inv.comp_tendstoUniformlyOn
        (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK)

/-- If an infinite product of functions in `C(α, β)` converges to `g`
(for the compact-open topology), then the pointwise product converges to `g x` for all `x ∈ α`. -/
@[to_additive
  /-- If an infinite sum of functions in `C(α, β)` converges to `g` (for the compact-open topology),
then the pointwise sum converges to `g x` for all `x ∈ α`. -/]
/-
**ContinuousMap.hasProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：hasProd_apply {γ : Type*} [CommMonoid β] [ContinuousMul β] {f : γ -> C(α, 
β)} {g : C(α, β)} {L : SummationFilter γ} (hf : HasProd f g L) (x : α) : HasProd
 (fun i : γ => f i x) (g x) L
参数：α, β；α, β；hf : HasProd f g L；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comm
Monoid α] [inst_1 : TopologicalSpace α] {f : β → α} {a : α}   {L : SummationFilt
e…
· 使用定理 `ContinuousEvalConst.continuous_eval_const`：∀ {F : Type u_1} {α : outPara
m (Type u_2)} {X : outParam (Type u_3)} {inst : FunLike F α X}   {inst_1 : Topol
ogicalSpace F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalConst`：∀ {X : Type u_2} {Y : Type u_3} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   ContinuousEvalConst 
C(X, Y) X Y
-/
theorem hasProd_apply {γ : Type*} [CommMonoid β] [ContinuousMul β]
    {f : γ → C(α, β)} {g : C(α, β)} {L : SummationFilter γ} (hf : HasProd f g L) (x : α) :
    HasProd (fun i : γ => f i x) (g x) L := by
  let ev : C(α, β) →* β := (Pi.evalMonoidHom _ x).comp coeFnMonoidHom
  exact hf.map ev (continuous_eval_const x)

@[to_additive]
/-
**ContinuousMap.multipliable_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：multipliable_apply [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ -> 
C(α, β)} {L : SummationFilter γ} (hf : Multipliable f L) (x : α) : Multipliable 
(fun i : γ => f i x) L
参数：α, β；hf : Multipliable f L；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `ContinuousMap.hasProd_apply`：hasProd_apply {γ : Type*} [CommMonoid β] [C
ontinuousMul β] {f : γ -> C(α, β)} {g : C(α, β)} {L : SummationFilter γ} (hf : H
asProd f g L) (x …
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem multipliable_apply [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ → C(α, β)}
    {L : SummationFilter γ} (hf : Multipliable f L) (x : α) : Multipliable (fun i : γ ↦ f i x) L :=
  (hasProd_apply hf.hasProd x).multipliable

@[to_additive]
/-
**ContinuousMap.tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：tprod_apply [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : 
γ -> C(α, β)} {L : SummationFilter γ} (hf : Multipliable f L) [L.NeBot] (x : α) 
: ∏'[L] i : γ, f i x = (∏'[L] i : γ, f i) x
参数：α, β；hf : Multipliable f L；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `ContinuousMap.hasProd_apply`：hasProd_apply {γ : Type*} [CommMonoid β] [C
ontinuousMul β] {f : γ -> C(α, β)} {g : C(α, β)} {L : SummationFilter γ} (hf : H
asProd f g L) (x …
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
theorem tprod_apply [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ → C(α, β)}
    {L : SummationFilter γ} (hf : Multipliable f L) [L.NeBot] (x : α) :
    ∏'[L] i : γ, f i x = (∏'[L] i : γ, f i) x :=
  (hasProd_apply hf.hasProd x).tprod_eq

end ContinuousMap

end GroupStructure

section RingStructure

/-!
### Ring structure

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/


section Subtype

/-- The subsemiring of continuous maps `α → β`. -/
/-
**continuousSubsemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [Topolo
gicalSpace R] [NonAssocSemiring R] [IsTopologicalSemiring R] : Subsemiring (α ->
 R)
参数：α : Type*；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subsemiring of continuous maps `α → β`.
-/
def continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [IsTopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }

/-- The subring of continuous maps `α → β`. -/
/-
**continuousSubring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubring (α : Type*) (R : Type*) [TopologicalSpace α] [Topologica
lSpace R] [Ring R] [IsTopologicalRing R] : Subring (α -> R)
参数：α : Type*；R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring of continuous maps `α → β`.
-/
def continuousSubring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] : Subring (α → R) :=
  { continuousAddSubgroup α R, continuousSubsemiring α R with }

end Subtype

namespace ContinuousMap

/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] : NonUnitalNonAssocSemiring C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul coe_nsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalSemiring β]
    [IsTopologicalSemiring β] : NonUnitalSemiring C(α, β) := fast_instance%
  coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_nsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [AddMonoidWithOne β]
    [ContinuousAdd β] : AddMonoidWithOne C(α, β) := fast_instance%
  coe_injective.addMonoidWithOne _ coe_zero coe_one coe_add coe_nsmul coe_natCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocSemiring β]
    [IsTopologicalSemiring β] : NonAssocSemiring C(α, β) := fast_instance%
  coe_injective.nonAssocSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_natCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : Semiring C(α, β) := fast_instance%
  coe_injective.semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocRing β] [IsTopologicalRing β] : NonUnitalNonAssocRing C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalRing β]
    [IsTopologicalRing β] : NonUnitalRing C(α, β) := fast_instance%
  coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocRing β]
    [IsTopologicalRing β] : NonAssocRing C(α, β) := fast_instance%
  coe_injective.nonAssocRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_natCast coe_intCast
/-
**ContinuousMap.instRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instRing {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
 [Ring β] [IsTopologicalRing β] : Ring C(α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
    [IsTopologicalRing β] : Ring C(α, β) := fast_instance%
  coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_natCast coe_intCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalCommSemiring β] [IsTopologicalSemiring β] : NonUnitalCommSemiring C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_nsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommSemiring β]
    [IsTopologicalSemiring β] : CommSemiring C(α, β) := fast_instance%
  coe_injective.commSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalCommRing β]
    [IsTopologicalRing β] : NonUnitalCommRing C(α, β) := fast_instance%
  coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommRing β]
    [IsTopologicalRing β] : CommRing C(α, β) := fast_instance%
  coe_injective.commRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_pow coe_natCast coe_intCast
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalSemiring β] [IsTopologicalSemiring β] : IsTopologicalSemiring C(α, β) where
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalRing β] [IsTopologicalRing β] : IsTopologicalRing C(α, β) where

/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`RingHom`.  Similar to `RingHom.compLeft`. -/
@[simps!]
/-
**ContinuousMap._root_.RingHom.compLeftContinuous** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the left by a (continuous) homomorphism of topological semirings,
 as a
`RingHom`.  Similar to `RingHom.compLeft`.
-/
protected def _root_.RingHom.compLeftContinuous (α : Type*) {β : Type*} {γ : Type*}
    [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [IsTopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [IsTopologicalSemiring γ] (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }

/-- Coercion to a function as a `RingHom`. -/
@[simps!]
/-
**ContinuousMap.coeFnRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：coeFnRingHom {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpac
e β] [Semiring β] [IsTopologicalSemiring β] : C(α, β) ->+* α -> β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as a `RingHom`.
-/
def coeFnRingHom {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _),
    (coeFnAddMonoidHom : C(α, β) →+ _) with }

end ContinuousMap

end RingStructure

section ModuleStructure

/-!
### Module structure

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type*) [TopologicalSpace α]
variable (R : Type*) [Semiring R]
variable (M : Type*) [TopologicalSpace M] [AddCommGroup M]
variable [Module R M] [ContinuousConstSMul R M] [IsTopologicalAddGroup M]

/-- The `R`-submodule of continuous maps `α → M`. -/
/-
**continuousSubmodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubmodule : Submodule R (α -> M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-submodule of continuous maps `α → M`.
-/
def continuousSubmodule : Submodule R (α → M) :=
  { continuousAddSubgroup α M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type*} {M : Type*}
  [TopologicalSpace M] {M₂ : Type*} [TopologicalSpace M₂]

@[to_additive]
/-
**ContinuousMap.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instSMul [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M) :=
  ⟨fun r f => ⟨r • ⇑f, f.continuous.const_smul r⟩⟩

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] : ContinuousConstSMul R C(α, M) where
  continuous_const_smul r := continuous_postcomp ⟨_, continuous_const_smul r⟩

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace R] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R C(α, M) :=
  ⟨(continuous_postcomp ⟨_, continuous_smul⟩).comp continuous_prodMk_const⟩

@[to_additive (attr := simp, norm_cast)]
/-
**ContinuousMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c 
• f) = c • ⇑f
参数：c : R；f : C(α, M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive]
/-
**ContinuousMap.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a :
 α) : (c • f) a = c • f a
参数：c : R；f : C(α, M)；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
    (c • f) a = c • f a :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : 
C(α, β)) : (r • f).comp g = r • f.comp g
参数：r : R；f : C(β, M)；g : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
    [SMulCommClass R R₁ M] : SMulCommClass R R₁ C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [IsScalarTower R M M] :
    IsScalarTower R C(α, M) C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_mul_assoc ..
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass R M M] :
    SMulCommClass R C(α, M) C(α, M) where
  smul_comm _ _ _ := ext fun _ => (mul_smul_comm ..).symm
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass M R M] :
    SMulCommClass C(α, M) R C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm (_ : M) ..
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M) :=
  fast_instance% Function.Injective.mulAction _ coe_injective coe_smul
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
    [ContinuousConstSMul R M] : DistribMulAction R C(α, M) := fast_instance%
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [ContinuousAdd M] [Module R M] [ContinuousConstSMul R M]
variable [ContinuousAdd M₂] [Module R M₂] [ContinuousConstSMul R M₂]
/-
**ContinuousMap.module** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：module : Module R C(α, M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module R C(α, M) := fast_instance%
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

variable (R)

/-- Composition on the left by a continuous linear map, as a `ContinuousLinearMap`.
Similar to `LinearMap.compLeft`. -/
@[simps]
/-
**ContinuousMap._root_.ContinuousLinearMap.compLeftContinuous** 是 Mathlib 中的一个定义
，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the left by a continuous linear map, as a `ContinuousLinearMap`.
Similar to `LinearMap.compLeft`.
-/
protected def _root_.ContinuousLinearMap.compLeftContinuous (α : Type*) [TopologicalSpace α]
    (g : M →L[R] M₂) : C(α, M) →L[R] C(α, M₂) where
  __ := g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous
  map_smul' := fun c _ => ext fun _ => g.map_smul' c _

/-- The constant map `x ↦ y ↦ x` as a `ContinuousLinearMap`. -/
@[simps!]
/-
**ContinuousMap._root_.ContinuousLinearMap.const** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant map `x ↦ y ↦ x` as a `ContinuousLinearMap`.
-/
def _root_.ContinuousLinearMap.const (α : Type*) [TopologicalSpace α] : M →L[R] C(α, M) where
  toFun m := .const α m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
/-
**ContinuousMap.coeFnLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：coeFnLinearMap : C(α, M) ->ₗ[R] α -> M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as a `LinearMap`.
-/
def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with
    map_smul' := coe_smul }

variable (M) in
/-- Composition on the right by a continuous map, as a `ContinuousLinearMap`. -/
@[simps]
/-
**ContinuousMap.compCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：compCLM (f : C(α, β)) : C(β, M) ->L[R] C(α, M) where toFun g
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the right by a continuous map, as a `ContinuousLinearMap`.
-/
def compCLM (f : C(α, β)) : C(β, M) →L[R] C(α, M) where
  toFun g := g.comp f
  map_add' _ _ := add_comp _ _ f
  map_smul' _ _ := smul_comp _ _ f

/-- Evaluation at a point, as a continuous linear map. -/
@[simps apply]
/-
**ContinuousMap.evalCLM** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：evalCLM (x : α) : C(α, M) ->L[R] M where toFun f
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point, as a continuous linear map.
-/
def evalCLM (x : α) : C(α, M) →L[R] M where
  toFun f := f x
  map_add' _ _ := add_apply _ _ x
  map_smul' _ _ := smul_apply _ _ x

end ContinuousMap

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `ContinuousSMul` and a `IsTopologicalSemiring`. -/


section Subtype

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
/-
**continuousSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousSubalgebra : Subalgebra R (α -> A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-subalgebra of continuous maps `α → A`.
-/
def continuousSubalgebra : Subalgebra R (α → A) :=
  { continuousSubsemiring α A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }

end Subtype

section ContinuousMap

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A] {A₂ : Type*}
  [TopologicalSpace A₂] [Semiring A₂] [Algebra R A₂] [IsTopologicalSemiring A₂]

/-- Continuous constant functions as a `RingHom`. -/
/-
**ContinuousMap.C** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.C : R ->+* C(α, A) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous constant functions as a `RingHom`.
-/
def ContinuousMap.C : R →+* C(α, A) where
  toFun := fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_add _ _

@[simp]
/-
**ContinuousMap.C_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.C r a = algebraMap R
 A r
参数：r : R；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.C r a = algebraMap R A r :=
  rfl
/-
**ContinuousMap.algebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMap.algebra : Algebra R C(α, A) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ContinuousMap.algebra : Algebra R C(α, A) where
  algebraMap := ContinuousMap.C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

variable (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`AlgHom`. Similar to `AlgHom.compLeft`. -/
@[simps!]
/-
**AlgHom.compLeftContinuous** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：(R : Type u_2) →   [inst : CommSemiring R] →     {A : Type u_3} →       [i
nst_1 : TopologicalSpace A] →         [inst_2 : Semiring A] →           [inst_3 
: Algebra R A] →             [inst_4 : IsTopologicalSemiring A] →               
{A₂ : Type u_4} →                 [inst_5 : TopologicalSpace A₂] →              
     [inst_6 : Semiring A₂] →                     [inst_7 : Algebra R A₂] →     
                  [inst_8 : IsTopologicalSemiring A₂] →                         
{α : Type u_5} →                           [inst_9 : TopologicalSpace α] → (g : 
A →ₐ[R] A₂) → Continuous ⇑g → C(α, A) →ₐ[R] C(α, A₂)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition on the left by a (continuous) homomorphism of topological `R`-algebr
as, as an
`AlgHom`. Similar to `AlgHom.compLeft`.
-/
protected def AlgHom.compLeftContinuous {α : Type*} [TopologicalSpace α] (g : A →ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }

variable (A)

/-- Precomposition of functions into a topological semiring by a continuous map is an algebra
homomorphism. -/
@[simps]
/-
**ContinuousMap.compRightAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.compRightAlgHom {α β : Type*} [TopologicalSpace α] [Topologi
calSpace β] (f : C(α, β)) : C(β, A) ->ₐ[R] C(α, A) where toFun g
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precomposition of functions into a topological semiring by a continuous map is a
n algebra
homomorphism.
-/
def ContinuousMap.compRightAlgHom {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A) where
  toFun g := g.comp f
  map_zero' := ext fun _ ↦ rfl
  map_add' _ _ := ext fun _ ↦ rfl
  map_one' := ext fun _ ↦ rfl
  map_mul' _ _ := ext fun _ ↦ rfl
  commutes' _ := ext fun _ ↦ rfl
/-
**ContinuousMap.compRightAlgHom_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.compRightAlgHom_continuous {α β : Type*} [TopologicalSpace α
] [TopologicalSpace β] (f : C(α, β)) : Continuous (compRightAlgHom R A f)
参数：f : C(α, β)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
-/
theorem ContinuousMap.compRightAlgHom_continuous {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : C(α, β)) : Continuous (compRightAlgHom R A f) :=
  continuous_precomp f

variable {A}

/-- Coercion to a function as an `AlgHom`. -/
@[simps!]
/-
**ContinuousMap.coeFnAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.coeFnAlgHom : C(α, A) ->ₐ[R] α -> A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function as an `AlgHom`.
-/
def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A :=
  { (ContinuousMap.coeFnRingHom : C(α, A) →+* _) with
    commutes' := fun _ => rfl }

variable {R}

/-- A version of `Set.SeparatesPoints` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
/-
**Subalgebra.SeparatesPoints** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop
参数：s : Subalgebra R C(α, A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.SeparatesPoints` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α → A)) '' (s : Set C(α, A)))
/-
**Subalgebra.separatesPoints_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.separatesPoints_monotone : Monotone fun s : Subalgebra R C(α, A
) => s.SeparatesPoints
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subalgebra.separatesPoints_monotone :
    Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints := fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]
/-
**algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • (1 : A)
参数：k : R；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable {𝕜 : Type*} [TopologicalSpace 𝕜]
variable (s : Set C(α, 𝕜)) (f : s) (x : α)

/-- A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
/-
**Set.SeparatesPointsStrongly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop
参数：s : Set C(α, 𝕜)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on
 them.

We give a slightly unusual formulation, where the specified values are given by 
some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothes
is `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous f
unctions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  ∀ (v : α → 𝕜) (x y : α), ∃ f ∈ s, (f x : 𝕜) = v x ∧ f y = v y

variable [Field 𝕜] [IsTopologicalRing 𝕜]

/-- Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
/-
**Subalgebra.SeparatesPoints.strongly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.Sepa
ratesPoints) : (s : Set C(α, 𝕜)).SeparatesPointsStrongly
参数：α, 𝕜；h : s.SeparatesPoints。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `algebraMap_apply`：algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A
) k a = k • (1 : A)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f
 x = b`.
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y => by
  by_cases n : x = y
  · subst n
    exact ⟨_, (v x • (1 : s) : s).prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y ≠ 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s :=
    ((b - a) * (f x - f y)⁻¹) • (algebraMap _ s (f x) - (⟨f, hf⟩ : s)) + algebraMap _ s a
  refine ⟨f', f'.prop, ?_, ?_⟩
  · simp [a, b, f']
  · simp [a, b, f', inv_mul_cancel_right₀ hxy]

end ContinuousMap

/-
**ContinuousMap.subsingleton_subalgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMap.subsingleton_subalgebra (α : Type*) [TopologicalSpace α] (R 
: Type*) [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Subsin
gleton α] : Subsingleton (Subalgebra R C(α, R))
参数：α : Type*；R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `algebraMap_apply`：algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A
) k a = k • (1 : A)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance ContinuousMap.subsingleton_subalgebra (α : Type*) [TopologicalSpace α] (R : Type*)
    [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Subsingleton α] :
    Subsingleton (Subalgebra R C(α, R)) :=
  ⟨fun s₁ s₂ => by
    cases isEmpty_or_nonempty α
    · have : Subsingleton C(α, R) := DFunLike.coe_injective.subsingleton
      subsingleton
    · inhabit α
      ext f
      have h : f = algebraMap R C(α, R) (f default) := by
        ext x'
        simp only [mul_one, smul_eq_mul, algebraMap_apply]
        congr
        simp [eq_iff_true_of_subsingleton]
      rw [h]
      simp only [Subalgebra.algebraMap_mem]⟩

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/

namespace ContinuousMap

variable
  {α : Type*} [TopologicalSpace α]
  {R : Type*} [Semiring R] [TopologicalSpace R]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousSMul R M]

/-
**ContinuousMap.instSMul'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：instSMul' : SMul C(α, R) C(α, M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul' : SMul C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

/-- Coercion to a function for a scalar-valued continuous map multiplying a vector-valued one
(as opposed to `ContinuousMap.coe_smul` which is multiplication by a constant scalar). -/
/-
**ContinuousMap.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {R : Type u_2} [inst_1 : Semi
ring R] [inst_2 : TopologicalSpace R]   {M : Type u_3} [inst_3 : TopologicalSpac
e M] [inst_4 : AddCommMonoid M] [inst_5 : _root_.Module R M]   [inst_6 : Continu
ousSMul R M] (f : C(α, R)) (g : C(α, M)), ⇑(f • g) = ⇑f • ⇑g
参数：f : C(α, R)；g : C(α, M)；f • g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to a function for a scalar-valued continuous map multiplying a vector-v
alued one
(as opposed to `ContinuousMap.coe_smul` which is multiplication by a constant sc
alar).
-/
@[simp] lemma coe_smul' (f : C(α, R)) (g : C(α, M)) :
    ⇑(f • g) = ⇑f • ⇑g :=
  rfl

/-- Evaluation of a scalar-valued continuous map multiplying a vector-valued one
(as opposed to `ContinuousMap.smul_apply` which is multiplication by a constant scalar). -/
-- (this doesn't need to be @[simp] since it can be derived from `coe_smul'` and `Pi.smul_apply'`)
/-
**ContinuousMap.smul_apply'** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) : (f • g) x = f x • g x
参数：f : C(α, R)；g : C(α, M)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
    (f • g) x = f x • g x :=
  rfl
/-
**ContinuousMap.module'** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
形式化陈述：module' [IsTopologicalSemiring R] [ContinuousAdd M] : Module C(α, R) C(α, 
M) where smul_add c f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' [IsTopologicalSemiring R] [ContinuousAdd M] :
    Module C(α, R) C(α, M) where
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul R (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ContinuousMap

end ModuleOverContinuousFunctions

/-! ### Evaluation as a bundled map -/

variable {X : Type*} (S R : Type*) [TopologicalSpace X] [CommSemiring S] [CommSemiring R]
variable [Algebra S R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Evaluation of continuous maps at a point, bundled as an algebra homomorphism. -/
@[simps]
/-
**ContinuousMap.evalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousMap.evalAlgHom (x : X) : C(X, R) ->ₐ[S] R where toFun f
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of continuous maps at a point, bundled as an algebra homomorphism.
-/
def ContinuousMap.evalAlgHom (x : X) : C(X, R) →ₐ[S] R where
  toFun f := f x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

section curry

namespace ContinuousMap

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_mul_apply [Mul Z] [ContinuousMul Z] (f g : C(X × Y, Z)) (x : X) : (f
 * g).curry x = f.curry x * g.curry x
参数：f g : C(X × Y, Z)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_mul_apply [Mul Z] [ContinuousMul Z] (f g : C(X × Y, Z)) (x : X) :
    (f * g).curry x = f.curry x * g.curry x :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_div_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_div_apply [Div Z] [ContinuousDiv Z] (f g : C(X × Y, Z)) (x : X) : (f
 / g).curry x = f.curry x / g.curry x
参数：f g : C(X × Y, Z)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_div_apply [Div Z] [ContinuousDiv Z] (f g : C(X × Y, Z)) (x : X) :
    (f / g).curry x = f.curry x / g.curry x :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_smul_apply {R : Type*} [SMul R Z] [ContinuousConstSMul R Z] (f : C(X
 × Y, Z)) (r : R) (x : X) : (r • f).curry x = r • f.curry x
参数：f : C(X × Y, Z)；r : R；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_smul_apply {R : Type*} [SMul R Z] [ContinuousConstSMul R Z]
    (f : C(X × Y, Z)) (r : R) (x : X) :
    (r • f).curry x = r • f.curry x :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_inv_apply [Inv Z] [ContinuousInv Z] (f : C(X × Y, Z)) (x : X) : (f⁻¹
).curry x = (f.curry x)⁻¹
参数：f : C(X × Y, Z)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_inv_apply [Inv Z] [ContinuousInv Z] (f : C(X × Y, Z)) (x : X) :
    (f⁻¹).curry x = (f.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_pow_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_pow_apply [Monoid Z] [ContinuousMul Z] (f : C(X × Y, Z)) (n : Nat) (
x : X) : (f ^ n).curry x = (f.curry x) ^ n
参数：f : C(X × Y, Z)；n : Nat；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_pow_apply [Monoid Z] [ContinuousMul Z]
    (f : C(X × Y, Z)) (n : ℕ) (x : X) :
    (f ^ n).curry x = (f.curry x) ^ n :=
  rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.curry_zpow_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：curry_zpow_apply [Group Z] [IsTopologicalGroup Z] (f : C(X × Y, Z)) (n : I
nt) (x : X) : (f ^ n).curry x = (f.curry x) ^ n
参数：f : C(X × Y, Z)；n : Int；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma curry_zpow_apply [Group Z] [IsTopologicalGroup Z]
    (f : C(X × Y, Z)) (n : ℤ) (x : X) :
    (f ^ n).curry x = (f.curry x) ^ n :=
  rfl

end ContinuousMap

end curry

