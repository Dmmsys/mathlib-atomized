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
variable {f g : { f : α -> β | Continuous f }}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun { f : α -> β | Continuous f } fun _ => α -> β
  body: ⟨Subtype.val⟩

中文:
实例 :
  签名: CoeFun { f : α -> β | Continuous f } fun _ => α -> β
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance : CoeFun { f : α -> β | Continuous f } fun _ => α -> β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-! ### `mul` and `add` -/

@[to_additive]
/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul β] [ContinuousMul β]
  body: ⟨fun f g => ⟨f * g, continuous_mul.comp (f.continuous.prodMk g.continuous :)⟩⟩

@[to_additive (attr := norm_cast, simp)]

中文:
实例 instMul
  签名: [Mul β] [ContinuousMul β]
  定义体: ⟨fun f g => ⟨f * g, continuous_mul.comp (f.continuous.prodMk g.continuous :)⟩⟩

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: continuous, continuous_mul, continuous_mul.comp, f.continuous.prodMk, g.continuous, prodMk
-/
instance instMul [Mul β] [ContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.continuous.prodMk g.continuous :)⟩⟩

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul β] [ContinuousMul β] (f g : C(α, β))
  statement: ⇑(f * g) = f * g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mul
  条件: [Mul β] [ContinuousMul β] (f g : C(α, β))
  结论: ⇑(f * g) = f * g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α)
  statement: (f * g) x = f x * g x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mul_apply
  条件: [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α)
  结论: (f * g) x = f x * g x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mul_comp` / 定理 `mul_comp`

English:
theorem mul_comp
  given: [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β))
  proof: rfl

中文:
定理 mul_comp
  条件: [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β))
  证明: rfl
-/
theorem mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl

/-! ### `one` -/

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: β] : One C(α, β)
  body: ⟨const α 1⟩

@[to_additive (attr := norm_cast, simp)]

中文:
实例 [One
  签名: β] : One C(α, β)
  定义体: ⟨const α 1⟩

@[to_additive (attr := norm_cast, simp)]
-/
instance [One β] : One C(α, β) :=
  ⟨const α 1⟩

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: [One β]
  statement: ⇑(1 : C(α, β)) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_one
  条件: [One β]
  结论: ⇑(1 : C(α, β)) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_one [One β] : ⇑(1 : C(α, β)) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: [One β] (x : α)
  statement: (1 : C(α, β)) x = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 one_apply
  条件: [One β] (x : α)
  结论: (1 : C(α, β)) x = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `one_comp` / 定理 `one_comp`

English:
theorem one_comp
  given: [One γ] (g : C(α, β))
  statement: (1 : C(β, γ)).comp g = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 one_comp
  条件: [One γ] (g : C(α, β))
  结论: (1 : C(β, γ)).comp g = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `comp_one` / 定理 `comp_one`

English:
theorem comp_one
  given: [One β] (g : C(β, γ))
  statement: g.comp (1 : C(α, β)) = const α (g 1)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_one
  条件: [One β] (g : C(β, γ))
  结论: g.comp (1 : C(α, β)) = const α (g 1)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_one [One β] (g : C(β, γ)) : g.comp (1 : C(α, β)) = const α (g 1) := rfl

@[to_additive (attr := simp)]
/--
theorem `const_one` / 定理 `const_one`

English:
theorem const_one
  given: [One β]
  statement: const α (1 : β) = 1
  proof: rfl

中文:
定理 const_one
  条件: [One β]
  结论: const α (1 : β) = 1
  证明: rfl
-/
theorem const_one [One β] : const α (1 : β) = 1 := rfl


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NatCast
  signature: β] : NatCast C(α, β)
  body: ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]

中文:
实例 [NatCast
  签名: β] : 自然数Cast C(α, β)
  定义体: ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
instance [NatCast β] : NatCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: [NatCast β] (n : Nat)
  statement: ((n : C(α, β)) : α -> β) = n
  proof: rfl

@[simp]

中文:
定理 coe_natCast
  条件: [自然数Cast β] (n : 自然数)
  结论: ((n : C(α, β)) : α -> β) = n
  证明: rfl

@[simp]
-/
theorem coe_natCast [NatCast β] (n : Nat) : ((n : C(α, β)) : α -> β) = n :=
  rfl

@[simp]
/--
theorem `natCast_apply` / 定理 `natCast_apply`

English:
theorem natCast_apply
  given: [NatCast β] (n : Nat) (x : α)
  statement: (n : C(α, β)) x = n
  proof: rfl

中文:
定理 natCast_apply
  条件: [自然数Cast β] (n : 自然数) (x : α)
  结论: (n : C(α, β)) x = n
  证明: rfl
-/
theorem natCast_apply [NatCast β] (n : Nat) (x : α) : (n : C(α, β)) x = n :=
  rfl


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IntCast
  signature: β] : IntCast C(α, β)
  body: ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]

中文:
实例 [IntCast
  签名: β] : 整数Cast C(α, β)
  定义体: ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
instance [IntCast β] : IntCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: [IntCast β] (n : Int)
  statement: ((n : C(α, β)) : α -> β) = n
  proof: rfl

@[simp]

中文:
定理 coe_intCast
  条件: [整数Cast β] (n : 整数)
  结论: ((n : C(α, β)) : α -> β) = n
  证明: rfl

@[simp]
-/
theorem coe_intCast [IntCast β] (n : Int) : ((n : C(α, β)) : α -> β) = n :=
  rfl

@[simp]
/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: [IntCast β] (n : Int) (x : α)
  statement: (n : C(α, β)) x = n
  proof: rfl

中文:
定理 intCast_apply
  条件: [整数Cast β] (n : 整数) (x : α)
  结论: (n : C(α, β)) x = n
  证明: rfl
-/
theorem intCast_apply [IntCast β] (n : Int) (x : α) : (n : C(α, β)) x = n :=
  rfl

/-! ### `nsmul` and `pow` -/

@[to_additive]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: [Monoid β] [ContinuousMul β]
  body: ⟨fun f n => ⟨(⇑f) ^ n, f.continuous.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]

中文:
实例 instPow
  签名: [Monoid β] [ContinuousMul β]
  定义体: ⟨fun f n => ⟨(⇑f) ^ n, f.continuous.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]

Depends on / 依赖: continuous, f.continuous.pow
-/
instance instPow [Monoid β] [ContinuousMul β] : Pow C(α, β) Nat :=
  ⟨fun f n => ⟨(⇑f) ^ n, f.continuous.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat)
  statement: ⇑(f ^ n) = (⇑f) ^ n
  proof: rfl

@[to_additive (attr := norm_cast)]

中文:
定理 coe_pow
  条件: [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : 自然数)
  结论: ⇑(f ^ n) = (⇑f) ^ n
  证明: rfl

@[to_additive (attr := norm_cast)]
-/
theorem coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat) (x : α)
  proof: rfl

中文:
定理 pow_apply
  条件: [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : 自然数) (x : α)
  证明: rfl
-/
theorem pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : Nat) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl

-- Don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_pow pow_apply

@[to_additive]
/--
theorem `pow_comp` / 定理 `pow_comp`

English:
theorem pow_comp
  given: [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : Nat) (g : C(α, β))
  proof: rfl

中文:
定理 pow_comp
  条件: [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : 自然数) (g : C(α, β))
  证明: rfl
-/
theorem pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : Nat) (g : C(α, β)) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl

-- Don't make `nsmul_comp` simp as the linter complains it's redundant w.r.t. `smul_comp`
attribute [simp] pow_comp

/-! ### `inv` and `neg` -/

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: β] [ContinuousInv β] : Inv C(α, β) where inv f
  body: ⟨f⁻¹, f.continuous.inv⟩

@[to_additive (attr := simp)]

中文:
实例 [Inv
  签名: β] [ContinuousInv β] : Inv C(α, β) where inv f
  定义体: ⟨f⁻¹, f.continuous.inv⟩

@[to_additive (attr := simp)]

Depends on / 依赖: continuous, f.continuous.inv
-/
instance [Inv β] [ContinuousInv β] : Inv C(α, β) where inv f := ⟨f⁻¹, f.continuous.inv⟩

@[to_additive (attr := simp)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv β] [ContinuousInv β] (f : C(α, β))
  statement: ⇑f⁻¹ = (⇑f)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_inv
  条件: [Inv β] [ContinuousInv β] (f : C(α, β))
  结论: ⇑f⁻¹ = (⇑f)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_inv [Inv β] [ContinuousInv β] (f : C(α, β)) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α)
  statement: f⁻¹ x = (f x)⁻¹
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 inv_apply
  条件: [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α)
  结论: f⁻¹ x = (f x)⁻¹
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem inv_apply [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `inv_comp` / 定理 `inv_comp`

English:
theorem inv_comp
  given: [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β))
  proof: rfl

中文:
定理 inv_comp
  条件: [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β))
  证明: rfl
-/
theorem inv_comp [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β)) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl

/-! ### `div` and `sub` -/

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: β] [ContinuousDiv β] : Div C(α, β) where
  body: ⟨f / g, f.continuous.div' g.continuous⟩

@[to_additive (attr := norm_cast, simp)]

中文:
实例 [Div
  签名: β] [ContinuousDiv β] : Div C(α, β) where
  定义体: ⟨f / g, f.continuous.div' g.continuous⟩

@[to_additive (attr := norm_cast, simp)]

Depends on / 依赖: continuous, f.continuous.div, g.continuous
-/
instance [Div β] [ContinuousDiv β] : Div C(α, β) where
  div f g := ⟨f / g, f.continuous.div' g.continuous⟩

@[to_additive (attr := norm_cast, simp)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: [Div β] [ContinuousDiv β] (f g : C(α, β))
  statement: ⇑(f / g) = f / g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_div
  条件: [Div β] [ContinuousDiv β] (f g : C(α, β))
  结论: ⇑(f / g) = f / g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `div_apply` / 定理 `div_apply`

English:
theorem div_apply
  given: [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α)
  statement: (f / g) x = f x / g x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 div_apply
  条件: [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α)
  结论: (f / g) x = f x / g x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `div_comp` / 定理 `div_comp`

English:
theorem div_comp
  given: [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β))
  proof: rfl

中文:
定理 div_comp
  条件: [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β))
  证明: rfl
-/
theorem div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl

/-! ### `zpow` and `zsmul` -/

@[to_additive]
/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: [Group β] [IsTopologicalGroup β]
  body: ⟨(⇑f) ^ z, f.continuous.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]

中文:
实例 instZPow
  签名: [Group β] [IsTopologicalGroup β]
  定义体: ⟨(⇑f) ^ z, f.continuous.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]

Depends on / 依赖: continuous, f.continuous.zpow
-/
instance instZPow [Group β] [IsTopologicalGroup β] : Pow C(α, β) Int where
  pow f z := ⟨(⇑f) ^ z, f.continuous.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
/--
theorem `coe_zpow` / 定理 `coe_zpow`

English:
theorem coe_zpow
  given: [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int)
  statement: ⇑(f ^ z) = (⇑f) ^ z
  proof: rfl

@[to_additive]

中文:
定理 coe_zpow
  条件: [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : 整数)
  结论: ⇑(f ^ z) = (⇑f) ^ z
  证明: rfl

@[to_additive]
-/
theorem coe_zpow [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

@[to_additive]
/--
theorem `zpow_apply` / 定理 `zpow_apply`

English:
theorem zpow_apply
  given: [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int) (x : α)
  proof: rfl

中文:
定理 zpow_apply
  条件: [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : 整数) (x : α)
  证明: rfl
-/
theorem zpow_apply [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : Int) (x : α) :
    (f ^ z) x = f x ^ z :=
  rfl

-- Don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_zpow zpow_apply

@[to_additive]
/--
theorem `zpow_comp` / 定理 `zpow_comp`

English:
theorem zpow_comp
  given: [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : Int) (g : C(α, β))
  proof: rfl

中文:
定理 zpow_comp
  条件: [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : 整数) (g : C(α, β))
  证明: rfl
-/
theorem zpow_comp [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : Int) (g : C(α, β)) :
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
/--
Definition of `continuousSubmonoid` / `continuousSubmonoid` 的定义

English:
definition continuousSubmonoid
  signature: (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
  body: { f : α -> β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc

中文:
定义 continuousSubmonoid
  签名: (α : 类型) (β : 类型) [TopologicalSpace α] [TopologicalSpace β]
  定义体: { f : α -> β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc

Depends on / 依赖: Continuous
-/
def continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α -> β) where
  carrier := { f : α -> β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubgroup` of continuous maps `α → β`. -/]
/--
Definition of `continuousSubgroup` / `continuousSubgroup` 的定义

English:
definition continuousSubgroup
  signature: (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
  body: { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

中文:
定义 continuousSubgroup
  签名: (α : 类型) (β : 类型) [TopologicalSpace α] [TopologicalSpace β] [Group β]
  定义体: { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

Depends on / 依赖: Continuous, Continuous.inv, continuousSubmonoid, inv_mem
-/
def continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [IsTopologicalGroup β] : Subgroup (α -> β) :=
  { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: β] [ContinuousMul β] : Semigroup C(α, β)
  body: fast_instance%
  coe_injective.semigroup _ coe_mul

@[to_additive]

中文:
实例 [Semigroup
  签名: β] [ContinuousMul β] : Semigroup C(α, β)
  定义体: fast_instance%
  coe_injective.semigroup _ coe_mul

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [Semigroup β] [ContinuousMul β] : Semigroup C(α, β) := fast_instance%
  coe_injective.semigroup _ coe_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: β] [ContinuousMul β] : CommSemigroup C(α, β)
  body: fast_instance%
  coe_injective.commSemigroup _ coe_mul

@[to_additive]

中文:
实例 [CommSemigroup
  签名: β] [ContinuousMul β] : CommSemigroup C(α, β)
  定义体: fast_instance%
  coe_injective.commSemigroup _ coe_mul

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [CommSemigroup β] [ContinuousMul β] : CommSemigroup C(α, β) := fast_instance%
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: β] [ContinuousMul β] : MulOneClass C(α, β)
  body: fast_instance%
  coe_injective.mulOneClass _ coe_one coe_mul

中文:
实例 [MulOneClass
  签名: β] [ContinuousMul β] : MulOneClass C(α, β)
  定义体: fast_instance%
  coe_injective.mulOneClass _ coe_one coe_mul

Depends on / 依赖: fast_instance
-/
instance [MulOneClass β] [ContinuousMul β] : MulOneClass C(α, β) := fast_instance%
  coe_injective.mulOneClass _ coe_one coe_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroClass
  signature: β] [ContinuousMul β] : MulZeroClass C(α, β)
  body: fast_instance%
  coe_injective.mulZeroClass _ coe_zero coe_mul

中文:
实例 [MulZeroClass
  签名: β] [ContinuousMul β] : MulZeroClass C(α, β)
  定义体: fast_instance%
  coe_injective.mulZeroClass _ coe_zero coe_mul

Depends on / 依赖: fast_instance
-/
instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C(α, β) := fast_instance%
  coe_injective.mulZeroClass _ coe_zero coe_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemigroupWithZero
  signature: β] [ContinuousMul β] : SemigroupWithZero C(α, β)
  body: fast_instance%
  coe_injective.semigroupWithZero _ coe_zero coe_mul

@[to_additive]

中文:
实例 [SemigroupWithZero
  签名: β] [ContinuousMul β] : SemigroupWithZero C(α, β)
  定义体: fast_instance%
  coe_injective.semigroupWithZero _ coe_zero coe_mul

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C(α, β) := fast_instance%
  coe_injective.semigroupWithZero _ coe_zero coe_mul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] [ContinuousMul β] : Monoid C(α, β)
  body: fast_instance%
  coe_injective.monoid _ coe_one coe_mul coe_pow

中文:
实例 [Monoid
  签名: β] [ContinuousMul β] : Monoid C(α, β)
  定义体: fast_instance%
  coe_injective.monoid _ coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance [Monoid β] [ContinuousMul β] : Monoid C(α, β) := fast_instance%
  coe_injective.monoid _ coe_one coe_mul coe_pow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: β] [ContinuousMul β] : MonoidWithZero C(α, β)
  body: fast_instance%
  coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]

中文:
实例 [MonoidWithZero
  签名: β] [ContinuousMul β] : MonoidWithZero C(α, β)
  定义体: fast_instance%
  coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [MonoidWithZero β] [ContinuousMul β] : MonoidWithZero C(α, β) := fast_instance%
  coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: β] [ContinuousMul β] : CommMonoid C(α, β)
  body: fast_instance%
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

中文:
实例 [CommMonoid
  签名: β] [ContinuousMul β] : CommMonoid C(α, β)
  定义体: fast_instance%
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

Depends on / 依赖: fast_instance
-/
instance [CommMonoid β] [ContinuousMul β] : CommMonoid C(α, β) := fast_instance%
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoidWithZero
  signature: β] [ContinuousMul β] : CommMonoidWithZero C(α, β)
  body: fast_instance%
  coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]

中文:
实例 [CommMonoidWithZero
  签名: β] [ContinuousMul β] : CommMonoidWithZero C(α, β)
  定义体: fast_instance%
  coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [CommMonoidWithZero β] [ContinuousMul β] : CommMonoidWithZero C(α, β) := fast_instance%
  coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyCompactSpace
  signature: α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β)
  body: ⟨by
    refine continuous_of_continuous_uncurry _ ?_
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval.comp (continuous_fst.prodMap continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval.c

中文:
实例 [LocallyCompactSpace
  签名: α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β)
  定义体: ⟨by
    refine continuous_of_continuous_uncurry _ ?_
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval.comp (continuous_fst.prodMap continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval.c

Depends on / 依赖: Continuous, continuous_eval, continuous_eval.comp, continuous_fst, continuous_fst.prodMap, continuous_id, continuous_of_continuous_uncurry, continuous_snd, continuous_snd.prodMap, h1.mul, prodMap, x.fst.fst, x.fst.snd, x.snd
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
/--
Definition of `coeFnMonoidHom` / `coeFnMonoidHom` 的定义

English:
definition coeFnMonoidHom
  signature: [Monoid β] [ContinuousMul β]
  body: f
  map_one' := coe_one
  map_mul' := coe_mul

中文:
定义 coeFnMonoidHom
  签名: [Monoid β] [ContinuousMul β]
  定义体: f
  map_one' := coe_one
  map_mul' := coe_mul
-/
def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) ->* α -> β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

variable (α) in
/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeft`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (continuous) homomorphism of topological `AddMonoid`s, as an
`AddMonoidHom`. Similar to `AddMonoidHom.comp_left`. -/]
/--
Definition of `_root_.MonoidHom.compLeftContinuous` / `_root_.MonoidHom.compLeftContinuous` 的定义

English:
definition _root_.MonoidHom.compLeftContinuous
  signature: {γ : Type*} [Monoid β] [ContinuousMul β]
  body: (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

中文:
定义 _root_.MonoidHom.compLeftContinuous
  签名: {γ : 类型} [Monoid β] [ContinuousMul β]
  定义体: (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _
-/
protected def _root_.MonoidHom.compLeftContinuous {γ : Type*} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β ->* γ) (hg : Continuous g) :
    C(α, β) ->* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

/-- Composition on the right as a `MonoidHom`. Similar to `MonoidHom.compHom'`. -/
@[to_additive (attr := simps)
      /-- Composition on the right as an `AddMonoidHom`. Similar to `AddMonoidHom.compHom'`. -/]
/--
Definition of `compMonoidHom'` / `compMonoidHom'` 的定义

English:
definition compMonoidHom'
  signature: {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
  body: f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g

@[to_additive (attr := simp)]

中文:
定义 compMonoidHom'
  签名: {γ : 类型} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
  定义体: f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g

@[to_additive (attr := simp)]

Depends on / 依赖: f.comp
-/
def compMonoidHom' {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) ->* C(α, γ) where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g

@[to_additive (attr := simp)]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι -> C(α, β))
  proof: map_prod coeFnMonoidHom f s

@[to_additive]

中文:
定理 coe_prod
  条件: [CommMonoid β] [ContinuousMul β] {ι : 类型} (s : Finset ι) (f : ι -> C(α, β))
  证明: map_prod coeFnMonoidHom f s

@[to_additive]

Depends on / 依赖: coeFnMonoidHom, map_prod
-/
theorem coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι -> C(α, β)) :
    ⇑(∏ i in s, f i) = ∏ i in s, (f i : α -> β) :=
  map_prod coeFnMonoidHom f s

@[to_additive]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  statement: [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι -> C(α, β))
  proof: by simp

@[to_additive]

中文:
定理 prod_apply
  结论: [CommMonoid β] [ContinuousMul β] {ι : 类型} (s : Finset ι) (f : ι -> C(α, β))
  证明: by simp

@[to_additive]
-/
theorem prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι -> C(α, β))
    (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a := by simp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: β] [IsTopologicalGroup β] : Group C(α, β)
  body: fast_instance%
  coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]

中文:
实例 [Group
  签名: β] [IsTopologicalGroup β] : Group C(α, β)
  定义体: fast_instance%
  coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance [Group β] [IsTopologicalGroup β] : Group C(α, β) := fast_instance%
  coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
/--
Instance `instCommGroupContinuousMap` / 实例 `instCommGroupContinuousMap`

English:
instance instCommGroupContinuousMap
  signature: [CommGroup β] [IsTopologicalGroup β]
  body: fast_instance%
  coe_injective.commGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]

中文:
实例 instCommGroupContinuousMap
  签名: [CommGroup β] [IsTopologicalGroup β]
  定义体: fast_instance%
  coe_injective.commGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]

Depends on / 依赖: fast_instance
-/
instance instCommGroupContinuousMap [CommGroup β] [IsTopologicalGroup β] :
    CommGroup C(α, β) := fast_instance%
  coe_injective.commGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: β] [IsTopologicalGroup β] : IsTopologicalGroup C(α, β) where
  body: by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt]; rw [tendsto_iff_forall_isCompact_tendstoUniformlyOn]; rw [nhds_prod_eq]
    exact fun K hK =>

中文:
实例 [CommGroup
  签名: β] [IsTopologicalGroup β] : IsTopologicalGroup C(α, β) where
  定义体: by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt]; rw [tendsto_iff_forall_isCompact_tendstoUniformlyOn]; rw [nhds_prod_eq]
    exact fun K hK =>

Depends on / 依赖: ContinuousAt, Filter, Filter.tendsto_id, IsTopologicalGroup, IsTopologicalGroup.rightUniformSpace, IsUniformGroup, UniformSpace, comp_tendstoUniformlyOn, continuous_iff_continuousAt, continuous_inv, isUniformGroup_of_commGroup, nhds_prod_eq, prodMk, rightUniformSpace, tendsto_id, tendsto_iff_forall_isCompact_tendstoUniformlyOn, tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp, uniformContinuous_mul, uniformContinuous_mul.comp_tendstoUniformlyOn
-/
instance [CommGroup β] [IsTopologicalGroup β] : IsTopologicalGroup C(α, β) where
  continuous_mul := by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt]; rw [tendsto_iff_forall_isCompact_tendstoUniformlyOn]; rw [nhds_prod_eq]
    exact fun K hK =>
      uniformContinuous_mul.comp_tendstoUniformlyOn
        ((tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK).prodMk
          (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK))
  continuous_inv := by
    let : UniformSpace β := IsTopologicalGroup.rightUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt]; rw [tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    exact fun K hK =>
      uniformContinuous_inv.comp_tendstoUniformlyOn
        (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK)

/-- If an infinite product of functions in `C(α, β)` converges to `g`
(for the compact-open topology), then the pointwise product converges to `g x` for all `x ∈ α`. -/
@[to_additive
  /-- If an infinite sum of functions in `C(α, β)` converges to `g` (for the compact-open topology),
then the pointwise sum converges to `g x` for all `x ∈ α`. -/]
/--
theorem `hasProd_apply` / 定理 `hasProd_apply`

English:
theorem hasProd_apply
  statement: {γ : Type*} [CommMonoid β] [ContinuousMul β]
  proof: by
  let ev : C(α, β) ->* β := (Pi.evalMonoidHom _ x).comp coeFnMonoidHom
  exact hf.map ev (continuous_eval_const x)

@[to_additive]

中文:
定理 hasProd_apply
  结论: {γ : 类型} [CommMonoid β] [ContinuousMul β]
  证明: by
  let ev : C(α, β) ->* β := (Pi.evalMonoidHom _ x).comp coeFnMonoidHom
  exact hf.map ev (continuous_eval_const x)

@[to_additive]

Depends on / 依赖: Pi.evalMonoidHom, coeFnMonoidHom, continuous_eval_const, evalMonoidHom, hf.map
-/
theorem hasProd_apply {γ : Type*} [CommMonoid β] [ContinuousMul β]
    {f : γ -> C(α, β)} {g : C(α, β)} {L : SummationFilter γ} (hf : HasProd f g L) (x : α) :
    HasProd (fun i : γ => f i x) (g x) L := by
  let ev : C(α, β) ->* β := (Pi.evalMonoidHom _ x).comp coeFnMonoidHom
  exact hf.map ev (continuous_eval_const x)

@[to_additive]
/--
theorem `multipliable_apply` / 定理 `multipliable_apply`

English:
theorem multipliable_apply
  statement: [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ -> C(α, β)}
  proof: (hasProd_apply hf.hasProd x).multipliable

@[to_additive]

中文:
定理 multipliable_apply
  结论: [CommMonoid β] [ContinuousMul β] {γ : 类型} {f : γ -> C(α, β)}
  证明: (hasProd_apply hf.hasProd x).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hasProd_apply, hf.hasProd, multipliable
-/
theorem multipliable_apply [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ -> C(α, β)}
    {L : SummationFilter γ} (hf : Multipliable f L) (x : α) : Multipliable (fun i : γ => f i x) L :=
  (hasProd_apply hf.hasProd x).multipliable

@[to_additive]
/--
theorem `tprod_apply` / 定理 `tprod_apply`

English:
theorem tprod_apply
  statement: [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ -> C(α, β)}
  proof: (hasProd_apply hf.hasProd x).tprod_eq

中文:
定理 tprod_apply
  结论: [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : 类型} {f : γ -> C(α, β)}
  证明: (hasProd_apply hf.hasProd x).tprod_eq

Depends on / 依赖: hasProd, hasProd_apply, hf.hasProd, tprod_eq
-/
theorem tprod_apply [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ -> C(α, β)}
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

/--
Definition of `continuousSubsemiring` / `continuousSubsemiring` 的定义

English:
definition continuousSubsemiring
  signature: (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
  body: { continuousAddSubmonoid α R, continuousSubmonoid α R with }

中文:
定义 continuousSubsemiring
  签名: (α : 类型) (R : 类型) [TopologicalSpace α] [TopologicalSpace R]
  定义体: { continuousAddSubmonoid α R, continuousSubmonoid α R with }

Depends on / 依赖: continuousAddSubmonoid, continuousSubmonoid
-/
def continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [IsTopologicalSemiring R] : Subsemiring (α -> R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }

/--
Definition of `continuousSubring` / `continuousSubring` 的定义

English:
definition continuousSubring
  signature: (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
  body: { continuousAddSubgroup α R, continuousSubsemiring α R with }

中文:
定义 continuousSubring
  签名: (α : 类型) (R : 类型) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
  定义体: { continuousAddSubgroup α R, continuousSubsemiring α R with }

Depends on / 依赖: continuousAddSubgroup, continuousSubsemiring
-/
def continuousSubring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] : Subring (α -> R) :=
  { continuousAddSubgroup α R, continuousSubsemiring α R with }

end Subtype

namespace ContinuousMap

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] : NonUnitalNonAssocSemiring C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalSemiring β]
    [IsTopologicalSemiring β] : NonUnitalSemiring C(α, β) := fast_instance%
  coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [AddMonoidWithOne β]
    [ContinuousAdd β] : AddMonoidWithOne C(α, β) := fast_instance%
  coe_injective.addMonoidWithOne _ coe_zero coe_one coe_add coe_nsmul coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocSemiring β]
    [IsTopologicalSemiring β] : NonAssocSemiring C(α, β) := fast_instance%
  coe_injective.nonAssocSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : Semiring C(α, β) := fast_instance%
  coe_injective.semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocRing β] [IsTopologicalRing β] : NonUnitalNonAssocRing C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalRing β]
    [IsTopologicalRing β] : NonUnitalRing C(α, β) := fast_instance%
  coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocRing β]
    [IsTopologicalRing β] : NonAssocRing C(α, β) := fast_instance%
  coe_injective.nonAssocRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_natCast coe_intCast

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
  body: fast_instance%
  coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_natCast coe_intCast

中文:
实例 instRing
  签名: {α : 类型} {β : 类型} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
  定义体: fast_instance%
  coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_natCast coe_intCast

Depends on / 依赖: fast_instance
-/
instance instRing {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
    [IsTopologicalRing β] : Ring C(α, β) := fast_instance%
  coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_natCast coe_intCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalCommSemiring β] [IsTopologicalSemiring β] : NonUnitalCommSemiring C(α, β) :=
  fast_instance%
  coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommSemiring β]
    [IsTopologicalSemiring β] : CommSemiring C(α, β) := fast_instance%
  coe_injective.commSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalCommRing β]
    [IsTopologicalRing β] : NonUnitalCommRing C(α, β) := fast_instance%
  coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommRing β]
    [IsTopologicalRing β] : CommRing C(α, β) := fast_instance%
  coe_injective.commRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_pow coe_natCast coe_intCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalSemiring β] [IsTopologicalSemiring β] : IsTopologicalSemiring C(α, β) where

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalRing β] [IsTopologicalRing β] : IsTopologicalRing C(α, β) where

/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`RingHom`. Similar to `RingHom.compLeft`. -/
@[simps!]
/--
Definition of `_root_.RingHom.compLeftContinuous` / `_root_.RingHom.compLeftContinuous` 的定义

English:
definition _root_.RingHom.compLeftContinuous
  signature: (α : Type*) {β : Type*} {γ : Type*}
  body: { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }

中文:
定义 _root_.RingHom.compLeftContinuous
  签名: (α : 类型) {β : 类型} {γ : 类型}
  定义体: { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }
-/
protected def _root_.RingHom.compLeftContinuous (α : Type*) {β : Type*} {γ : Type*}
    [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [IsTopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [IsTopologicalSemiring γ] (g : β ->+* γ) (hg : Continuous g) : C(α, β) ->+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }

/-- Coercion to a function as a `RingHom`. -/
@[simps!]
/--
Definition of `coeFnRingHom` / `coeFnRingHom` 的定义

English:
definition coeFnRingHom
  signature: {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
  body: { (coeFnMonoidHom : C(α, β) ->* _),
    (coeFnAddMonoidHom : C(α, β) ->+ _) with }

中文:
定义 coeFnRingHom
  签名: {α : 类型} {β : 类型} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
  定义体: { (coeFnMonoidHom : C(α, β) ->* _),
    (coeFnAddMonoidHom : C(α, β) ->+ _) with }

Depends on / 依赖: coeFnAddMonoidHom, coeFnMonoidHom
-/
def coeFnRingHom {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : C(α, β) ->+* α -> β :=
  { (coeFnMonoidHom : C(α, β) ->* _),
    (coeFnAddMonoidHom : C(α, β) ->+ _) with }

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

/--
Definition of `continuousSubmodule` / `continuousSubmodule` 的定义

English:
definition continuousSubmodule
  signature: : Submodule R (α -> M)
  body: { continuousAddSubgroup α M with
    carrier := { f : α -> M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }

中文:
定义 continuousSubmodule
  签名: : Submodule R (α -> M)
  定义体: { continuousAddSubgroup α M with
    carrier := { f : α -> M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }

Depends on / 依赖: Continuous, carrier, const_smul, continuousAddSubgroup, hf.const_smul, smul_mem
-/
def continuousSubmodule : Submodule R (α -> M) :=
  { continuousAddSubgroup α M with
    carrier := { f : α -> M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type*} {M : Type*}
  [TopologicalSpace M] {M₂ : Type*} [TopologicalSpace M₂]

@[to_additive]
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul R M] [ContinuousConstSMul R M]
  body: ⟨fun r f => ⟨r • ⇑f, f.continuous.const_smul r⟩⟩

@[to_additive]

中文:
实例 instSMul
  签名: [SMul R M] [ContinuousConstSMul R M]
  定义体: ⟨fun r f => ⟨r • ⇑f, f.continuous.const_smul r⟩⟩

@[to_additive]

Depends on / 依赖: const_smul, continuous, f.continuous.const_smul
-/
instance instSMul [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M) :=
  ⟨fun r f => ⟨r • ⇑f, f.continuous.const_smul r⟩⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] : ContinuousConstSMul R C(α, M) where
  body: continuous_postcomp ⟨_, continuous_const_smul r⟩

@[to_additive]

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] : ContinuousConstSMul R C(α, M) where
  定义体: continuous_postcomp ⟨_, continuous_const_smul r⟩

@[to_additive]

Depends on / 依赖: continuous_const_smul, continuous_postcomp
-/
instance [SMul R M] [ContinuousConstSMul R M] : ContinuousConstSMul R C(α, M) where
  continuous_const_smul r := continuous_postcomp ⟨_, continuous_const_smul r⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] [SMul R M] [ContinuousSMul R M] :
  body: ⟨(continuous_postcomp ⟨_, continuous_smul⟩).comp continuous_prodMk_const⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 [TopologicalSpace
  签名: R] [SMul R M] [ContinuousSMul R M] :
  定义体: ⟨(continuous_postcomp ⟨_, continuous_smul⟩).comp continuous_prodMk_const⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: continuous_postcomp, continuous_prodMk_const, continuous_smul
-/
instance [TopologicalSpace R] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R C(α, M) :=
  ⟨(continuous_postcomp ⟨_, continuous_smul⟩).comp continuous_prodMk_const⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M))
  statement: ⇑(c • f) = c • ⇑f
  proof: rfl

@[to_additive]

中文:
定理 coe_smul
  条件: [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M))
  结论: ⇑(c • f) = c • ⇑f
  证明: rfl

@[to_additive]
-/
theorem coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_apply
  条件: [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
    (c • f) a = c • f a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β))
  proof: rfl

@[to_additive]

中文:
定理 smul_comp
  条件: [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β))
  证明: rfl

@[to_additive]
-/
theorem smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
  body: ext fun _ => smul_comm _ _ _

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
  定义体: ext fun _ => smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
    [SMulCommClass R R₁ M] : SMulCommClass R R₁ C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [SMul
  签名: R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [IsScalarTower R M M] :
  body: ext fun _ => smul_mul_assoc ..

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [IsScalarTower R M M] :
  定义体: ext fun _ => smul_mul_assoc ..

Depends on / 依赖: smul_mul_assoc
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [IsScalarTower R M M] :
    IsScalarTower R C(α, M) C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_mul_assoc ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass R M M] :
  body: ext fun _ => (mul_smul_comm ..).symm

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass R M M] :
  定义体: ext fun _ => (mul_smul_comm ..).symm

Depends on / 依赖: mul_smul_comm
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass R M M] :
    SMulCommClass R C(α, M) C(α, M) where
  smul_comm _ _ _ := ext fun _ => (mul_smul_comm ..).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass M R M] :
  body: ext fun _ => smul_comm (_ : M) ..

中文:
实例 [SMul
  签名: R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass M R M] :
  定义体: ext fun _ => smul_comm (_ : M) ..

Depends on / 依赖: smul_comm
-/
instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass M R M] :
    SMulCommClass C(α, M) R C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm (_ : M) ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M)
  body: fast_instance% Function.Injective.mulAction _ coe_injective coe_smul

中文:
实例 [Monoid
  签名: R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M)
  定义体: fast_instance% Function.Injective.mulAction _ coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.mulAction, Injective, coe_injective, coe_smul, fast_instance, mulAction
-/
instance [Monoid R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M) :=
  fast_instance% Function.Injective.mulAction _ coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
  body: fast_instance%
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

中文:
实例 [Monoid
  签名: R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
  定义体: fast_instance%
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
    [ContinuousConstSMul R M] : DistribMulAction R C(α, M) := fast_instance%
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [ContinuousAdd M] [Module R M] [ContinuousConstSMul R M]
variable [ContinuousAdd M₂] [Module R M₂] [ContinuousConstSMul R M₂]

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module R C(α, M)
  body: fast_instance%
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

中文:
实例 module
  签名: : Module R C(α, M)
  定义体: fast_instance%
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

Depends on / 依赖: fast_instance
-/
instance module : Module R C(α, M) := fast_instance%
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul

variable (R)

/-- Composition on the left by a continuous linear map, as a `ContinuousLinearMap`.
Similar to `LinearMap.compLeft`. -/
@[simps]
/--
Definition of `_root_.ContinuousLinearMap.compLeftContinuous` / `_root_.ContinuousLinearMap.compLeftContinuous` 的定义

English:
definition _root_.ContinuousLinearMap.compLeftContinuous
  signature: (α : Type*) [TopologicalSpace α]
  body: g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous
  map_smul' := fun c _ => ext fun _ => g.map_smul' c _

中文:
定义 _root_.ContinuousLinearMap.compLeftContinuous
  签名: (α : 类型) [TopologicalSpace α]
  定义体: g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous
  map_smul' := fun c _ => ext fun _ => g.map_smul' c _
-/
protected def _root_.ContinuousLinearMap.compLeftContinuous (α : Type*) [TopologicalSpace α]
    (g : M ->L[R] M₂) : C(α, M) ->L[R] C(α, M₂) where
  __ := g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous
  map_smul' := fun c _ => ext fun _ => g.map_smul' c _

/-- The constant map `x ↦ y ↦ x` as a `ContinuousLinearMap`. -/
@[simps!]
/--
Definition of `_root_.ContinuousLinearMap.const` / `_root_.ContinuousLinearMap.const` 的定义

English:
definition _root_.ContinuousLinearMap.const
  signature: (α : Type*) [TopologicalSpace α]
  body: .const α m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 _root_.ContinuousLinearMap.const
  签名: (α : 类型) [TopologicalSpace α]
  定义体: .const α m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def _root_.ContinuousLinearMap.const (α : Type*) [TopologicalSpace α] : M ->L[R] C(α, M) where
  toFun m := .const α m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
/--
Definition of `coeFnLinearMap` / `coeFnLinearMap` 的定义

English:
definition coeFnLinearMap
  signature: : C(α, M) ->ₗ[R] α -> M
  body: { (coeFnAddMonoidHom : C(α, M) ->+ _) with
    map_smul' := coe_smul }

中文:
定义 coeFnLinearMap
  签名: : C(α, M) ->ₗ[R] α -> M
  定义体: { (coeFnAddMonoidHom : C(α, M) ->+ _) with
    map_smul' := coe_smul }

Depends on / 依赖: coeFnAddMonoidHom, coe_smul, map_smul
-/
def coeFnLinearMap : C(α, M) ->ₗ[R] α -> M :=
  { (coeFnAddMonoidHom : C(α, M) ->+ _) with
    map_smul' := coe_smul }

variable (M) in
/-- Composition on the right by a continuous map, as a `ContinuousLinearMap`. -/
@[simps]
/--
Definition of `compCLM` / `compCLM` 的定义

English:
definition compCLM
  signature: (f : C(α, β))
  body: g.comp f
  map_add' _ _ := add_comp _ _ f
  map_smul' _ _ := smul_comp _ _ f

中文:
定义 compCLM
  签名: (f : C(α, β))
  定义体: g.comp f
  map_add' _ _ := add_comp _ _ f
  map_smul' _ _ := smul_comp _ _ f

Depends on / 依赖: g.comp
-/
def compCLM (f : C(α, β)) : C(β, M) ->L[R] C(α, M) where
  toFun g := g.comp f
  map_add' _ _ := add_comp _ _ f
  map_smul' _ _ := smul_comp _ _ f

/-- Evaluation at a point, as a continuous linear map. -/
@[simps apply]
/--
Definition of `evalCLM` / `evalCLM` 的定义

English:
definition evalCLM
  signature: (x : α)
  body: f x
  map_add' _ _ := add_apply _ _ x
  map_smul' _ _ := smul_apply _ _ x

中文:
定义 evalCLM
  签名: (x : α)
  定义体: f x
  map_add' _ _ := add_apply _ _ x
  map_smul' _ _ := smul_apply _ _ x
-/
def evalCLM (x : α) : C(α, M) ->L[R] M where
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

/--
Definition of `continuousSubalgebra` / `continuousSubalgebra` 的定义

English:
definition continuousSubalgebra
  signature: : Subalgebra R (α -> A)
  body: { continuousSubsemiring α A with
    carrier := { f : α -> A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }

中文:
定义 continuousSubalgebra
  签名: : Subalgebra R (α -> A)
  定义体: { continuousSubsemiring α A with
    carrier := { f : α -> A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }

Depends on / 依赖: Continuous, algebraMap, algebraMap_mem, carrier, continuousSubsemiring, continuous_const
-/
def continuousSubalgebra : Subalgebra R (α -> A) :=
  { continuousSubsemiring α A with
    carrier := { f : α -> A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }

end Subtype

section ContinuousMap

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A] {A₂ : Type*}
  [TopologicalSpace A₂] [Semiring A₂] [Algebra R A₂] [IsTopologicalSemiring A₂]

/--
Definition of `ContinuousMap.C` / `ContinuousMap.C` 的定义

English:
definition ContinuousMap.C
  signature: : R ->+* C(α, A) where
  body: fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_a

中文:
定义 ContinuousMap.C
  签名: : R ->+* C(α, A) where
  定义体: fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_a

Depends on / 依赖: algebraMap, continuous_const
-/
def ContinuousMap.C : R ->+* C(α, A) where
  toFun := fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_add _ _

@[simp]
/--
theorem `ContinuousMap.C_apply` / 定理 `ContinuousMap.C_apply`

English:
theorem ContinuousMap.C_apply
  given: (r : R) (a : α)
  statement: ContinuousMap.C r a = algebraMap R A r
  proof: rfl

中文:
定理 ContinuousMap.C_apply
  条件: (r : R) (a : α)
  结论: ContinuousMap.C r a = algebraMap R A r
  证明: rfl
-/
theorem ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.C r a = algebraMap R A r :=
  rfl

/--
Instance `ContinuousMap.algebra` / 实例 `ContinuousMap.algebra`

English:
instance ContinuousMap.algebra
  signature: : Algebra R C(α, A) where
  body: ContinuousMap.C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

中文:
实例 ContinuousMap.algebra
  签名: : Algebra R C(α, A) where
  定义体: ContinuousMap.C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

Depends on / 依赖: ContinuousMap, ContinuousMap.C
-/
instance ContinuousMap.algebra : Algebra R C(α, A) where
  algebraMap := ContinuousMap.C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

variable (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`AlgHom`. Similar to `AlgHom.compLeft`. -/
@[simps!]
/--
Definition of `AlgHom.compLeftContinuous` / `AlgHom.compLeftContinuous` 的定义

English:
definition AlgHom.compLeftContinuous
  signature: {α : Type*} [TopologicalSpace α] (g : A ->ₐ[R] A₂)
  body: { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }

中文:
定义 AlgHom.compLeftContinuous
  签名: {α : 类型} [TopologicalSpace α] (g : A ->ₐ[R] A₂)
  定义体: { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }
-/
protected def AlgHom.compLeftContinuous {α : Type*} [TopologicalSpace α] (g : A ->ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) ->ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }

variable (A)

/-- Precomposition of functions into a topological semiring by a continuous map is an algebra
homomorphism. -/
@[simps]
/--
Definition of `ContinuousMap.compRightAlgHom` / `ContinuousMap.compRightAlgHom` 的定义

English:
definition ContinuousMap.compRightAlgHom
  signature: {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  body: g.comp f
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  map_one' := ext fun _ => rfl
  map_mul' _ _ := ext fun _ => rfl
  commutes' _ := ext fun _ => rfl

中文:
定义 ContinuousMap.compRightAlgHom
  签名: {α β : 类型} [TopologicalSpace α] [TopologicalSpace β]
  定义体: g.comp f
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  map_one' := ext fun _ => rfl
  map_mul' _ _ := ext fun _ => rfl
  commutes' _ := ext fun _ => rfl

Depends on / 依赖: g.comp
-/
def ContinuousMap.compRightAlgHom {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) ->ₐ[R] C(α, A) where
  toFun g := g.comp f
  map_zero' := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  map_one' := ext fun _ => rfl
  map_mul' _ _ := ext fun _ => rfl
  commutes' _ := ext fun _ => rfl

/--
theorem `ContinuousMap.compRightAlgHom_continuous` / 定理 `ContinuousMap.compRightAlgHom_continuous`

English:
theorem ContinuousMap.compRightAlgHom_continuous
  statement: {α β : Type*} [TopologicalSpace α]
  proof: continuous_precomp f

中文:
定理 ContinuousMap.compRightAlgHom_continuous
  结论: {α β : 类型} [TopologicalSpace α]
  证明: continuous_precomp f

Depends on / 依赖: continuous_precomp
-/
theorem ContinuousMap.compRightAlgHom_continuous {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : C(α, β)) : Continuous (compRightAlgHom R A f) :=
  continuous_precomp f

variable {A}

/-- Coercion to a function as an `AlgHom`. -/
@[simps!]
/--
Definition of `ContinuousMap.coeFnAlgHom` / `ContinuousMap.coeFnAlgHom` 的定义

English:
definition ContinuousMap.coeFnAlgHom
  signature: : C(α, A) ->ₐ[R] α -> A
  body: { (ContinuousMap.coeFnRingHom : C(α, A) ->+* _) with
    commutes' := fun _ => rfl }

中文:
定义 ContinuousMap.coeFnAlgHom
  签名: : C(α, A) ->ₐ[R] α -> A
  定义体: { (ContinuousMap.coeFnRingHom : C(α, A) ->+* _) with
    commutes' := fun _ => rfl }

Depends on / 依赖: ContinuousMap, ContinuousMap.coeFnRingHom, coeFnRingHom, commutes
-/
def ContinuousMap.coeFnAlgHom : C(α, A) ->ₐ[R] α -> A :=
  { (ContinuousMap.coeFnRingHom : C(α, A) ->+* _) with
    commutes' := fun _ => rfl }

variable {R}

/--
Definition of `Subalgebra.SeparatesPoints` / `Subalgebra.SeparatesPoints` 的定义

English:
abbreviation Subalgebra.SeparatesPoints
  signature: (s : Subalgebra R C(α, A))
  body: Set.SeparatesPoints ((fun f : C(α, A) => (f : α -> A)) '' (s : Set C(α, A)))

中文:
缩写 Subalgebra.SeparatesPoints
  签名: (s : Subalgebra R C(α, A))
  定义体: Set.SeparatesPoints ((fun f : C(α, A) => (f : α -> A)) '' (s : Set C(α, A)))

Depends on / 依赖: SeparatesPoints, Set.SeparatesPoints
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α -> A)) '' (s : Set C(α, A)))

/--
theorem `Subalgebra.separatesPoints_monotone` / 定理 `Subalgebra.separatesPoints_monotone`

English:
theorem Subalgebra.separatesPoints_monotone
  proof: fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]

中文:
定理 Subalgebra.separatesPoints_monotone
  证明: fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]
-/
theorem Subalgebra.separatesPoints_monotone :
    Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints := fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (k : R) (a : α)
  statement: algebraMap R C(α, A) k a = k • (1 : A)
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

中文:
定理 algebraMap_apply
  条件: (k : R) (a : α)
  结论: algebraMap R C(α, A) k a = k • (1 : A)
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
theorem algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable {𝕜 : Type*} [TopologicalSpace 𝕜]
variable (s : Set C(α, 𝕜)) (f : s) (x : α)

/--
Definition of `Set.SeparatesPointsStrongly` / `Set.SeparatesPointsStrongly` 的定义

English:
definition Set.SeparatesPointsStrongly
  signature: (s : Set C(α, 𝕜))
  body: forall (v : α -> 𝕜) (x y : α), exists f in s, (f x : 𝕜) = v x ∧ f y = v y

中文:
定义 Set.SeparatesPointsStrongly
  签名: (s : Set C(α, 𝕜))
  定义体: forall (v : α -> 𝕜) (x y : α), exists f in s, (f x : 𝕜) = v x ∧ f y = v y
-/
def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  forall (v : α -> 𝕜) (x y : α), exists f in s, (f x : 𝕜) = v x ∧ f y = v y

variable [Field 𝕜] [IsTopologicalRing 𝕜]

/--
theorem `Subalgebra.SeparatesPoints.strongly` / 定理 `Subalgebra.SeparatesPoints.strongly`

English:
theorem Subalgebra.SeparatesPoints.strongly
  given: {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints)
  proof: fun v x y => by
  by_cases n : x = y
  · subst n
    exact ⟨_, (v x • (1 : s) : s).prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y != 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s :=
    ((b - a) * (f x - f y)⁻¹) • (algebraMap _ s 

中文:
定理 Subalgebra.SeparatesPoints.strongly
  条件: {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints)
  证明: fun v x y => by
  by_cases n : x = y
  · subst n
    exact ⟨_, (v x • (1 : s) : s).prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y != 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s :=
    ((b - a) * (f x - f y)⁻¹) • (algebraMap _ s 

Depends on / 依赖: algebraMap, mul_one, replace, sub_ne_zero_of_ne
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y => by
  by_cases n : x = y
  · subst n
    exact ⟨_, (v x • (1 : s) : s).prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y != 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s :=
    ((b - a) * (f x - f y)⁻¹) • (algebraMap _ s (f x) - (⟨f, hf⟩ : s)) + algebraMap _ s a
  refine ⟨f', f'.prop, ?_, ?_⟩
  · simp [a, b, f']
  · simp [a, b, f', inv_mul_cancel_right₀ hxy]

end ContinuousMap

/--
Instance `ContinuousMap.subsingleton_subalgebra` / 实例 `ContinuousMap.subsingleton_subalgebra`

English:
instance ContinuousMap.subsingleton_subalgebra
  signature: (α : Type*) [TopologicalSpace α] (R : Type*)
  body: ⟨fun s₁ s₂ => by
    cases isEmpty_or_nonempty α
    · have : Subsingleton C(α, R) := DFunLike.coe_injective.subsingleton
      subsingleton
    · inhabit α
      ext f
      have h : f = algebraMap R C(α, R) (f default) := by
        ext x'
        simp only [mul_one, smul_eq_mul, algebraMap_apply]

中文:
实例 ContinuousMap.subsingleton_subalgebra
  签名: (α : 类型) [TopologicalSpace α] (R : 类型)
  定义体: ⟨fun s₁ s₂ => by
    cases isEmpty_or_nonempty α
    · have : Subsingleton C(α, R) := DFunLike.coe_injective.subsingleton
      subsingleton
    · inhabit α
      ext f
      have h : f = algebraMap R C(α, R) (f default) := by
        ext x'
        simp only [mul_one, smul_eq_mul, algebraMap_apply]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.subsingleton, Subalgebra, Subalgebra.algebraMap_mem, Subsingleton, algebraMap, algebraMap_apply, algebraMap_mem, coe_injective, eq_iff_true_of_subsingleton, inhabit, isEmpty_or_nonempty, mul_one, smul_eq_mul, subsingleton
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

/--
Instance `instSMul'` / 实例 `instSMul'`

English:
instance instSMul'
  signature: : SMul C(α, R) C(α, M)
  body: ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

中文:
实例 instSMul'
  签名: : SMul C(α, R) C(α, M)
  定义体: ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

Depends on / 依赖: Continuous, Continuous.smul
-/
instance instSMul' : SMul C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

/--
lemma `coe_smul'` / 引理 `coe_smul'`

English:
lemma coe_smul'
  given: (f : C(α, R)) (g : C(α, M))
  proof: rfl

中文:
引理 coe_smul'
  条件: (f : C(α, R)) (g : C(α, M))
  证明: rfl
-/
@[simp] lemma coe_smul' (f : C(α, R)) (g : C(α, M)) :
    ⇑(f • g) = ⇑f • ⇑g :=
  rfl

-- (this doesn't need to be @[simp] since it can be derived from `coe_smul'` and `Pi.smul_apply'`)
/--
lemma `smul_apply'` / 引理 `smul_apply'`

English:
lemma smul_apply'
  given: (f : C(α, R)) (g : C(α, M)) (x : α)
  proof: rfl

中文:
引理 smul_apply'
  条件: (f : C(α, R)) (g : C(α, M)) (x : α)
  证明: rfl
-/
lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
    (f • g) x = f x • g x :=
  rfl

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [IsTopologicalSemiring R] [ContinuousAdd M]
  body: by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul R (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; 

中文:
实例 module'
  签名: [IsTopologicalSemiring R] [ContinuousAdd M]
  定义体: by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul R (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; 

Depends on / 依赖: add_smul, mul_smul, one_smul, smul_add, smul_zero, zero_smul
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
/--
Definition of `ContinuousMap.evalAlgHom` / `ContinuousMap.evalAlgHom` 的定义

English:
definition ContinuousMap.evalAlgHom
  signature: (x : X)
  body: f x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

中文:
定义 ContinuousMap.evalAlgHom
  签名: (x : X)
  定义体: f x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
-/
def ContinuousMap.evalAlgHom (x : X) : C(X, R) ->ₐ[S] R where
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
/--
lemma `curry_mul_apply` / 引理 `curry_mul_apply`

English:
lemma curry_mul_apply
  given: [Mul Z] [ContinuousMul Z] (f g : C(X × Y, Z)) (x : X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 curry_mul_apply
  条件: [Mul Z] [ContinuousMul Z] (f g : C(X × Y, Z)) (x : X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma curry_mul_apply [Mul Z] [ContinuousMul Z] (f g : C(X × Y, Z)) (x : X) :
    (f * g).curry x = f.curry x * g.curry x :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `curry_div_apply` / 引理 `curry_div_apply`

English:
lemma curry_div_apply
  given: [Div Z] [ContinuousDiv Z] (f g : C(X × Y, Z)) (x : X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 curry_div_apply
  条件: [Div Z] [ContinuousDiv Z] (f g : C(X × Y, Z)) (x : X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma curry_div_apply [Div Z] [ContinuousDiv Z] (f g : C(X × Y, Z)) (x : X) :
    (f / g).curry x = f.curry x / g.curry x :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `curry_smul_apply` / 引理 `curry_smul_apply`

English:
lemma curry_smul_apply
  statement: {R : Type*} [SMul R Z] [ContinuousConstSMul R Z]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 curry_smul_apply
  结论: {R : 类型} [SMul R Z] [ContinuousConstSMul R Z]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma curry_smul_apply {R : Type*} [SMul R Z] [ContinuousConstSMul R Z]
    (f : C(X × Y, Z)) (r : R) (x : X) :
    (r • f).curry x = r • f.curry x :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `curry_inv_apply` / 引理 `curry_inv_apply`

English:
lemma curry_inv_apply
  given: [Inv Z] [ContinuousInv Z] (f : C(X × Y, Z)) (x : X)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 curry_inv_apply
  条件: [Inv Z] [ContinuousInv Z] (f : C(X × Y, Z)) (x : X)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma curry_inv_apply [Inv Z] [ContinuousInv Z] (f : C(X × Y, Z)) (x : X) :
    (f⁻¹).curry x = (f.curry x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `curry_pow_apply` / 引理 `curry_pow_apply`

English:
lemma curry_pow_apply
  statement: [Monoid Z] [ContinuousMul Z]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 curry_pow_apply
  结论: [Monoid Z] [ContinuousMul Z]
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma curry_pow_apply [Monoid Z] [ContinuousMul Z]
    (f : C(X × Y, Z)) (n : Nat) (x : X) :
    (f ^ n).curry x = (f.curry x) ^ n :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `curry_zpow_apply` / 引理 `curry_zpow_apply`

English:
lemma curry_zpow_apply
  statement: [Group Z] [IsTopologicalGroup Z]
  proof: rfl

中文:
引理 curry_zpow_apply
  结论: [Group Z] [IsTopologicalGroup Z]
  证明: rfl
-/
lemma curry_zpow_apply [Group Z] [IsTopologicalGroup Z]
    (f : C(X × Y, Z)) (n : Int) (x : X) :
    (f ^ n).curry x = (f.curry x) ^ n :=
  rfl

end ContinuousMap

end curry
