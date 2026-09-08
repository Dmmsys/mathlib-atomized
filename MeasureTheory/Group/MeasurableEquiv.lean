/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `MeasurableEquiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `MeasurableEquiv.vadd`: additive version of `MeasurableEquiv.smul`;
* `MeasurableEquiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `MeasurableEquiv.mulLeft`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `MeasurableEquiv.addLeft`: additive version of `MeasurableEquiv.mulLeft`;
* `MeasurableEquiv.mulRight`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `MeasurableEquiv.addRight`: additive version of `MeasurableEquiv.mulRight`;
* `MeasurableEquiv.mulLeft₀`, `MeasurableEquiv.mulRight₀`: versions of
  `MeasurableEquiv.mulLeft` and `MeasurableEquiv.mulRight` for groups with zero;
* `MeasurableEquiv.inv`: `Inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `MeasurableEquiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/

@[expose] public section

open scoped Pointwise NNReal

namespace MeasurableEquiv

variable {G G₀ α : Type*} [MeasurableSpace α] [Group G] [GroupWithZero G₀] [MulAction G α]
  [MulAction G₀ α] [MeasurableConstSMul G α] [MeasurableConstSMul G₀ α]

/-- If a group `G` acts on `α` by measurable maps, then each element `c : G` defines a measurable
automorphism of `α`. -/
@[to_additive (attr := simps! -fullyApplied toEquiv apply)
      /-- If an additive group `G` acts on `α` by measurable maps, then each element `c : G`
      defines a measurable automorphism of `α`. -/]
/-
**MeasurableEquiv.smul** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：smul (c : G) : α ≃ᵐ α where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_toFun := measurable_const_smul c
  measurable_invFun := measurable_const_smul c⁻¹

@[to_additive]
/-
**MeasurableEquiv._root_.measurableEmbedding_const_smul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_const_smul (c : G) : MeasurableEmbedding (c • · : α → α) :=
  (smul c).measurableEmbedding

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl

/-- If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero element `c : G₀`
defines a measurable automorphism of `α` -/
/-
**MeasurableEquiv.smul** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：smul (c : G) : α ≃ᵐ α where toEquiv
参数：c : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a group with zero `G₀` acts on `α` by measurable maps, then each nonzero elem
ent `c : G₀`
defines a measurable automorphism of `α`
-/
def smul₀ (c : G₀) (hc : c ≠ 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)
/-
**MeasurableEquiv.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_smul₀ {c : G₀} (hc : c ≠ 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (c • ·) := rfl

@[simp]
/-
**MeasurableEquiv.symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹
参数：c : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_smul₀ {c : G₀} (hc : c ≠ 0) :
    (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
  ext rfl
/-
**MeasurableEquiv._root_.measurableEmbedding_const_smul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_const_smul₀ {c : G₀} (hc : c ≠ 0) :
    MeasurableEmbedding (c • · : α → α) :=
  (smul₀ c hc).measurableEmbedding

variable [MeasurableSpace G] [MeasurableSpace G₀]

section Mul

variable [MeasurableMul G] [MeasurableMul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      /-- If `G` is an additive group with measurable addition, then addition of `g : G`
      on the left is a measurable automorphism of `G`. -/]
/-
**MeasurableEquiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：mulLeft (g : G) : G ≃ᵐ G
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_mulLeft (g : G) : ⇑(mulLeft g) = (g * ·)
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulLeft (g : G) : ⇑(mulLeft g) = (g * ·) :=
  rfl

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.symm_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.toEquiv_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g :=
  rfl

@[to_additive]
/-
**MeasurableEquiv._root_.measurableEmbedding_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `
MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_mulLeft (g : G) : MeasurableEmbedding (g * ·) :=
  (mulLeft g).measurableEmbedding

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      /-- If `G` is an additive group with measurable addition, then addition of `g : G`
      on the right is a measurable automorphism of `G`. -/]
/-
**MeasurableEquiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：mulRight (g : G) : G ≃ᵐ G where toEquiv
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g

@[to_additive]
/-
**MeasurableEquiv._root_.measurableEmbedding_mulRight** 是 Mathlib 中的一个定理，位于命名空间 
`MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_mulRight (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).measurableEmbedding

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.coe_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.symm_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.toEquiv_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then left multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
/-
**MeasurableEquiv.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：mulLeft (g : G) : G ≃ᵐ G
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G₀` is a group with zero with measurable multiplication, then left multiplic
ation by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`.
-/
def mulLeft₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg
/-
**MeasurableEquiv._root_.measurableEmbedding_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `
MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_mulLeft₀ {g : G₀} (hg : g ≠ 0) :
    MeasurableEmbedding (g * ·) :=
  (mulLeft₀ g hg).measurableEmbedding
/-
**MeasurableEquiv.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_mulLeft (g : G) : ⇑(mulLeft g) = (g * ·)
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mulLeft₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulLeft₀ g hg) = (g * ·) := rfl

@[simp]
/-
**MeasurableEquiv.symm_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_mulLeft₀ {g : G₀} (hg : g ≠ 0) :
    (mulLeft₀ g hg).symm = mulLeft₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
/-
**MeasurableEquiv.toEquiv_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_mulLeft₀ {g : G₀} (hg : g ≠ 0) : (mulLeft₀ g hg).toEquiv = Equiv.mulLeft₀ g hg :=
  rfl

/-- If `G₀` is a group with zero with measurable multiplication, then right multiplication by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`. -/
/-
**MeasurableEquiv.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：mulRight (g : G) : G ≃ᵐ G where toEquiv
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G₀` is a group with zero with measurable multiplication, then right multipli
cation by a
nonzero element `g : G₀` is a measurable automorphism of `G₀`.
-/
def mulRight₀ (g : G₀) (hg : g ≠ 0) : G₀ ≃ᵐ G₀ where
  toEquiv := Equiv.mulRight₀ g hg
/-
**MeasurableEquiv._root_.measurableEmbedding_mulRight** 是 Mathlib 中的一个定理，位于命名空间 
`MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.measurableEmbedding_mulRight₀ {g : G₀} (hg : g ≠ 0) :
    MeasurableEmbedding fun x => x * g :=
  (mulRight₀ g hg).measurableEmbedding

@[simp]
/-
**MeasurableEquiv.coe_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulRight₀ {g : G₀} (hg : g ≠ 0) : ⇑(mulRight₀ g hg) = fun x => x * g :=
  rfl

@[simp]
/-
**MeasurableEquiv.symm_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableS
pace α] [inst_1 : MeasurableSpace β] {e₁ e₂ : α ≃ᵐ β},   ⇑e₁ = ⇑e₂ → e₁ = e₂
-/
theorem symm_mulRight₀ {g : G₀} (hg : g ≠ 0) :
    (mulRight₀ g hg).symm = mulRight₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
/-
**MeasurableEquiv.toEquiv_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_mulRight₀ {g : G₀} (hg : g ≠ 0) : (mulRight₀ g hg).toEquiv = Equiv.mulRight₀ g hg :=
  rfl

end Mul

/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive (attr := simps! -fullyApplied toEquiv apply)
    /-- Negation as a measurable automorphism of an additive group. -/]
/-
**MeasurableEquiv.inv** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G w
here toEquiv
参数：G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G where
  toEquiv := Equiv.inv G

@[to_additive (attr := simp)]
/-
**MeasurableEquiv.symm_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableEquiv`。
形式化陈述：symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : (in
v G).symm = inv G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] :
    (inv G).symm = inv G :=
  rfl

/-- `equiv.divRight` as a `MeasurableEquiv`. -/
@[to_additive /-- `equiv.subRight` as a `MeasurableEquiv` -/]
/-
**MeasurableEquiv.divRight** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：divRight [MeasurableMul G] (g : G) : G ≃ᵐ G where toEquiv
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`equiv.divRight` as a `MeasurableEquiv`.
-/
def divRight [MeasurableMul G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divRight g
  measurable_toFun := measurable_div_const' g
  measurable_invFun := measurable_mul_const g

@[to_additive]
/-
**MeasurableEquiv._root_.measurableEmbedding_divRight** 是 Mathlib 中的一个引理，位于命名空间 
`MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.measurableEmbedding_divRight [MeasurableMul G] (g : G) :
    MeasurableEmbedding fun x ↦ x / g :=
  (divRight g).measurableEmbedding

/-- `equiv.divLeft` as a `MeasurableEquiv` -/
@[to_additive /-- `equiv.subLeft` as a `MeasurableEquiv` -/]
/-
**MeasurableEquiv.divLeft** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G where toEquiv
参数：g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`equiv.divLeft` as a `MeasurableEquiv`
-/
def divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divLeft g
  measurable_toFun := measurable_id.const_div g
  measurable_invFun := measurable_inv.mul_const g

@[to_additive]
/-
**MeasurableEquiv._root_.measurableEmbedding_divLeft** 是 Mathlib 中的一个引理，位于命名空间 `
MeasurableEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.measurableEmbedding_divLeft [MeasurableMul G] [MeasurableInv G] (g : G) :
    MeasurableEmbedding fun x ↦ g / x :=
  (divLeft g).measurableEmbedding

end MeasurableEquiv

namespace MeasureTheory.Measure
variable {G A : Type*} [Group G] [MulAction G A] [MeasurableSpace A]
  [MeasurableConstSMul G A] {μ ν : Measure A} {g : G}

/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DistribMulAction Gᵈᵐᵃ (Measure A) where
  smul g μ := μ.map (DomMulAct.mk.symm g⁻¹ • ·)
  one_smul μ := show μ.map _ = _ by simp
  mul_smul g g' μ := show μ.map _ = ((μ.map _).map _) by
    rw [map_map]
    · simp [Function.comp_def, mul_smul]
    · exact measurable_const_smul ..
    · exact measurable_const_smul ..
  smul_zero g := show (0 : Measure A).map _ = 0 by simp
  smul_add g μ ν := show (μ + ν).map _ = μ.map _ + ν.map _ by
    rw [Measure.map_add]; exact measurable_const_smul ..
/-
**MeasureTheory.Measure.domSMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) : (g • μ) s = μ (DomM
ulAct.mk.symm g • s)
参数：μ : Measure A；g : Gᵈᵐᵃ；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.preimage_smul_inv`：preimage_smul_inv (a : α) (t : Set β) : (fun x =>
 a⁻¹ • x) ⁻¹' t = a • t
-/
lemma domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ (DomMulAct.mk.symm g • s) := by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass ℝ≥0 Gᵈᵐᵃ (Measure A) where
  smul_comm r g μ := show r • μ.map _ = (r • μ).map _ by simp
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass Gᵈᵐᵃ ℝ≥0 (Measure A) := .symm ..

end MeasureTheory.Measure

