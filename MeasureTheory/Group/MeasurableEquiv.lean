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
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: (c : G)
  body: MulAction.toPerm c
  measurable_toFun := measurable_const_smul c
  measurable_invFun := measurable_const_smul c⁻¹

@[to_additive]

中文:
定义 smul
  签名: (c : G)
  定义体: MulAction.toPerm c
  measurable_toFun := measurable_const_smul c
  measurable_invFun := measurable_const_smul c⁻¹

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, toPerm
-/
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_toFun := measurable_const_smul c
  measurable_invFun := measurable_const_smul c⁻¹

@[to_additive]
/--
theorem `_root_.measurableEmbedding_const_smul` / 定理 `_root_.measurableEmbedding_const_smul`

English:
theorem _root_.measurableEmbedding_const_smul
  given: (c : G)
  statement: MeasurableEmbedding (c • · : α -> α)
  proof: (smul c).measurableEmbedding

@[to_additive (attr := simp)]

中文:
定理 _root_.measurableEmbedding_const_smul
  条件: (c : G)
  结论: 可测嵌入 (c • · : α -> α)
  证明: (smul c).measurableEmbedding

@[to_additive (attr := simp)]

Depends on / 依赖: measurableEmbedding
-/
theorem _root_.measurableEmbedding_const_smul (c : G) : MeasurableEmbedding (c • · : α -> α) :=
  (smul c).measurableEmbedding

@[to_additive (attr := simp)]
/--
theorem `symm_smul` / 定理 `symm_smul`

English:
theorem symm_smul
  given: (c : G)
  statement: (smul c : α ≃ᵐ α).symm = smul c⁻¹
  proof: ext rfl

中文:
定理 symm_smul
  条件: (c : G)
  结论: (smul c : α ≃ᵐ α).symm = smul c⁻¹
  证明: ext rfl
-/
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl

/--
Definition of `smul₀` / `smul₀` 的定义

English:
definition smul₀
  signature: (c : G₀) (hc : c != 0)
  body: MeasurableEquiv.smul (Units.mk0 c hc)

中文:
定义 smul₀
  签名: (c : G₀) (hc : c != 0)
  定义体: MeasurableEquiv.smul (Units.mk0 c hc)

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.smul, Units.mk0
-/
def smul₀ (c : G₀) (hc : c != 0) : α ≃ᵐ α :=
  MeasurableEquiv.smul (Units.mk0 c hc)

/--
lemma `coe_smul₀` / 引理 `coe_smul₀`

English:
lemma coe_smul₀
  given: {c : G₀} (hc : c != 0)
  statement: ⇑(smul₀ c hc : α ≃ᵐ α) = (c • ·)
  proof: rfl

@[simp]

中文:
引理 coe_smul₀
  条件: {c : G₀} (hc : c != 0)
  结论: ⇑(smul₀ c hc : α ≃ᵐ α) = (c • ·)
  证明: rfl

@[simp]
-/
@[simp] lemma coe_smul₀ {c : G₀} (hc : c != 0) : ⇑(smul₀ c hc : α ≃ᵐ α) = (c • ·) := rfl

@[simp]
/--
theorem `symm_smul₀` / 定理 `symm_smul₀`

English:
theorem symm_smul₀
  given: {c : G₀} (hc : c != 0)
  proof: ext rfl

中文:
定理 symm_smul₀
  条件: {c : G₀} (hc : c != 0)
  证明: ext rfl
-/
theorem symm_smul₀ {c : G₀} (hc : c != 0) :
    (smul₀ c hc : α ≃ᵐ α).symm = smul₀ c⁻¹ (inv_ne_zero hc) :=
  ext rfl

/--
theorem `_root_.measurableEmbedding_const_smul₀` / 定理 `_root_.measurableEmbedding_const_smul₀`

English:
theorem _root_.measurableEmbedding_const_smul₀
  given: {c : G₀} (hc : c != 0)
  proof: (smul₀ c hc).measurableEmbedding

中文:
定理 _root_.measurableEmbedding_const_smul₀
  条件: {c : G₀} (hc : c != 0)
  证明: (smul₀ c hc).measurableEmbedding

Depends on / 依赖: measurableEmbedding
-/
theorem _root_.measurableEmbedding_const_smul₀ {c : G₀} (hc : c != 0) :
    MeasurableEmbedding (c • · : α -> α) :=
  (smul₀ c hc).measurableEmbedding

variable [MeasurableSpace G] [MeasurableSpace G₀]

section Mul

variable [MeasurableMul G] [MeasurableMul G₀]

/-- If `G` is a group with measurable multiplication, then left multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      /-- If `G` is an additive group with measurable addition, then addition of `g : G`
      on the left is a measurable automorphism of `G`. -/]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (g : G)
  body: smul g

@[to_additive (attr := simp)]

中文:
定义 mulLeft
  签名: (g : G)
  定义体: smul g

@[to_additive (attr := simp)]
-/
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g

@[to_additive (attr := simp)]
/--
theorem `coe_mulLeft` / 定理 `coe_mulLeft`

English:
theorem coe_mulLeft
  given: (g : G)
  statement: ⇑(mulLeft g) = (g * ·)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mulLeft
  条件: (g : G)
  结论: ⇑(mulLeft g) = (g * ·)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mulLeft (g : G) : ⇑(mulLeft g) = (g * ·) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `symm_mulLeft` / 定理 `symm_mulLeft`

English:
theorem symm_mulLeft
  given: (g : G)
  statement: (mulLeft g).symm = mulLeft g⁻¹
  proof: ext rfl

@[to_additive (attr := simp)]

中文:
定理 symm_mulLeft
  条件: (g : G)
  结论: (mulLeft g).symm = mulLeft g⁻¹
  证明: ext rfl

@[to_additive (attr := simp)]
-/
theorem symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
/--
theorem `toEquiv_mulLeft` / 定理 `toEquiv_mulLeft`

English:
theorem toEquiv_mulLeft
  given: (g : G)
  statement: (mulLeft g).toEquiv = Equiv.mulLeft g
  proof: rfl

@[to_additive]

中文:
定理 toEquiv_mulLeft
  条件: (g : G)
  结论: (mulLeft g).toEquiv = 等价.mulLeft g
  证明: rfl

@[to_additive]
-/
theorem toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g :=
  rfl

@[to_additive]
/--
theorem `_root_.measurableEmbedding_mulLeft` / 定理 `_root_.measurableEmbedding_mulLeft`

English:
theorem _root_.measurableEmbedding_mulLeft
  given: (g : G)
  statement: MeasurableEmbedding (g * ·)
  proof: (mulLeft g).measurableEmbedding

中文:
定理 _root_.measurableEmbedding_mulLeft
  条件: (g : G)
  结论: 可测嵌入 (g * ·)
  证明: (mulLeft g).measurableEmbedding

Depends on / 依赖: measurableEmbedding, mulLeft
-/
theorem _root_.measurableEmbedding_mulLeft (g : G) : MeasurableEmbedding (g * ·) :=
  (mulLeft g).measurableEmbedding

/-- If `G` is a group with measurable multiplication, then right multiplication by `g : G` is a
measurable automorphism of `G`. -/
@[to_additive
      /-- If `G` is an additive group with measurable addition, then addition of `g : G`
      on the right is a measurable automorphism of `G`. -/]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (g : G)
  body: Equiv.mulRight g

@[to_additive]

中文:
定义 mulRight
  签名: (g : G)
  定义体: Equiv.mulRight g

@[to_additive]

Depends on / 依赖: Equiv.mulRight, mulRight
-/
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g

@[to_additive]
/--
theorem `_root_.measurableEmbedding_mulRight` / 定理 `_root_.measurableEmbedding_mulRight`

English:
theorem _root_.measurableEmbedding_mulRight
  given: (g : G)
  statement: MeasurableEmbedding fun x => x * g
  proof: (mulRight g).measurableEmbedding

@[to_additive (attr := simp)]

中文:
定理 _root_.measurableEmbedding_mulRight
  条件: (g : G)
  结论: 可测嵌入 fun x => x * g
  证明: (mulRight g).measurableEmbedding

@[to_additive (attr := simp)]

Depends on / 依赖: measurableEmbedding, mulRight
-/
theorem _root_.measurableEmbedding_mulRight (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).measurableEmbedding

@[to_additive (attr := simp)]
/--
theorem `coe_mulRight` / 定理 `coe_mulRight`

English:
theorem coe_mulRight
  given: (g : G)
  statement: ⇑(mulRight g) = fun x => x * g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mulRight
  条件: (g : G)
  结论: ⇑(mulRight g) = fun x => x * g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `symm_mulRight` / 定理 `symm_mulRight`

English:
theorem symm_mulRight
  given: (g : G)
  statement: (mulRight g).symm = mulRight g⁻¹
  proof: ext rfl

@[to_additive (attr := simp)]

中文:
定理 symm_mulRight
  条件: (g : G)
  结论: (mulRight g).symm = mulRight g⁻¹
  证明: ext rfl

@[to_additive (attr := simp)]
-/
theorem symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
/--
theorem `toEquiv_mulRight` / 定理 `toEquiv_mulRight`

English:
theorem toEquiv_mulRight
  given: (g : G)
  statement: (mulRight g).toEquiv = Equiv.mulRight g
  proof: rfl

中文:
定理 toEquiv_mulRight
  条件: (g : G)
  结论: (mulRight g).toEquiv = 等价.mulRight g
  证明: rfl
-/
theorem toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g :=
  rfl

/--
Definition of `mulLeft₀` / `mulLeft₀` 的定义

English:
definition mulLeft₀
  signature: (g : G₀) (hg : g != 0)
  body: smul₀ g hg

中文:
定义 mulLeft₀
  签名: (g : G₀) (hg : g != 0)
  定义体: smul₀ g hg
-/
def mulLeft₀ (g : G₀) (hg : g != 0) : G₀ ≃ᵐ G₀ :=
  smul₀ g hg

/--
theorem `_root_.measurableEmbedding_mulLeft₀` / 定理 `_root_.measurableEmbedding_mulLeft₀`

English:
theorem _root_.measurableEmbedding_mulLeft₀
  given: {g : G₀} (hg : g != 0)
  proof: (mulLeft₀ g hg).measurableEmbedding

中文:
定理 _root_.measurableEmbedding_mulLeft₀
  条件: {g : G₀} (hg : g != 0)
  证明: (mulLeft₀ g hg).measurableEmbedding

Depends on / 依赖: measurableEmbedding
-/
theorem _root_.measurableEmbedding_mulLeft₀ {g : G₀} (hg : g != 0) :
    MeasurableEmbedding (g * ·) :=
  (mulLeft₀ g hg).measurableEmbedding

/--
lemma `coe_mulLeft₀` / 引理 `coe_mulLeft₀`

English:
lemma coe_mulLeft₀
  given: {g : G₀} (hg : g != 0)
  statement: ⇑(mulLeft₀ g hg) = (g * ·)
  proof: rfl

@[simp]

中文:
引理 coe_mulLeft₀
  条件: {g : G₀} (hg : g != 0)
  结论: ⇑(mulLeft₀ g hg) = (g * ·)
  证明: rfl

@[simp]
-/
@[simp] lemma coe_mulLeft₀ {g : G₀} (hg : g != 0) : ⇑(mulLeft₀ g hg) = (g * ·) := rfl

@[simp]
/--
theorem `symm_mulLeft₀` / 定理 `symm_mulLeft₀`

English:
theorem symm_mulLeft₀
  given: {g : G₀} (hg : g != 0)
  proof: ext rfl

@[simp]

中文:
定理 symm_mulLeft₀
  条件: {g : G₀} (hg : g != 0)
  证明: ext rfl

@[simp]
-/
theorem symm_mulLeft₀ {g : G₀} (hg : g != 0) :
    (mulLeft₀ g hg).symm = mulLeft₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
/--
theorem `toEquiv_mulLeft₀` / 定理 `toEquiv_mulLeft₀`

English:
theorem toEquiv_mulLeft₀
  given: {g : G₀} (hg : g != 0)
  statement: (mulLeft₀ g hg).toEquiv = Equiv.mulLeft₀ g hg
  proof: rfl

中文:
定理 toEquiv_mulLeft₀
  条件: {g : G₀} (hg : g != 0)
  结论: (mulLeft₀ g hg).toEquiv = 等价.mulLeft₀ g hg
  证明: rfl
-/
theorem toEquiv_mulLeft₀ {g : G₀} (hg : g != 0) : (mulLeft₀ g hg).toEquiv = Equiv.mulLeft₀ g hg :=
  rfl

/--
Definition of `mulRight₀` / `mulRight₀` 的定义

English:
definition mulRight₀
  signature: (g : G₀) (hg : g != 0)
  body: Equiv.mulRight₀ g hg

中文:
定义 mulRight₀
  签名: (g : G₀) (hg : g != 0)
  定义体: Equiv.mulRight₀ g hg

Depends on / 依赖: Equiv.mulRight
-/
def mulRight₀ (g : G₀) (hg : g != 0) : G₀ ≃ᵐ G₀ where
  toEquiv := Equiv.mulRight₀ g hg

/--
theorem `_root_.measurableEmbedding_mulRight₀` / 定理 `_root_.measurableEmbedding_mulRight₀`

English:
theorem _root_.measurableEmbedding_mulRight₀
  given: {g : G₀} (hg : g != 0)
  proof: (mulRight₀ g hg).measurableEmbedding

@[simp]

中文:
定理 _root_.measurableEmbedding_mulRight₀
  条件: {g : G₀} (hg : g != 0)
  证明: (mulRight₀ g hg).measurableEmbedding

@[simp]

Depends on / 依赖: measurableEmbedding
-/
theorem _root_.measurableEmbedding_mulRight₀ {g : G₀} (hg : g != 0) :
    MeasurableEmbedding fun x => x * g :=
  (mulRight₀ g hg).measurableEmbedding

@[simp]
/--
theorem `coe_mulRight₀` / 定理 `coe_mulRight₀`

English:
theorem coe_mulRight₀
  given: {g : G₀} (hg : g != 0)
  statement: ⇑(mulRight₀ g hg) = fun x => x * g
  proof: rfl

@[simp]

中文:
定理 coe_mulRight₀
  条件: {g : G₀} (hg : g != 0)
  结论: ⇑(mulRight₀ g hg) = fun x => x * g
  证明: rfl

@[simp]
-/
theorem coe_mulRight₀ {g : G₀} (hg : g != 0) : ⇑(mulRight₀ g hg) = fun x => x * g :=
  rfl

@[simp]
/--
theorem `symm_mulRight₀` / 定理 `symm_mulRight₀`

English:
theorem symm_mulRight₀
  given: {g : G₀} (hg : g != 0)
  proof: ext rfl

@[simp]

中文:
定理 symm_mulRight₀
  条件: {g : G₀} (hg : g != 0)
  证明: ext rfl

@[simp]
-/
theorem symm_mulRight₀ {g : G₀} (hg : g != 0) :
    (mulRight₀ g hg).symm = mulRight₀ g⁻¹ (inv_ne_zero hg) :=
  ext rfl

@[simp]
/--
theorem `toEquiv_mulRight₀` / 定理 `toEquiv_mulRight₀`

English:
theorem toEquiv_mulRight₀
  given: {g : G₀} (hg : g != 0)
  statement: (mulRight₀ g hg).toEquiv = Equiv.mulRight₀ g hg
  proof: rfl

中文:
定理 toEquiv_mulRight₀
  条件: {g : G₀} (hg : g != 0)
  结论: (mulRight₀ g hg).toEquiv = 等价.mulRight₀ g hg
  证明: rfl
-/
theorem toEquiv_mulRight₀ {g : G₀} (hg : g != 0) : (mulRight₀ g hg).toEquiv = Equiv.mulRight₀ g hg :=
  rfl

end Mul

/-- Inversion as a measurable automorphism of a group or group with zero. -/
@[to_additive (attr := simps! -fullyApplied toEquiv apply)
    /-- Negation as a measurable automorphism of an additive group. -/]
/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
  body: Equiv.inv G

@[to_additive (attr := simp)]

中文:
定义 inv
  签名: (G) [可测空间 G] [InvolutiveInv G] [MeasurableInv G]
  定义体: Equiv.inv G

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.inv
-/
def inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G where
  toEquiv := Equiv.inv G

@[to_additive (attr := simp)]
/--
theorem `symm_inv` / 定理 `symm_inv`

English:
theorem symm_inv
  given: {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
  proof: rfl

中文:
定理 symm_inv
  条件: {G} [可测空间 G] [InvolutiveInv G] [MeasurableInv G]
  证明: rfl
-/
theorem symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] :
    (inv G).symm = inv G :=
  rfl

/-- `equiv.divRight` as a `MeasurableEquiv`. -/
@[to_additive /-- `equiv.subRight` as a `MeasurableEquiv` -/]
/--
Definition of `divRight` / `divRight` 的定义

English:
definition divRight
  signature: [MeasurableMul G] (g : G)
  body: Equiv.divRight g
  measurable_toFun := measurable_div_const' g
  measurable_invFun := measurable_mul_const g

@[to_additive]

中文:
定义 divRight
  签名: [MeasurableMul G] (g : G)
  定义体: Equiv.divRight g
  measurable_toFun := measurable_div_const' g
  measurable_invFun := measurable_mul_const g

@[to_additive]

Depends on / 依赖: Equiv.divRight, divRight
-/
def divRight [MeasurableMul G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divRight g
  measurable_toFun := measurable_div_const' g
  measurable_invFun := measurable_mul_const g

@[to_additive]
/--
lemma `_root_.measurableEmbedding_divRight` / 引理 `_root_.measurableEmbedding_divRight`

English:
lemma _root_.measurableEmbedding_divRight
  given: [MeasurableMul G] (g : G)
  proof: (divRight g).measurableEmbedding

中文:
引理 _root_.measurableEmbedding_divRight
  条件: [MeasurableMul G] (g : G)
  证明: (divRight g).measurableEmbedding

Depends on / 依赖: divRight, measurableEmbedding
-/
lemma _root_.measurableEmbedding_divRight [MeasurableMul G] (g : G) :
    MeasurableEmbedding fun x => x / g :=
  (divRight g).measurableEmbedding

/-- `equiv.divLeft` as a `MeasurableEquiv` -/
@[to_additive /-- `equiv.subLeft` as a `MeasurableEquiv` -/]
/--
Definition of `divLeft` / `divLeft` 的定义

English:
definition divLeft
  signature: [MeasurableMul G] [MeasurableInv G] (g : G)
  body: Equiv.divLeft g
  measurable_toFun := measurable_id.const_div g
  measurable_invFun := measurable_inv.mul_const g

@[to_additive]

中文:
定义 divLeft
  签名: [MeasurableMul G] [MeasurableInv G] (g : G)
  定义体: Equiv.divLeft g
  measurable_toFun := measurable_id.const_div g
  measurable_invFun := measurable_inv.mul_const g

@[to_additive]

Depends on / 依赖: Equiv.divLeft, Ideal.Quotient.subsingleton_iff.mp, Quotient, comap_top, dif_neg, divLeft, h.symm.trans, hp.ne_top, ne_top, subsingleton_iff
-/
def divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divLeft g
  measurable_toFun := measurable_id.const_div g
  measurable_invFun := measurable_inv.mul_const g

@[to_additive]
/--
lemma `_root_.measurableEmbedding_divLeft` / 引理 `_root_.measurableEmbedding_divLeft`

English:
lemma _root_.measurableEmbedding_divLeft
  given: [MeasurableMul G] [MeasurableInv G] (g : G)
  proof: (divLeft g).measurableEmbedding

中文:
引理 _root_.measurableEmbedding_divLeft
  条件: [MeasurableMul G] [MeasurableInv G] (g : G)
  证明: (divLeft g).measurableEmbedding

Depends on / 依赖: dif_pos, divLeft, inertiaDeg, measurableEmbedding, over_def
-/
lemma _root_.measurableEmbedding_divLeft [MeasurableMul G] [MeasurableInv G] (g : G) :
    MeasurableEmbedding fun x => g / x :=
  (divLeft g).measurableEmbedding

end MeasurableEquiv

namespace MeasureTheory.Measure
variable {G A : Type*} [Group G] [MulAction G A] [MeasurableSpace A]
  [MeasurableConstSMul G A] {μ ν : Measure A} {g : G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction Gᵈᵐᵃ (Measure A)
  body: μ.map (DomMulAct.mk.symm g⁻¹ • ·)
  one_smul μ := show μ.map _ = _ by simp
  mul_smul g g' μ := show μ.map _ = ((μ.map _).map _) by
    rw [map_map]
    · simp [Function.comp_def, mul_smul]
    · exact measurable_const_smul ..
    · exact measurable_const_smul ..
  smul_zero g := show (0 : Measure A

中文:
实例 :
  签名: 分配乘法作用 Gᵈᵐᵃ (测度 A)
  定义体: μ.map (DomMulAct.mk.symm g⁻¹ • ·)
  one_smul μ := show μ.map _ = _ by simp
  mul_smul g g' μ := show μ.map _ = ((μ.map _).map _) by
    rw [map_map]
    · simp [Function.comp_def, mul_smul]
    · exact measurable_const_smul ..
    · exact measurable_const_smul ..
  smul_zero g := show (0 : Measure A

Depends on / 依赖: DomMulAct, DomMulAct.mk.symm, Nontrivial, Quotient, Quotient.nontrivial_of_liesOver_of_isPrime, _algebraMap, finrank_pos, finrank_pos.trans_eq, inertiaDeg, nontrivial_of_liesOver_of_isPrime, trans_eq
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

/--
lemma `domSMul_apply` / 引理 `domSMul_apply`

English:
lemma domSMul_apply
  given: (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A)
  proof: by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s

中文:
引理 domSMul_apply
  条件: (μ : 测度 A) (g : Gᵈᵐᵃ) (s : 集合 A)
  证明: by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s

Depends on / 依赖: DomMulAct, DomMulAct.mk.symm, Ideal.over_def, IsPrime, MeasurableEquiv, MeasurableEquiv.smul, Module, Module.finrank_pos.trans_eq, Set.preimage_smul_inv, _algebraMap, finrank_pos, inertiaDeg, map_apply, over_def, p.IsPrime, preimage_smul_inv, trans_eq
-/
lemma domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ (DomMulAct.mk.symm g • s) := by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass Real>=0 Gᵈᵐᵃ (Measure A)
  body: show r • μ.map _ = (r • μ).map _ by simp

中文:
实例 :
  签名: 标量交换类 实数>=0 Gᵈᵐᵃ (测度 A)
  定义体: show r • μ.map _ = (r • μ).map _ by simp

Depends on / 依赖: Nat.ne_of_lt, _pos, inertiaDeg, ne_of_lt
-/
instance : SMulCommClass Real>=0 Gᵈᵐᵃ (Measure A) where
  smul_comm r g μ := show r • μ.map _ = (r • μ).map _ by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass Gᵈᵐᵃ Real>=0 (Measure A)
  body: .symm ..

中文:
实例 :
  签名: 标量交换类 Gᵈᵐᵃ 实数>=0 (测度 A)
  定义体: .symm ..

Depends on / 依赖: AlgHom, AlgHom.comp_algebraMap, LiesOver, P.LiesOver, P.comap, Quotient, Quotient.algEquivOfEqComap, _algebraMap, algEquivOfEqComap, algebraMap, comap_coe, comap_comap, comp_algebraMap, dif_neg, e.toAlgHom_toRingHom, eq.symm, finrank_eq, he.mp, inertiaDeg, toAlgHom_toRingHom
-/
instance : SMulCommClass Gᵈᵐᵃ Real>=0 (Measure A) := .symm ..

end MeasureTheory.Measure
