/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e.
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `SymAlg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by `Mathlib/Algebra/Opposites.lean`. We use Oxford Spellings
(IETF en-GB-oxendict).

## Note

See `SymmetricAlgebra` instead if you are looking for the symmetric algebra of a module.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

@[expose] public section


open Function

/--
Definition of `SymAlg` / `SymAlg` 的定义

English:
definition SymAlg
  signature: (α : Type*)
  body: α

@[inherit_doc] postfix:max "ˢʸᵐ" => SymAlg

中文:
定义 SymAlg
  签名: (α : 类型)
  定义体: α

@[inherit_doc] postfix:max "ˢʸᵐ" => SymAlg
-/
def SymAlg (α : Type*) : Type _ :=
  α

@[inherit_doc] postfix:max "ˢʸᵐ" => SymAlg

namespace SymAlg

variable {α : Type*}

/-- The element of `SymAlg α` that represents `a : α`. -/
@[match_pattern]
/--
Definition of `sym` / `sym` 的定义

English:
definition sym
  signature: : α ≃ αˢʸᵐ
  body: Equiv.refl _

中文:
定义 sym
  签名: : α ≃ αˢʸᵐ
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl, Scheme, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion, Set.image_preimage_eq_inter_range.trans, X.basicOpen, X.basicOpen_res, X.presheaf.map, basicOpen, basicOpen_res, convert, fapply, hU.basicOpen, homOfLE, image_preimage_eq_inter_range, isAffineOpen_iff_of_isOpenImmersion, le_top, presheaf
-/
def sym : α ≃ αˢʸᵐ :=
  Equiv.refl _

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
-- We add `@[pp_nodot]` in case RFC https://github.com/leanprover/lean4/issues/6178 happens.
@[pp_nodot]
/--
Definition of `unsym` / `unsym` 的定义

English:
definition unsym
  signature: : αˢʸᵐ ≃ α
  body: Equiv.refl _

@[simp]

中文:
定义 unsym
  签名: : αˢʸᵐ ≃ α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def unsym : αˢʸᵐ ≃ α :=
  Equiv.refl _

@[simp]
/--
theorem `unsym_sym` / 定理 `unsym_sym`

English:
theorem unsym_sym
  given: (a : α)
  statement: unsym (sym a) = a
  proof: rfl

@[simp]

中文:
定理 unsym_sym
  条件: (a : α)
  结论: unsym (sym a) = a
  证明: rfl

@[simp]
-/
theorem unsym_sym (a : α) : unsym (sym a) = a :=
  rfl

@[simp]
/--
theorem `sym_unsym` / 定理 `sym_unsym`

English:
theorem sym_unsym
  given: (a : α)
  statement: sym (unsym a) = a
  proof: rfl

@[simp]

中文:
定理 sym_unsym
  条件: (a : α)
  结论: sym (unsym a) = a
  证明: rfl

@[simp]
-/
theorem sym_unsym (a : α) : sym (unsym a) = a :=
  rfl

@[simp]
/--
theorem `sym_comp_unsym` / 定理 `sym_comp_unsym`

English:
theorem sym_comp_unsym
  statement: (sym : α -> αˢʸᵐ) ∘ unsym = id
  proof: rfl

@[simp]

中文:
定理 sym_comp_unsym
  结论: (sym : α -> αˢʸᵐ) ∘ unsym = id
  证明: rfl

@[simp]
-/
theorem sym_comp_unsym : (sym : α -> αˢʸᵐ) ∘ unsym = id :=
  rfl

@[simp]
/--
theorem `unsym_comp_sym` / 定理 `unsym_comp_sym`

English:
theorem unsym_comp_sym
  statement: (unsym : αˢʸᵐ -> α) ∘ sym = id
  proof: rfl

@[simp]

中文:
定理 unsym_comp_sym
  结论: (unsym : αˢʸᵐ -> α) ∘ sym = id
  证明: rfl

@[simp]
-/
theorem unsym_comp_sym : (unsym : αˢʸᵐ -> α) ∘ sym = id :=
  rfl

@[simp]
/--
theorem `sym_symm` / 定理 `sym_symm`

English:
theorem sym_symm
  statement: (@sym α).symm = unsym
  proof: rfl

@[simp]

中文:
定理 sym_symm
  结论: (@sym α).symm = unsym
  证明: rfl

@[simp]

Depends on / 依赖: IsAffine, IsAffineHom, isAffineHom_of_isAffine
-/
theorem sym_symm : (@sym α).symm = unsym :=
  rfl

@[simp]
/--
theorem `unsym_symm` / 定理 `unsym_symm`

English:
theorem unsym_symm
  statement: (@unsym α).symm = sym
  proof: rfl

中文:
定理 unsym_symm
  结论: (@unsym α).symm = sym
  证明: rfl
-/
theorem unsym_symm : (@unsym α).symm = sym :=
  rfl

/--
theorem `sym_bijective` / 定理 `sym_bijective`

English:
theorem sym_bijective
  statement: Bijective (sym : α -> αˢʸᵐ)
  proof: sym.bijective

中文:
定理 sym_bijective
  结论: 双射 (sym : α -> αˢʸᵐ)
  证明: sym.bijective

Depends on / 依赖: bijective, sym.bijective
-/
theorem sym_bijective : Bijective (sym : α -> αˢʸᵐ) :=
  sym.bijective

/--
theorem `unsym_bijective` / 定理 `unsym_bijective`

English:
theorem unsym_bijective
  statement: Bijective (unsym : αˢʸᵐ -> α)
  proof: unsym.symm.bijective

中文:
定理 unsym_bijective
  结论: 双射 (unsym : αˢʸᵐ -> α)
  证明: unsym.symm.bijective

Depends on / 依赖: IsAffineHom, MorphismProperty, MorphismProperty.pullback_snd, bijective, isAffine_of_isAffineHom, pullback, pullback.snd, pullback_snd, unsym.symm.bijective
-/
theorem unsym_bijective : Bijective (unsym : αˢʸᵐ -> α) :=
  unsym.symm.bijective

/--
theorem `sym_injective` / 定理 `sym_injective`

English:
theorem sym_injective
  statement: Injective (sym : α -> αˢʸᵐ)
  proof: sym.injective

中文:
定理 sym_injective
  结论: 单射 (sym : α -> αˢʸᵐ)
  证明: sym.injective

Depends on / 依赖: IsAffineHom, MorphismProperty, MorphismProperty.pullback_fst, injective, isAffine_of_isAffineHom, pullback, pullback.fst, pullback_fst, sym.injective
-/
theorem sym_injective : Injective (sym : α -> αˢʸᵐ) :=
  sym.injective

/--
theorem `sym_surjective` / 定理 `sym_surjective`

English:
theorem sym_surjective
  statement: Surjective (sym : α -> αˢʸᵐ)
  proof: sym.surjective

中文:
定理 sym_surjective
  结论: 满射 (sym : α -> αˢʸᵐ)
  证明: sym.surjective

Depends on / 依赖: surjective, sym.surjective
-/
theorem sym_surjective : Surjective (sym : α -> αˢʸᵐ) :=
  sym.surjective

/--
theorem `unsym_injective` / 定理 `unsym_injective`

English:
theorem unsym_injective
  statement: Injective (unsym : αˢʸᵐ -> α)
  proof: unsym.injective

中文:
定理 unsym_injective
  结论: 单射 (unsym : αˢʸᵐ -> α)
  证明: unsym.injective

Depends on / 依赖: injective, unsym.injective
-/
theorem unsym_injective : Injective (unsym : αˢʸᵐ -> α) :=
  unsym.injective

/--
theorem `unsym_surjective` / 定理 `unsym_surjective`

English:
theorem unsym_surjective
  statement: Surjective (unsym : αˢʸᵐ -> α)
  proof: unsym.surjective

中文:
定理 unsym_surjective
  结论: 满射 (unsym : αˢʸᵐ -> α)
  证明: unsym.surjective

Depends on / 依赖: IsAffine, Scheme, Scheme.Hom.comp_apply, comp_apply, convert, coprod, coprod.map, coprodMk, hW.preimage, isAffineOpen_opensRange, le_antisymm, preimage, replace, surjective, toScheme, unsym.surjective
-/
theorem unsym_surjective : Surjective (unsym : αˢʸᵐ -> α) :=
  unsym.surjective

/--
theorem `sym_inj` / 定理 `sym_inj`

English:
theorem sym_inj
  given: {a b : α}
  statement: sym a = sym b ↔ a = b
  proof: sym_injective.eq_iff

中文:
定理 sym_inj
  条件: {a b : α}
  结论: sym a = sym b ↔ a = b
  证明: sym_injective.eq_iff

Depends on / 依赖: eq_iff, sym_injective, sym_injective.eq_iff
-/
theorem sym_inj {a b : α} : sym a = sym b ↔ a = b :=
  sym_injective.eq_iff

/--
theorem `unsym_inj` / 定理 `unsym_inj`

English:
theorem unsym_inj
  given: {a b : αˢʸᵐ}
  statement: unsym a = unsym b ↔ a = b
  proof: unsym_injective.eq_iff

中文:
定理 unsym_inj
  条件: {a b : αˢʸᵐ}
  结论: unsym a = unsym b ↔ a = b
  证明: unsym_injective.eq_iff

Depends on / 依赖: eq_iff, unsym_injective, unsym_injective.eq_iff
-/
theorem unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b :=
  unsym_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial αˢʸᵐ
  body: sym_injective.nontrivial

中文:
实例 [非平凡
  签名: α] : 非平凡 αˢʸᵐ
  定义体: sym_injective.nontrivial

Depends on / 依赖: nontrivial, sym_injective, sym_injective.nontrivial
-/
instance [Nontrivial α] : Nontrivial αˢʸᵐ :=
  sym_injective.nontrivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited αˢʸᵐ
  body: ⟨sym default⟩

中文:
实例 [可居
  签名: α] : 可居 αˢʸᵐ
  定义体: ⟨sym default⟩
-/
instance [Inhabited α] : Inhabited αˢʸᵐ :=
  ⟨sym default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton αˢʸᵐ
  body: unsym_injective.subsingleton

中文:
实例 [子单例
  签名: α] : 子单例 αˢʸᵐ
  定义体: unsym_injective.subsingleton

Depends on / 依赖: subsingleton, unsym_injective, unsym_injective.subsingleton
-/
instance [Subsingleton α] : Subsingleton αˢʸᵐ :=
  unsym_injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique αˢʸᵐ
  body: Unique.mk' _

中文:
实例 [唯一
  签名: α] : 唯一 αˢʸᵐ
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance [Unique α] : Unique αˢʸᵐ :=
  Unique.mk' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : IsEmpty αˢʸᵐ
  body: Function.isEmpty unsym

@[to_additive]

中文:
实例 [是空
  签名: α] : 是空 αˢʸᵐ
  定义体: Function.isEmpty unsym

@[to_additive]

Depends on / 依赖: Function, Function.isEmpty, isEmpty
-/
instance [IsEmpty α] : IsEmpty αˢʸᵐ :=
  Function.isEmpty unsym

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One αˢʸᵐ where one
  body: sym 1

中文:
实例 [幺
  签名: α] : 幺 αˢʸᵐ where one
  定义体: sym 1
-/
instance [One α] : One αˢʸᵐ where one := sym 1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] : Add αˢʸᵐ where add a b
  body: sym (unsym a + unsym b)

中文:
实例 [加法
  签名: α] : 加法 αˢʸᵐ where add a b
  定义体: sym (unsym a + unsym b)
-/
instance [Add α] : Add αˢʸᵐ where add a b := sym (unsym a + unsym b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Sub
  signature: α] : Sub αˢʸᵐ where sub a b
  body: sym (unsym a - unsym b)

中文:
实例 [减法
  签名: α] : 减法 αˢʸᵐ where sub a b
  定义体: sym (unsym a - unsym b)
-/
instance [Sub α] : Sub αˢʸᵐ where sub a b := sym (unsym a - unsym b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: α] : Neg αˢʸᵐ where neg a
  body: sym (-unsym a)

中文:
实例 [取负
  签名: α] : 取负 αˢʸᵐ where neg a
  定义体: sym (-unsym a)
-/
instance [Neg α] : Neg αˢʸᵐ where neg a := sym (-unsym a)

-- Introduce the symmetrized multiplication
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] : Mul αˢʸᵐ where
  body: sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]

中文:
实例 [加法
  签名: α] [乘法 α] [幺 α] [Of自然数 α 2] [可逆 (2 : α)] : 乘法 αˢʸᵐ where
  定义体: sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]
-/
instance [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] : Mul αˢʸᵐ where
  mul a b := sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv αˢʸᵐ where inv a
  body: sym (unsym a)⁻¹

中文:
实例 [取逆
  签名: α] : 取逆 αˢʸᵐ where inv a
  定义体: sym (unsym a)⁻¹
-/
instance [Inv α] : Inv αˢʸᵐ where inv a := sym (unsym a)⁻¹

instance (R : Type*) [SMul R α] : SMul R αˢʸᵐ where smul r a := sym (r • unsym a)

@[to_additive (attr := simp)]
/--
theorem `sym_one` / 定理 `sym_one`

English:
theorem sym_one
  given: [One α]
  statement: sym (1 : α) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 sym_one
  条件: [幺 α]
  结论: sym (1 : α) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem sym_one [One α] : sym (1 : α) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unsym_one` / 定理 `unsym_one`

English:
theorem unsym_one
  given: [One α]
  statement: unsym (1 : αˢʸᵐ) = 1
  proof: rfl

@[simp]

中文:
定理 unsym_one
  条件: [幺 α]
  结论: unsym (1 : αˢʸᵐ) = 1
  证明: rfl

@[simp]
-/
theorem unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1 :=
  rfl

@[simp]
/--
theorem `sym_add` / 定理 `sym_add`

English:
theorem sym_add
  given: [Add α] (a b : α)
  statement: sym (a + b) = sym a + sym b
  proof: rfl

@[simp]

中文:
定理 sym_add
  条件: [加法 α] (a b : α)
  结论: sym (a + b) = sym a + sym b
  证明: rfl

@[simp]
-/
theorem sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b :=
  rfl

@[simp]
/--
theorem `unsym_add` / 定理 `unsym_add`

English:
theorem unsym_add
  given: [Add α] (a b : αˢʸᵐ)
  statement: unsym (a + b) = unsym a + unsym b
  proof: rfl

@[simp]

中文:
定理 unsym_add
  条件: [加法 α] (a b : αˢʸᵐ)
  结论: unsym (a + b) = unsym a + unsym b
  证明: rfl

@[simp]
-/
theorem unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b :=
  rfl

@[simp]
/--
theorem `sym_sub` / 定理 `sym_sub`

English:
theorem sym_sub
  given: [Sub α] (a b : α)
  statement: sym (a - b) = sym a - sym b
  proof: rfl

@[simp]

中文:
定理 sym_sub
  条件: [减法 α] (a b : α)
  结论: sym (a - b) = sym a - sym b
  证明: rfl

@[simp]
-/
theorem sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b :=
  rfl

@[simp]
/--
theorem `unsym_sub` / 定理 `unsym_sub`

English:
theorem unsym_sub
  given: [Sub α] (a b : αˢʸᵐ)
  statement: unsym (a - b) = unsym a - unsym b
  proof: rfl

@[simp]

中文:
定理 unsym_sub
  条件: [减法 α] (a b : αˢʸᵐ)
  结论: unsym (a - b) = unsym a - unsym b
  证明: rfl

@[simp]
-/
theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b :=
  rfl

@[simp]
/--
theorem `sym_neg` / 定理 `sym_neg`

English:
theorem sym_neg
  given: [Neg α] (a : α)
  statement: sym (-a) = -sym a
  proof: rfl

@[simp]

中文:
定理 sym_neg
  条件: [取负 α] (a : α)
  结论: sym (-a) = -sym a
  证明: rfl

@[simp]
-/
theorem sym_neg [Neg α] (a : α) : sym (-a) = -sym a :=
  rfl

@[simp]
/--
theorem `unsym_neg` / 定理 `unsym_neg`

English:
theorem unsym_neg
  given: [Neg α] (a : αˢʸᵐ)
  statement: unsym (-a) = -unsym a
  proof: rfl

中文:
定理 unsym_neg
  条件: [取负 α] (a : αˢʸᵐ)
  结论: unsym (-a) = -unsym a
  证明: rfl
-/
theorem unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ)
  proof: rfl

中文:
定理 mul_def
  条件: [加法 α] [乘法 α] [幺 α] [Of自然数 α 2] [可逆 (2 : α)] (a b : αˢʸᵐ)
  证明: rfl
-/
theorem mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a)) := rfl

/--
theorem `unsym_mul` / 定理 `unsym_mul`

English:
theorem unsym_mul
  given: [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ)
  proof: rfl

中文:
定理 unsym_mul
  条件: [乘法 α] [加法 α] [幺 α] [Of自然数 α 2] [可逆 (2 : α)] (a b : αˢʸᵐ)
  证明: rfl
-/
theorem unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    unsym (a * b) = ⅟2 * (unsym a * unsym b + unsym b * unsym a) := rfl

/--
theorem `sym_mul_sym` / 定理 `sym_mul_sym`

English:
theorem sym_mul_sym
  given: [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α)
  proof: rfl

@[simp, to_additive existing]

中文:
定理 sym_mul_sym
  条件: [乘法 α] [加法 α] [幺 α] [Of自然数 α 2] [可逆 (2 : α)] (a b : α)
  证明: rfl

@[simp, to_additive existing]
-/
theorem sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α) :
    sym a * sym b = sym (⅟2 * (a * b + b * a)) :=
  rfl

@[simp, to_additive existing]
/--
theorem `sym_inv` / 定理 `sym_inv`

English:
theorem sym_inv
  given: [Inv α] (a : α)
  statement: sym a⁻¹ = (sym a)⁻¹
  proof: rfl

@[simp, to_additive existing]

中文:
定理 sym_inv
  条件: [取逆 α] (a : α)
  结论: sym a⁻¹ = (sym a)⁻¹
  证明: rfl

@[simp, to_additive existing]
-/
theorem sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹ :=
  rfl

@[simp, to_additive existing]
/--
theorem `unsym_inv` / 定理 `unsym_inv`

English:
theorem unsym_inv
  given: [Inv α] (a : αˢʸᵐ)
  statement: unsym a⁻¹ = (unsym a)⁻¹
  proof: rfl

@[simp]

中文:
定理 unsym_inv
  条件: [取逆 α] (a : αˢʸᵐ)
  结论: unsym a⁻¹ = (unsym a)⁻¹
  证明: rfl

@[simp]
-/
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹ :=
  rfl

@[simp]
/--
theorem `sym_smul` / 定理 `sym_smul`

English:
theorem sym_smul
  given: {R : Type*} [SMul R α] (c : R) (a : α)
  statement: sym (c • a) = c • sym a
  proof: rfl

@[simp]

中文:
定理 sym_smul
  条件: {R : 类型} [标量乘法 R α] (c : R) (a : α)
  结论: sym (c • a) = c • sym a
  证明: rfl

@[simp]
-/
theorem sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : sym (c • a) = c • sym a :=
  rfl

@[simp]
/--
theorem `unsym_smul` / 定理 `unsym_smul`

English:
theorem unsym_smul
  given: {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ)
  statement: unsym (c • a) = c • unsym a
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unsym_smul
  条件: {R : 类型} [标量乘法 R α] (c : R) (a : αˢʸᵐ)
  结论: unsym (c • a) = c • unsym a
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c • unsym a :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unsym_eq_one_iff` / 定理 `unsym_eq_one_iff`

English:
theorem unsym_eq_one_iff
  given: [One α] (a : αˢʸᵐ)
  statement: unsym a = 1 ↔ a = 1
  proof: unsym_injective.eq_iff' rfl

@[to_additive (attr := simp)]

中文:
定理 unsym_eq_one_iff
  条件: [幺 α] (a : αˢʸᵐ)
  结论: unsym a = 1 ↔ a = 1
  证明: unsym_injective.eq_iff' rfl

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, unsym_injective, unsym_injective.eq_iff
-/
theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a = 1 ↔ a = 1 :=
  unsym_injective.eq_iff' rfl

@[to_additive (attr := simp)]
/--
theorem `sym_eq_one_iff` / 定理 `sym_eq_one_iff`

English:
theorem sym_eq_one_iff
  given: [One α] (a : α)
  statement: sym a = 1 ↔ a = 1
  proof: sym_injective.eq_iff' rfl

@[to_additive]

中文:
定理 sym_eq_one_iff
  条件: [幺 α] (a : α)
  结论: sym a = 1 ↔ a = 1
  证明: sym_injective.eq_iff' rfl

@[to_additive]

Depends on / 依赖: eq_iff, sym_injective, sym_injective.eq_iff
-/
theorem sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1 :=
  sym_injective.eq_iff' rfl

@[to_additive]
/--
theorem `unsym_ne_one_iff` / 定理 `unsym_ne_one_iff`

English:
theorem unsym_ne_one_iff
  given: [One α] (a : αˢʸᵐ)
  statement: unsym a != (1 : α) ↔ a != (1 : αˢʸᵐ)
  proof: not_congr unsym_eq_one_iff a

@[to_additive]

中文:
定理 unsym_ne_one_iff
  条件: [幺 α] (a : αˢʸᵐ)
  结论: unsym a != (1 : α) ↔ a != (1 : αˢʸᵐ)
  证明: not_congr unsym_eq_one_iff a

@[to_additive]

Depends on / 依赖: not_congr, unsym_eq_one_iff
-/
theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : unsym a != (1 : α) ↔ a != (1 : αˢʸᵐ) :=
not_congr unsym_eq_one_iff a

@[to_additive]
/--
theorem `sym_ne_one_iff` / 定理 `sym_ne_one_iff`

English:
theorem sym_ne_one_iff
  given: [One α] (a : α)
  statement: sym a != (1 : αˢʸᵐ) ↔ a != (1 : α)
  proof: not_congr sym_eq_one_iff a

中文:
定理 sym_ne_one_iff
  条件: [幺 α] (a : α)
  结论: sym a != (1 : αˢʸᵐ) ↔ a != (1 : α)
  证明: not_congr sym_eq_one_iff a

Depends on / 依赖: not_congr, sym_eq_one_iff
-/
theorem sym_ne_one_iff [One α] (a : α) : sym a != (1 : αˢʸᵐ) ↔ a != (1 : α) :=
not_congr sym_eq_one_iff a

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: [AddCommSemigroup α]
  body: unsym_injective.addCommSemigroup _ unsym_add

中文:
实例 addCommSemigroup
  签名: [加法交换半群 α]
  定义体: unsym_injective.addCommSemigroup _ unsym_add

Depends on / 依赖: addCommSemigroup, unsym_add, unsym_injective, unsym_injective.addCommSemigroup
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ :=
  unsym_injective.addCommSemigroup _ unsym_add

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: [AddMonoid α]
  body: unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl

中文:
实例 addMonoid
  签名: [加法幺半群 α]
  定义体: unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl

Depends on / 依赖: addMonoid, unsym_add, unsym_injective, unsym_injective.addMonoid, unsym_zero
-/
instance addMonoid [AddMonoid α] : AddMonoid αˢʸᵐ :=
  unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: [AddGroup α]
  body: unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl

中文:
实例 addGroup
  签名: [加法群 α]
  定义体: unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl

Depends on / 依赖: addGroup, unsym_add, unsym_injective, unsym_injective.addGroup, unsym_neg, unsym_sub, unsym_zero
-/
instance addGroup [AddGroup α] : AddGroup αˢʸᵐ :=
  unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [AddCommMonoid α]
  body: { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

中文:
实例 addCommMonoid
  签名: [加法交换幺半群 α]
  定义体: { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

Depends on / 依赖: SymAlg, SymAlg.addCommSemigroup, SymAlg.addMonoid, addCommSemigroup, addMonoid
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid αˢʸᵐ :=
  { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: [AddCommGroup α]
  body: { SymAlg.addCommMonoid, SymAlg.addGroup with }

中文:
实例 addCommGroup
  签名: [加法交换群 α]
  定义体: { SymAlg.addCommMonoid, SymAlg.addGroup with }

Depends on / 依赖: SymAlg, SymAlg.addCommMonoid, SymAlg.addGroup, addCommMonoid, addGroup
-/
instance addCommGroup [AddCommGroup α] : AddCommGroup αˢʸᵐ :=
  { SymAlg.addCommMonoid, SymAlg.addGroup with }

instance {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] : Module R αˢʸᵐ :=
  Function.Injective.module R ⟨⟨unsym, unsym_zero⟩, unsym_add⟩ unsym_injective unsym_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [AddMonoidWithOne α] [Invertible (2 : α)] (a
  body: sym (⅟a)
  invOf_mul_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]
  mul_invOf_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]

中文:
实例 [乘法
  签名: α] [加法带幺幺半群 α] [可逆 (2 : α)] (a
  定义体: sym (⅟a)
  invOf_mul_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]
  mul_invOf_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]
-/
instance [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    Invertible (sym a) where
  invOf := sym (⅟a)
  invOf_mul_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]
  mul_invOf_self := by
    rw [sym_mul_sym]; rw [mul_invOf_self]; rw [invOf_mul_self]; rw [one_add_one_eq_two]; rw [invOf_mul_self]; rw [sym_one]

@[simp]
/--
theorem `invOf_sym` / 定理 `invOf_sym`

English:
theorem invOf_sym
  given: [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a]
  proof: rfl

中文:
定理 invOf_sym
  条件: [乘法 α] [加法带幺幺半群 α] [可逆 (2 : α)] (a : α) [可逆 a]
  证明: rfl
-/
theorem invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    ⅟(sym a) = sym (⅟a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `nonAssocSemiring` / 实例 `nonAssocSemiring`

English:
instance nonAssocSemiring
  signature: [Semiring α] [Invertible (2 : α)]
  body: { SymAlg.addCommMonoid with
    zero_mul := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_zero]
    mul_zero := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_

中文:
实例 nonAssocSemiring
  签名: [半环 α] [可逆 (2 : α)]
  定义体: { SymAlg.addCommMonoid with
    zero_mul := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_zero]
    mul_zero := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_

Depends on / 依赖: SymAlg, SymAlg.addCommMonoid, addCommMonoid, add_zero, invOf_mul_cancel_left, mul_def, mul_one, mul_zero, one_mul, sym_unsym, sym_zero, two_mul, unsym_one, unsym_zero, zero_mul
-/
instance nonAssocSemiring [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ :=
  { SymAlg.addCommMonoid with
    zero_mul := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_zero]
    mul_zero := fun _ => by
      rw [mul_def]; rw [unsym_zero]; rw [zero_mul]; rw [mul_zero]; rw [add_zero]; rw [mul_zero]; rw [sym_zero]
    mul_one := fun _ => by
      rw [mul_def]; rw [unsym_one]; rw [mul_one]; rw [one_mul]; rw [← two_mul]; rw [invOf_mul_cancel_left]; rw [sym_unsym]
    one_mul := fun _ => by
      rw [mul_def]; rw [unsym_one]; rw [mul_one]; rw [one_mul]; rw [← two_mul]; rw [invOf_mul_cancel_left]; rw [sym_unsym]
    left_distrib := fun a b c => by
      rw [mul_def]; rw [mul_def]; rw [mul_def]; rw [← sym_add]; rw [← mul_add]; rw [unsym_add]; rw [add_mul]
      congr 2
      rw [mul_add]
      abel
    right_distrib := fun a b c => by
      rw [mul_def]; rw [mul_def]; rw [mul_def]; rw [← sym_add]; rw [← mul_add]; rw [unsym_add]; rw [add_mul]
      congr 2
      rw [mul_add]
      abel }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ
  body: { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

中文:
实例 [环
  签名: α] [可逆 (2 : α)] : 非结合环 αˢʸᵐ
  定义体: { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

Depends on / 依赖: SymAlg, SymAlg.addCommGroup, SymAlg.nonAssocSemiring, addCommGroup, nonAssocSemiring
-/
instance [Ring α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ :=
  { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }



/--
theorem `unsym_mul_self` / 定理 `unsym_mul_self`

English:
theorem unsym_mul_self
  given: [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ)
  proof: by
  rw [mul_def]; rw [unsym_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

中文:
定理 unsym_mul_self
  条件: [半环 α] [可逆 (2 : α)] (a : αˢʸᵐ)
  证明: by
  rw [mul_def]; rw [unsym_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

Depends on / 依赖: invOf_mul_cancel_left, mul_def, two_mul, unsym_sym
-/
theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) :
    unsym (a * a) = unsym a * unsym a := by
  rw [mul_def]; rw [unsym_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

/--
theorem `sym_mul_self` / 定理 `sym_mul_self`

English:
theorem sym_mul_self
  given: [Semiring α] [Invertible (2 : α)] (a : α)
  statement: sym (a * a) = sym a * sym a
  proof: by
  rw [sym_mul_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

中文:
定理 sym_mul_self
  条件: [半环 α] [可逆 (2 : α)] (a : α)
  结论: sym (a * a) = sym a * sym a
  证明: by
  rw [sym_mul_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

Depends on / 依赖: invOf_mul_cancel_left, sym_mul_sym, two_mul
-/
theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym a * sym a := by
  rw [sym_mul_sym]; rw [← two_mul]; rw [invOf_mul_cancel_left]

/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
  proof: by rw [mul_def, mul_def, add_comm]

中文:
定理 mul_comm
  结论: [乘法 α] [加法交换半群 α] [幺 α] [Of自然数 α 2] [可逆 (2 : α)]
  证明: by rw [mul_def, mul_def, add_comm]

Depends on / 依赖: add_comm, mul_def
-/
theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
    (a b : αˢʸᵐ) :
    a * b = b * a := by rw [mul_def, mul_def, add_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: α] [Invertible (2 : α)] : CommMagma αˢʸᵐ where
  body: SymAlg.mul_comm

中文:
实例 [环
  签名: α] [可逆 (2 : α)] : 交换原群 αˢʸᵐ where
  定义体: SymAlg.mul_comm

Depends on / 依赖: SymAlg, SymAlg.mul_comm, mul_comm
-/
instance [Ring α] [Invertible (2 : α)] : CommMagma αˢʸᵐ where
  mul_comm := SymAlg.mul_comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  body: by
    have commute_half_left := fun a : α => by
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * 

中文:
实例 [环
  签名: α] [可逆 (2 : α)] : 是交换Jordan αˢʸᵐ where
  定义体: by
    have commute_half_left := fun a : α => by
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * 

Depends on / 依赖: Commute, Commute.one_left, add_left, commute_half_left, invOf_left, one_add_one_eq_two, one_left, this.invOf_left.eq
-/
instance [Ring α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  lmul_comm_rmul_rmul a b := by
    have commute_half_left := fun a : α => by
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * unsym (a * a) +
          unsym (a * a) * unsym a * unsym b +
          unsym (a * a) * unsym b * unsym a)) := ?_
      _ = sym (⅟2 * (unsym a *
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) +
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) * unsym a)) := ?_
      _ = a * (b * (a * a)) := ?_
    -- Rearrange LHS
    · rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a * a)),
        mul_assoc, mul_assoc, ← mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)),
        ← add_assoc, ← mul_assoc, ← mul_assoc]
    · rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟2) (unsym a),
        mul_assoc (⅟2) _ (unsym a), ← mul_add, ← mul_assoc]
      conv_rhs => rw [mul_add (unsym a)]
      rw [add_mul]; rw [← add_assoc]; rw [← mul_assoc]; rw [← mul_assoc]
      rw [unsym_mul_self]
      rw [← mul_assoc]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← sub_eq_zero]; rw [← mul_sub]
      convert! mul_zero (⅟(2 : α) * ⅟(2 : α))
      rw [add_sub_add_right_eq_sub]; rw [add_assoc]; rw [add_assoc]; rw [add_sub_add_left_eq_sub]; rw [add_comm]; rw [add_sub_add_right_eq_sub]; rw [sub_eq_zero]
    -- Rearrange RHS
    · rw [← mul_def, ← mul_def]

end SymAlg
