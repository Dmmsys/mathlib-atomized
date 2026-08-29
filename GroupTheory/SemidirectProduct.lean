/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `fn : N →* H` and `fg : G →* H` that satisfy the
condition `∀ n g, fn (φ g n) = fg g * fn n * fg g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `SemidirectProduct N G φ`

## Tags
group, semidirect product
-/

@[expose] public section

open Subgroup

variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]

-- Don't generate sizeOf and injectivity lemmas, which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It is the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext]
/--
Definition of `SemidirectProduct` / `SemidirectProduct` 的定义

English:
structure SemidirectProduct
  parameters: (φ : G ->* MulAut N)
  axioms and operations (2):
    - left : N
    - right : G

中文:
结构 SemidirectProduct
  参数: (φ : G ->* MulAut N)
  公理与运算 (2 个):
    - left : N
    - right : G
-/
structure SemidirectProduct (φ : G ->* MulAut N) where
  /-- The element of N -/
  left : N
  /-- The element of G -/
  right : G
  deriving DecidableEq

attribute [pp_using_anonymous_constructor] SemidirectProduct

@[inherit_doc]
notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable {N G}
variable {φ : G ->* MulAut N}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (SemidirectProduct N G φ)
  body: ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩

中文:
实例 :
  签名: Mul (SemidirectProduct N G φ)
  定义体: ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩
-/
instance : Mul (SemidirectProduct N G φ) where
  mul a b := ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (a b : SemidirectProduct N G φ)
  statement: a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩
  proof: rfl

@[simp]

中文:
引理 mul_def
  条件: (a b : SemidirectProduct N G φ)
  结论: a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩
  证明: rfl

@[simp]
-/
lemma mul_def (a b : SemidirectProduct N G φ) : a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩ := rfl

@[simp]
/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (a b : N ⋊[φ] G)
  statement: (a * b).left = a.left * φ a.right b.left
  proof: rfl

@[simp]

中文:
定理 mul_left
  条件: (a b : N ⋊[φ] G)
  结论: (a * b).left = a.left * φ a.right b.left
  证明: rfl

@[simp]
-/
theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left := rfl

@[simp]
/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (a b : N ⋊[φ] G)
  statement: (a * b).right = a.right * b.right
  proof: rfl

中文:
定理 mul_right
  条件: (a b : N ⋊[φ] G)
  结论: (a * b).right = a.right * b.right
  证明: rfl
-/
theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (SemidirectProduct N G φ)
  body: ⟨1, 1⟩

@[simp]

中文:
实例 :
  签名: One (SemidirectProduct N G φ)
  定义体: ⟨1, 1⟩

@[simp]
-/
instance : One (SemidirectProduct N G φ) where one := ⟨1, 1⟩

@[simp]
/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  statement: (1 : N ⋊[φ] G).left = 1
  proof: rfl

@[simp]

中文:
定理 one_left
  结论: (1 : N ⋊[φ] G).left = 1
  证明: rfl

@[simp]
-/
theorem one_left : (1 : N ⋊[φ] G).left = 1 := rfl

@[simp]
/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  statement: (1 : N ⋊[φ] G).right = 1
  proof: rfl

中文:
定理 one_right
  结论: (1 : N ⋊[φ] G).right = 1
  证明: rfl
-/
theorem one_right : (1 : N ⋊[φ] G).right = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (SemidirectProduct N G φ)
  body: ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩

@[simp]

中文:
实例 :
  签名: Inv (SemidirectProduct N G φ)
  定义体: ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩

@[simp]
-/
instance : Inv (SemidirectProduct N G φ) where
  inv x := ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩

@[simp]
/--
theorem `inv_left` / 定理 `inv_left`

English:
theorem inv_left
  given: (a : N ⋊[φ] G)
  statement: a⁻¹.left = φ a.right⁻¹ a.left⁻¹
  proof: rfl

@[simp]

中文:
定理 inv_left
  条件: (a : N ⋊[φ] G)
  结论: a⁻¹.left = φ a.right⁻¹ a.left⁻¹
  证明: rfl

@[simp]
-/
theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹ := rfl

@[simp]
/--
theorem `inv_right` / 定理 `inv_right`

English:
theorem inv_right
  given: (a : N ⋊[φ] G)
  statement: a⁻¹.right = a.right⁻¹
  proof: rfl

中文:
定理 inv_right
  条件: (a : N ⋊[φ] G)
  结论: a⁻¹.right = a.right⁻¹
  证明: rfl
-/
theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (N ⋊[φ] G)
  body: SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)

中文:
实例 :
  签名: Group (N ⋊[φ] G)
  定义体: SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)

Depends on / 依赖: SemidirectProduct, SemidirectProduct.ext, mul_assoc
-/
instance : Group (N ⋊[φ] G) where
  mul_assoc a b c := SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (N ⋊[φ] G)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (N ⋊[φ] G)
  定义体: ⟨1⟩
-/
instance : Inhabited (N ⋊[φ] G) := ⟨1⟩

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : N ->* N ⋊[φ] G where
  body: ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]

@[simp]

中文:
定义 inl
  签名: : N ->* N ⋊[φ] G where
  定义体: ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]

@[simp]
-/
def inl : N ->* N ⋊[φ] G where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]

@[simp]
/--
theorem `left_inl` / 定理 `left_inl`

English:
theorem left_inl
  given: (n : N)
  statement: (inl n : N ⋊[φ] G).left = n
  proof: rfl

@[simp]

中文:
定理 left_inl
  条件: (n : N)
  结论: (inl n : N ⋊[φ] G).left = n
  证明: rfl

@[simp]
-/
theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n := rfl

@[simp]
/--
theorem `right_inl` / 定理 `right_inl`

English:
theorem right_inl
  given: (n : N)
  statement: (inl n : N ⋊[φ] G).right = 1
  proof: rfl

中文:
定理 right_inl
  条件: (n : N)
  结论: (inl n : N ⋊[φ] G).right = 1
  证明: rfl
-/
theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 := rfl

/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Function.Injective (inl : N -> N ⋊[φ] G)
  proof: Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩

@[simp]

中文:
定理 inl_injective
  结论: Function.Injective (inl : N -> N ⋊[φ] G)
  证明: Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩

@[simp]

Depends on / 依赖: Function, Function.injective_iff_hasLeftInverse, injective_iff_hasLeftInverse, left_inl
-/
theorem inl_injective : Function.Injective (inl : N -> N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩

@[simp]
/--
theorem `inl_inj` / 定理 `inl_inj`

English:
theorem inl_inj
  given: {n₁ n₂ : N}
  statement: (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂
  proof: inl_injective.eq_iff

中文:
定理 inl_inj
  条件: {n₁ n₂ : N}
  结论: (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂
  证明: inl_injective.eq_iff

Depends on / 依赖: eq_iff, inl_injective, inl_injective.eq_iff
-/
theorem inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
  inl_injective.eq_iff

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : G ->* N ⋊[φ] G where
  body: ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp

@[simp]

中文:
定义 inr
  签名: : G ->* N ⋊[φ] G where
  定义体: ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp

@[simp]
-/
def inr : G ->* N ⋊[φ] G where
  toFun g := ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp

@[simp]
/--
theorem `left_inr` / 定理 `left_inr`

English:
theorem left_inr
  given: (g : G)
  statement: (inr g : N ⋊[φ] G).left = 1
  proof: rfl

@[simp]

中文:
定理 left_inr
  条件: (g : G)
  结论: (inr g : N ⋊[φ] G).left = 1
  证明: rfl

@[simp]
-/
theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 := rfl

@[simp]
/--
theorem `right_inr` / 定理 `right_inr`

English:
theorem right_inr
  given: (g : G)
  statement: (inr g : N ⋊[φ] G).right = g
  proof: rfl

中文:
定理 right_inr
  条件: (g : G)
  结论: (inr g : N ⋊[φ] G).right = g
  证明: rfl
-/
theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g := rfl

/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Function.Injective (inr : G -> N ⋊[φ] G)
  proof: Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩

@[simp]

中文:
定理 inr_injective
  结论: Function.Injective (inr : G -> N ⋊[φ] G)
  证明: Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩

@[simp]

Depends on / 依赖: Function, Function.injective_iff_hasLeftInverse, injective_iff_hasLeftInverse, right_inr
-/
theorem inr_injective : Function.Injective (inr : G -> N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩

@[simp]
/--
theorem `inr_inj` / 定理 `inr_inj`

English:
theorem inr_inj
  given: {g₁ g₂ : G}
  statement: (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂
  proof: inr_injective.eq_iff

中文:
定理 inr_inj
  条件: {g₁ g₂ : G}
  结论: (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂
  证明: inr_injective.eq_iff

Depends on / 依赖: eq_iff, inr_injective, inr_injective.eq_iff
-/
theorem inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
  inr_injective.eq_iff

/--
theorem `inl_aut` / 定理 `inl_aut`

English:
theorem inl_aut
  given: (g : G) (n : N)
  statement: (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹
  proof: by
  ext <;> simp

中文:
定理 inl_aut
  条件: (g : G) (n : N)
  结论: (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹
  证明: by
  ext <;> simp
-/
theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ := by
  ext <;> simp

/--
theorem `inl_aut_inv` / 定理 `inl_aut_inv`

English:
theorem inl_aut_inv
  given: (g : G) (n : N)
  statement: (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g
  proof: by
  rw [← map_inv]; rw [inl_aut]; rw [inv_inv]

@[simp]

中文:
定理 inl_aut_inv
  条件: (g : G) (n : N)
  结论: (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g
  证明: by
  rw [← map_inv]; rw [inl_aut]; rw [inv_inv]

@[simp]

Depends on / 依赖: inl_aut, inv_inv, map_inv
-/
theorem inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g := by
  rw [← map_inv]; rw [inl_aut]; rw [inv_inv]

@[simp]
/--
theorem `mk_eq_inl_mul_inr` / 定理 `mk_eq_inl_mul_inr`

English:
theorem mk_eq_inl_mul_inr
  given: (g : G) (n : N)
  statement: (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
  proof: by ext <;> simp

@[simp]

中文:
定理 mk_eq_inl_mul_inr
  条件: (g : G) (n : N)
  结论: (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g
  证明: by ext <;> simp

@[simp]
-/
theorem mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g := by ext <;> simp

@[simp]
/--
theorem `inl_left_mul_inr_right` / 定理 `inl_left_mul_inr_right`

English:
theorem inl_left_mul_inr_right
  given: (x : N ⋊[φ] G)
  statement: inl x.left * inr x.right = x
  proof: by ext <;> simp

中文:
定理 inl_left_mul_inr_right
  条件: (x : N ⋊[φ] G)
  结论: inl x.left * inr x.right = x
  证明: by ext <;> simp
-/
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x := by ext <;> simp

/--
Definition of `rightHom` / `rightHom` 的定义

English:
definition rightHom
  signature: : N ⋊[φ] G ->* G where
  body: SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 rightHom
  签名: : N ⋊[φ] G ->* G where
  定义体: SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: SemidirectProduct, SemidirectProduct.right
-/
def rightHom : N ⋊[φ] G ->* G where
  toFun := SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
theorem `rightHom_eq_right` / 定理 `rightHom_eq_right`

English:
theorem rightHom_eq_right
  statement: (rightHom : N ⋊[φ] G -> G) = right
  proof: rfl

@[simp]

中文:
定理 rightHom_eq_right
  结论: (rightHom : N ⋊[φ] G -> G) = right
  证明: rfl

@[simp]
-/
theorem rightHom_eq_right : (rightHom : N ⋊[φ] G -> G) = right := rfl

@[simp]
/--
theorem `rightHom_comp_inl` / 定理 `rightHom_comp_inl`

English:
theorem rightHom_comp_inl
  statement: (rightHom : N ⋊[φ] G ->* G).comp inl = 1
  proof: by ext; simp [rightHom]

@[simp]

中文:
定理 rightHom_comp_inl
  结论: (rightHom : N ⋊[φ] G ->* G).comp inl = 1
  证明: by ext; simp [rightHom]

@[simp]

Depends on / 依赖: rightHom
-/
theorem rightHom_comp_inl : (rightHom : N ⋊[φ] G ->* G).comp inl = 1 := by ext; simp [rightHom]

@[simp]
/--
theorem `rightHom_comp_inr` / 定理 `rightHom_comp_inr`

English:
theorem rightHom_comp_inr
  statement: (rightHom : N ⋊[φ] G ->* G).comp inr = MonoidHom.id _
  proof: by
  ext; simp [rightHom]

@[simp]

中文:
定理 rightHom_comp_inr
  结论: (rightHom : N ⋊[φ] G ->* G).comp inr = MonoidHom.id _
  证明: by
  ext; simp [rightHom]

@[simp]

Depends on / 依赖: rightHom
-/
theorem rightHom_comp_inr : (rightHom : N ⋊[φ] G ->* G).comp inr = MonoidHom.id _ := by
  ext; simp [rightHom]

@[simp]
/--
theorem `rightHom_inl` / 定理 `rightHom_inl`

English:
theorem rightHom_inl
  given: (n : N)
  statement: rightHom (inl n : N ⋊[φ] G) = 1
  proof: by simp [rightHom]

@[simp]

中文:
定理 rightHom_inl
  条件: (n : N)
  结论: rightHom (inl n : N ⋊[φ] G) = 1
  证明: by simp [rightHom]

@[simp]

Depends on / 依赖: rightHom
-/
theorem rightHom_inl (n : N) : rightHom (inl n : N ⋊[φ] G) = 1 := by simp [rightHom]

@[simp]
/--
theorem `rightHom_inr` / 定理 `rightHom_inr`

English:
theorem rightHom_inr
  given: (g : G)
  statement: rightHom (inr g : N ⋊[φ] G) = g
  proof: by simp [rightHom]

中文:
定理 rightHom_inr
  条件: (g : G)
  结论: rightHom (inr g : N ⋊[φ] G) = g
  证明: by simp [rightHom]

Depends on / 依赖: isSymmOp_of_isCommutative, rightHom
-/
theorem rightHom_inr (g : G) : rightHom (inr g : N ⋊[φ] G) = g := by simp [rightHom]

/--
theorem `rightHom_surjective` / 定理 `rightHom_surjective`

English:
theorem rightHom_surjective
  statement: Function.Surjective (rightHom : N ⋊[φ] G -> G)
  proof: Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩

中文:
定理 rightHom_surjective
  结论: Function.Surjective (rightHom : N ⋊[φ] G -> G)
  证明: Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩

Depends on / 依赖: Function, Function.surjective_iff_hasRightInverse, rightHom_inr, surjective_iff_hasRightInverse
-/
theorem rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G -> G) :=
  Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩

/--
theorem `range_inl_eq_ker_rightHom` / 定理 `range_inl_eq_ker_rightHom`

English:
theorem range_inl_eq_ker_rightHom
  statement: (inl : N ->* N ⋊[φ] G).range = rightHom.ker
  proof: le_antisymm (fun _ => by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx => ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩

中文:
定理 range_inl_eq_ker_rightHom
  结论: (inl : N ->* N ⋊[φ] G).range = rightHom.ker
  证明: le_antisymm (fun _ => by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx => ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, contextual, eq_comm, h.left_comm, le_antisymm, left_comm, mem_ker, x.left
-/
theorem range_inl_eq_ker_rightHom : (inl : N ->* N ⋊[φ] G).range = rightHom.ker :=
  le_antisymm (fun _ => by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx => ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩

/-- The bijection between the semidirect product and the product. -/
@[simps]
/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: : N ⋊[φ] G ≃ N × G where
  body: ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

中文:
定义 equivProd
  签名: : N ⋊[φ] G ≃ N × G where
  定义体: ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

Depends on / 依赖: h.right_comm, right_comm
-/
def equivProd : N ⋊[φ] G ≃ N × G where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/-- The group isomorphism between a semidirect product with respect to the trivial map
  and the product. -/
@[simps (rhsMd := .default)]
/--
Definition of `mulEquivProd` / `mulEquivProd` 的定义

English:
definition mulEquivProd
  signature: : N ⋊[1] G ≃* N × G
  body: { equivProd with map_mul' _ _ := rfl }

中文:
定义 mulEquivProd
  签名: : N ⋊[1] G ≃* N × G
  定义体: { equivProd with map_mul' _ _ := rfl }

Depends on / 依赖: equivProd, ha.assoc, hc.comm, map_mul
-/
def mulEquivProd : N ⋊[1] G ≃* N × G :=
  { equivProd with map_mul' _ _ := rfl }

section lift

variable (fn : N ->* H) (fg : G ->* H)
  (h : forall g, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : N ⋊[φ] G ->* H where
  body: fn a.1 * fg a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g => DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]

@[simp]

中文:
定义 lift
  签名: : N ⋊[φ] G ->* H where
  定义体: fn a.1 * fg a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g => DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]

@[simp]

Depends on / 依赖: ha.assoc, hc.comm
-/
def lift : N ⋊[φ] G ->* H where
  toFun a := fn a.1 * fg a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g => DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]

@[simp]
/--
theorem `lift_inl` / 定理 `lift_inl`

English:
theorem lift_inl
  given: (n : N)
  statement: lift fn fg h (inl n) = fn n
  proof: by simp [lift]

@[simp]

中文:
定理 lift_inl
  条件: (n : N)
  结论: lift fn fg h (inl n) = fn n
  证明: by simp [lift]

@[simp]
-/
theorem lift_inl (n : N) : lift fn fg h (inl n) = fn n := by simp [lift]

@[simp]
/--
theorem `lift_comp_inl` / 定理 `lift_comp_inl`

English:
theorem lift_comp_inl
  statement: (lift fn fg h).comp inl = fn
  proof: by ext; simp

@[simp]

中文:
定理 lift_comp_inl
  结论: (lift fn fg h).comp inl = fn
  证明: by ext; simp

@[simp]
-/
theorem lift_comp_inl : (lift fn fg h).comp inl = fn := by ext; simp

@[simp]
/--
theorem `lift_inr` / 定理 `lift_inr`

English:
theorem lift_inr
  given: (g : G)
  statement: lift fn fg h (inr g) = fg g
  proof: by simp [lift]

@[simp]

中文:
定理 lift_inr
  条件: (g : G)
  结论: lift fn fg h (inr g) = fg g
  证明: by simp [lift]

@[simp]
-/
theorem lift_inr (g : G) : lift fn fg h (inr g) = fg g := by simp [lift]

@[simp]
/--
theorem `lift_comp_inr` / 定理 `lift_comp_inr`

English:
theorem lift_comp_inr
  statement: (lift fn fg h).comp inr = fg
  proof: by ext; simp

中文:
定理 lift_comp_inr
  结论: (lift fn fg h).comp inr = fg
  证明: by ext; simp
-/
theorem lift_comp_inr : (lift fn fg h).comp inr = fg := by ext; simp

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (F : N ⋊[φ] G ->* H)
  proof: by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]

中文:
定理 lift_unique
  条件: (F : N ⋊[φ] G ->* H)
  证明: by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, MonoidHom, MonoidHom.coe_mk, MonoidHom.comp_apply, OneHom, OneHom.coe_mk, coe_mk, comp_apply, ext_iff, forall_const, inl_left_mul_inr_right, map_mul
-/
theorem lift_unique (F : N ⋊[φ] G ->* H) :
    F = lift (F.comp inl) (F.comp inr) fun _ => by ext; simp [inl_aut] := by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : N ⋊[φ] G ->* H} (hl : f.comp inl = g.comp inl)
  proof: by
  rw [lift_unique f]; rw [lift_unique g]
  simp only [*]

中文:
定理 hom_ext
  结论: {f g : N ⋊[φ] G ->* H} (hl : f.comp inl = g.comp inl)
  证明: by
  rw [lift_unique f]; rw [lift_unique g]
  simp only [*]

Depends on / 依赖: lift_unique
-/
theorem hom_ext {f g : N ⋊[φ] G ->* H} (hl : f.comp inl = g.comp inl)
    (hr : f.comp inr = g.comp inr) : f = g := by
  rw [lift_unique f]; rw [lift_unique g]
  simp only [*]

/-- The homomorphism from a semidirect product of subgroups to the ambient group. -/
@[simps!]
/--
Definition of `monoidHomSubgroup` / `monoidHomSubgroup` 的定义

English:
definition monoidHomSubgroup
  signature: {H K : Subgroup G} (h : K <= normalizer H)
  body: lift H.subtype K.subtype (by simp [DFunLike.ext_iff])

中文:
定义 monoidHomSubgroup
  签名: {H K : Subgroup G} (h : K <= normalizer H)
  定义体: lift H.subtype K.subtype (by simp [DFunLike.ext_iff])

Depends on / 依赖: DFunLike, DFunLike.ext_iff, H.subtype, K.subtype, ext_iff, subtype
-/
def monoidHomSubgroup {H K : Subgroup G} (h : K <= normalizer H) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion h)] K ->* G :=
  lift H.subtype K.subtype (by simp [DFunLike.ext_iff])

/-- The isomorphism from a semidirect product of complementary subgroups to the ambient group. -/
@[simps!]
/--
Definition of `mulEquivSubgroup` / `mulEquivSubgroup` 的定义

English:
definition mulEquivSubgroup
  signature: {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K)
  body: MulEquiv.ofBijective (monoidHomSubgroup _) ((equivProd.bijective_comp _).mpr h)

中文:
定义 mulEquivSubgroup
  签名: {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K)
  定义体: MulEquiv.ofBijective (monoidHomSubgroup _) ((equivProd.bijective_comp _).mpr h)

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, bijective_comp, equivProd, equivProd.bijective_comp, monoidHomSubgroup, ofBijective
-/
noncomputable def mulEquivSubgroup {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion (H.normalizer_eq_top ▸ le_top))] K ≃* G :=
  MulEquiv.ofBijective (monoidHomSubgroup _) ((equivProd.bijective_comp _).mpr h)

end lift

section Map

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ ->* MulAut N₁} {φ₂ : G₂ ->* MulAut N₂}
  (fn : N₁ ->* N₂) (fg : G₁ ->* G₂)
  (h : forall g : G₁, fn.comp (φ₁ g).toMonoidHom = (φ₂ (fg g)).toMonoidHom.comp fn)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : N₁ ⋊[φ₁] G₁ ->* N₂ ⋊[φ₂] G₂ where
  body: ⟨fn x.1, fg x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

@[simp]

中文:
定义 map
  签名: : N₁ ⋊[φ₁] G₁ ->* N₂ ⋊[φ₂] G₂ where
  定义体: ⟨fn x.1, fg x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

@[simp]
-/
def map : N₁ ⋊[φ₁] G₁ ->* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

@[simp]
/--
theorem `map_left` / 定理 `map_left`

English:
theorem map_left
  given: (g : N₁ ⋊[φ₁] G₁)
  statement: (map fn fg h g).left = fn g.left
  proof: rfl

@[simp]

中文:
定理 map_left
  条件: (g : N₁ ⋊[φ₁] G₁)
  结论: (map fn fg h g).left = fn g.left
  证明: rfl

@[simp]
-/
theorem map_left (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).left = fn g.left := rfl

@[simp]
/--
theorem `map_right` / 定理 `map_right`

English:
theorem map_right
  given: (g : N₁ ⋊[φ₁] G₁)
  statement: (map fn fg h g).right = fg g.right
  proof: rfl

@[simp]

中文:
定理 map_right
  条件: (g : N₁ ⋊[φ₁] G₁)
  结论: (map fn fg h g).right = fg g.right
  证明: rfl

@[simp]
-/
theorem map_right (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).right = fg g.right := rfl

@[simp]
/--
theorem `rightHom_comp_map` / 定理 `rightHom_comp_map`

English:
theorem rightHom_comp_map
  statement: rightHom.comp (map fn fg h) = fg.comp rightHom
  proof: rfl

@[simp]

中文:
定理 rightHom_comp_map
  结论: rightHom.comp (map fn fg h) = fg.comp rightHom
  证明: rfl

@[simp]
-/
theorem rightHom_comp_map : rightHom.comp (map fn fg h) = fg.comp rightHom := rfl

@[simp]
/--
theorem `map_inl` / 定理 `map_inl`

English:
theorem map_inl
  given: (n : N₁)
  statement: map fn fg h (inl n) = inl (fn n)
  proof: by simp [map]

@[simp]

中文:
定理 map_inl
  条件: (n : N₁)
  结论: map fn fg h (inl n) = inl (fn n)
  证明: by simp [map]

@[simp]
-/
theorem map_inl (n : N₁) : map fn fg h (inl n) = inl (fn n) := by simp [map]

@[simp]
/--
theorem `map_comp_inl` / 定理 `map_comp_inl`

English:
theorem map_comp_inl
  statement: (map fn fg h).comp inl = inl.comp fn
  proof: by ext <;> simp

@[simp]

中文:
定理 map_comp_inl
  结论: (map fn fg h).comp inl = inl.comp fn
  证明: by ext <;> simp

@[simp]
-/
theorem map_comp_inl : (map fn fg h).comp inl = inl.comp fn := by ext <;> simp

@[simp]
/--
theorem `map_inr` / 定理 `map_inr`

English:
theorem map_inr
  given: (g : G₁)
  statement: map fn fg h (inr g) = inr (fg g)
  proof: by simp [map]

@[simp]

中文:
定理 map_inr
  条件: (g : G₁)
  结论: map fn fg h (inr g) = inr (fg g)
  证明: by simp [map]

@[simp]
-/
theorem map_inr (g : G₁) : map fn fg h (inr g) = inr (fg g) := by simp [map]

@[simp]
/--
theorem `map_comp_inr` / 定理 `map_comp_inr`

English:
theorem map_comp_inr
  statement: (map fn fg h).comp inr = inr.comp fg
  proof: by ext <;> simp [map]

中文:
定理 map_comp_inr
  结论: (map fn fg h).comp inr = inr.comp fg
  证明: by ext <;> simp [map]
-/
theorem map_comp_inr : (map fn fg h).comp inr = inr.comp fg := by ext <;> simp [map]

end Map

section Congr

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ ->* MulAut N₁} {φ₂ : G₂ ->* MulAut N₂}
  (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
  (h : forall g : G₁, (φ₁ g).trans fn = fn.trans (φ₂ (fg g)))

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given isomorphisms `N₁ ≃* N₂` and
  `G₁ ≃* G₂` that satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`. -/
@[simps]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where
  body: ⟨fn x.1, fg x.2⟩
  invFun x := ⟨fn.symm x.1, fg.symm x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

中文:
定义 congr
  签名: : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where
  定义体: ⟨fn x.1, fg x.2⟩
  invFun x := ⟨fn.symm x.1, fg.symm x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all
-/
def congr : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  invFun x := ⟨fn.symm x.1, fg.symm x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` without specifying `φ₂`. -/
@[simps!]
/--
Definition of `congr'` / `congr'` 的定义

English:
definition congr'
  signature: :
  body: congr fn fg (fun _ => by ext; simp)

中文:
定义 congr'
  签名: :
  定义体: congr fn fg (fun _ => by ext; simp)
-/
def congr' :
    N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[MonoidHom.comp (MulAut.congr fn) (φ₁.comp fg.symm)] G₂ :=
  congr fn fg (fun _ => by ext; simp)

end Congr

@[simp]
/--
lemma `card` / 引理 `card`

English:
lemma card
  statement: Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G
  proof: Nat.card_prod _ _ ▸ Nat.card_congr equivProd

中文:
引理 card
  结论: 自然数.card (N ⋊[φ] G) = 自然数.card N * 自然数.card G
  证明: Nat.card_prod _ _ ▸ Nat.card_congr equivProd

Depends on / 依赖: Nat.card_congr, Nat.card_prod, card_congr, card_prod, equivProd
-/
lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G :=
  Nat.card_prod _ _ ▸ Nat.card_congr equivProd

end SemidirectProduct
