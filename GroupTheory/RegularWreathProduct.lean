/-
Copyright (c) 2025 Francisco Silva. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Silva
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.GroupTheory.Sylow

/-!
# Regular wreath product

This file defines the regular wreath product of groups, and the canonical maps in and out of the
product. The regular wreath product of `D` and `Q` is the product `(Q → D) × Q` with the group
operation `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (fun x ↦ b₁ (a₂⁻¹ * x)), a₂ * b₂⟩`.

## Main definitions

* `RegularWreathProduct D Q` : The regular wreath product of groups `D` and `Q`.
* `rightHom` : The canonical projection `D ≀ᵣ Q →* Q`.
* `inl` : The canonical map `Q →* D ≀ᵣ Q`.
* `toPerm` : The homomorphism from `D ≀ᵣ Q` to `Equiv.Perm (Λ × Q)`, where `Λ` is a `D`-set.
* `IteratedWreathProduct G n` : The iterated wreath product of a group `G` `n` times.
* `Sylow.mulEquivIteratedWreathProduct` : The isomorphism between the Sylow `p`-subgroup of `Perm
  p^n` and the iterated wreath product of the cyclic group of order `p` `n` times.

## Notation

This file introduces the global notation `D ≀ᵣ Q` for `RegularWreathProduct D Q`.

## Tags
group, regular wreath product, sylow p-subgroup
-/

@[expose] public section

variable (D Q : Type*) [Group D] [Group Q]

/-- The regular wreath product of groups `Q` and `D`. It is the product `(Q → D) × Q` with the group
operation `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (fun x ↦ b₁ (a₂⁻¹ * x)), a₂ * b₂⟩`. -/
@[ext]
/--
Definition of `RegularWreathProduct` / `RegularWreathProduct` 的定义

English:
structure RegularWreathProduct
  parameters: where
  axioms and operations (2):
    - left : Q -> D
    - right : Q

中文:
结构 RegularWreathProduct
  参数: where
  公理与运算 (2 个):
    - left : Q -> D
    - right : Q
-/
structure RegularWreathProduct where
  /-- The function of Q → D -/
  left : Q -> D
  /-- The element of Q -/
  right : Q

@[inherit_doc] infix:65 " ≀ᵣ " => RegularWreathProduct

namespace RegularWreathProduct
variable {D Q}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (D ≀ᵣ Q)
  body: ⟨a.1 * (fun x => b.1 (a.2⁻¹ * x)), a.2 * b.2⟩

中文:
实例 :
  签名: Mul (D ≀ᵣ Q)
  定义体: ⟨a.1 * (fun x => b.1 (a.2⁻¹ * x)), a.2 * b.2⟩
-/
instance : Mul (D ≀ᵣ Q) where
  mul a b := ⟨a.1 * (fun x => b.1 (a.2⁻¹ * x)), a.2 * b.2⟩

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: (a b : D ≀ᵣ Q)
  statement: a * b = ⟨a.1 * fun x => b.1 (a.2⁻¹ * x), a.2 * b.2⟩
  proof: rfl

@[simp]

中文:
引理 mul_def
  条件: (a b : D ≀ᵣ Q)
  结论: a * b = ⟨a.1 * fun x => b.1 (a.2⁻¹ * x), a.2 * b.2⟩
  证明: rfl

@[simp]
-/
lemma mul_def (a b : D ≀ᵣ Q) : a * b = ⟨a.1 * fun x => b.1 (a.2⁻¹ * x), a.2 * b.2⟩ := rfl

@[simp]
/--
theorem `mul_left` / 定理 `mul_left`

English:
theorem mul_left
  given: (a b : D ≀ᵣ Q)
  statement: (a * b).1 = a.1 * fun x => b.1 (a.2⁻¹ * x)
  proof: rfl

@[simp]

中文:
定理 mul_left
  条件: (a b : D ≀ᵣ Q)
  结论: (a * b).1 = a.1 * fun x => b.1 (a.2⁻¹ * x)
  证明: rfl

@[simp]
-/
theorem mul_left (a b : D ≀ᵣ Q) : (a * b).1 = a.1 * fun x => b.1 (a.2⁻¹ * x) := rfl

@[simp]
/--
theorem `mul_right` / 定理 `mul_right`

English:
theorem mul_right
  given: (a b : D ≀ᵣ Q)
  statement: (a * b).right = a.right * b.right
  proof: rfl

中文:
定理 mul_right
  条件: (a b : D ≀ᵣ Q)
  结论: (a * b).right = a.right * b.right
  证明: rfl
-/
theorem mul_right (a b : D ≀ᵣ Q) : (a * b).right = a.right * b.right := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (RegularWreathProduct D Q)
  body: ⟨1, 1⟩

@[simp]

中文:
实例 :
  签名: One (RegularWreathProduct D Q)
  定义体: ⟨1, 1⟩

@[simp]
-/
instance : One (RegularWreathProduct D Q) where one := ⟨1, 1⟩

@[simp]
/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  statement: (1 : D ≀ᵣ Q).left = 1
  proof: rfl

@[simp]

中文:
定理 one_left
  结论: (1 : D ≀ᵣ Q).left = 1
  证明: rfl

@[simp]
-/
theorem one_left : (1 : D ≀ᵣ Q).left = 1 := rfl

@[simp]
/--
theorem `one_right` / 定理 `one_right`

English:
theorem one_right
  statement: (1 : D ≀ᵣ Q).right = 1
  proof: rfl

中文:
定理 one_right
  结论: (1 : D ≀ᵣ Q).right = 1
  证明: rfl
-/
theorem one_right : (1 : D ≀ᵣ Q).right = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (RegularWreathProduct D Q)
  body: ⟨fun k => x.1⁻¹ (x.2 * k), x.2⁻¹⟩

@[simp]

中文:
实例 :
  签名: Inv (RegularWreathProduct D Q)
  定义体: ⟨fun k => x.1⁻¹ (x.2 * k), x.2⁻¹⟩

@[simp]
-/
instance : Inv (RegularWreathProduct D Q) where
  inv x := ⟨fun k => x.1⁻¹ (x.2 * k), x.2⁻¹⟩

@[simp]
/--
theorem `inv_left` / 定理 `inv_left`

English:
theorem inv_left
  given: (a : D ≀ᵣ Q)
  statement: a⁻¹.left = fun x => a.left⁻¹ (a.right * x)
  proof: rfl

@[simp]

中文:
定理 inv_left
  条件: (a : D ≀ᵣ Q)
  结论: a⁻¹.left = fun x => a.left⁻¹ (a.right * x)
  证明: rfl

@[simp]
-/
theorem inv_left (a : D ≀ᵣ Q) : a⁻¹.left = fun x => a.left⁻¹ (a.right * x) := rfl

@[simp]
/--
theorem `inv_right` / 定理 `inv_right`

English:
theorem inv_right
  given: (a : D ≀ᵣ Q)
  statement: a⁻¹.right = a.right⁻¹
  proof: rfl

中文:
定理 inv_right
  条件: (a : D ≀ᵣ Q)
  结论: a⁻¹.right = a.right⁻¹
  证明: rfl
-/
theorem inv_right (a : D ≀ᵣ Q) : a⁻¹.right = a.right⁻¹ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (RegularWreathProduct D Q)
  body: by ext <;> simp [mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

中文:
实例 :
  签名: Group (RegularWreathProduct D Q)
  定义体: by ext <;> simp [mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

Depends on / 依赖: inv_mul_cancel, mul_assoc, mul_one, one_mul
-/
instance : Group (RegularWreathProduct D Q) where
  mul_assoc a b c := by ext <;> simp [mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RegularWreathProduct D Q)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (RegularWreathProduct D Q)
  定义体: ⟨1⟩
-/
instance : Inhabited (RegularWreathProduct D Q) := ⟨1⟩

/--
Definition of `rightHom` / `rightHom` 的定义

English:
definition rightHom
  signature: : D ≀ᵣ Q ->* Q where
  body: RegularWreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 rightHom
  签名: : D ≀ᵣ Q ->* Q where
  定义体: RegularWreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: RegularWreathProduct, RegularWreathProduct.right
-/
def rightHom : D ≀ᵣ Q ->* Q where
  toFun := RegularWreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : Q ->* D ≀ᵣ Q where
  body: ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp]

中文:
定义 inl
  签名: : Q ->* D ≀ᵣ Q where
  定义体: ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp]
-/
def inl : Q ->* D ≀ᵣ Q where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp]
/--
theorem `left_inl` / 定理 `left_inl`

English:
theorem left_inl
  given: (q : Q)
  statement: (inl q : D ≀ᵣ Q).left = 1
  proof: rfl

@[simp]

中文:
定理 left_inl
  条件: (q : Q)
  结论: (inl q : D ≀ᵣ Q).left = 1
  证明: rfl

@[simp]

Depends on / 依赖: Infinite
-/
theorem left_inl (q : Q) : (inl q : D ≀ᵣ Q).left = 1 := rfl

@[simp]
/--
theorem `right_inl` / 定理 `right_inl`

English:
theorem right_inl
  given: (q : Q)
  statement: (inl q : D ≀ᵣ Q).right = q
  proof: rfl

@[simp]

中文:
定理 right_inl
  条件: (q : Q)
  结论: (inl q : D ≀ᵣ Q).right = q
  证明: rfl

@[simp]
-/
theorem right_inl (q : Q) : (inl q : D ≀ᵣ Q).right = q := rfl

@[simp]
/--
theorem `rightHom_eq_right` / 定理 `rightHom_eq_right`

English:
theorem rightHom_eq_right
  statement: (rightHom : D ≀ᵣ Q -> Q) = right
  proof: rfl

@[simp]

中文:
定理 rightHom_eq_right
  结论: (rightHom : D ≀ᵣ Q -> Q) = right
  证明: rfl

@[simp]
-/
theorem rightHom_eq_right : (rightHom : D ≀ᵣ Q -> Q) = right := rfl

@[simp]
/--
theorem `rightHom_comp_inl_eq_id` / 定理 `rightHom_comp_inl_eq_id`

English:
theorem rightHom_comp_inl_eq_id
  statement: (rightHom : D ≀ᵣ Q ->* Q).comp inl = MonoidHom.id _
  proof: by ext; simp

@[simp]

中文:
定理 rightHom_comp_inl_eq_id
  结论: (rightHom : D ≀ᵣ Q ->* Q).comp inl = MonoidHom.id _
  证明: by ext; simp

@[simp]
-/
theorem rightHom_comp_inl_eq_id : (rightHom : D ≀ᵣ Q ->* Q).comp inl = MonoidHom.id _ := by ext; simp

@[simp]
/--
theorem `fun_id` / 定理 `fun_id`

English:
theorem fun_id
  given: (q : Q)
  statement: rightHom (inl q : D ≀ᵣ Q) = q
  proof: by simp

中文:
定理 fun_id
  条件: (q : Q)
  结论: rightHom (inl q : D ≀ᵣ Q) = q
  证明: by simp
-/
theorem fun_id (q : Q) : rightHom (inl q : D ≀ᵣ Q) = q := by simp

/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: D Q
  body: fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

中文:
定义 equivProd
  签名: D Q
  定义体: fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
-/
def equivProd D Q : D ≀ᵣ Q ≃ (Q -> D) × Q where
  toFun := fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: D] [Finite Q] : Finite (D ≀ᵣ Q)
  body: Finite.of_equiv _ (equivProd D Q).symm

omit [Group D] [Group Q] in

中文:
实例 [Finite
  签名: D] [Finite Q] : Finite (D ≀ᵣ Q)
  定义体: Finite.of_equiv _ (equivProd D Q).symm

omit [Group D] [Group Q] in

Depends on / 依赖: Finite, Finite.of_equiv, equivProd, of_equiv
-/
instance [Finite D] [Finite Q] : Finite (D ≀ᵣ Q) :=
  Finite.of_equiv _ (equivProd D Q).symm

omit [Group D] [Group Q] in
/--
theorem `card` / 定理 `card`

English:
theorem card
  given: [Finite Q]
  statement: Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q
  proof: by
  rw [Nat.card_congr (equivProd D Q)]; rw [Nat.card_prod (Q -> D) Q]; rw [Nat.card_fun]

中文:
定理 card
  条件: [Finite Q]
  结论: 自然数.card (D ≀ᵣ Q) = 自然数.card D ^ 自然数.card Q * 自然数.card Q
  证明: by
  rw [Nat.card_congr (equivProd D Q)]; rw [Nat.card_prod (Q -> D) Q]; rw [Nat.card_fun]

Depends on / 依赖: Nat.card_congr, Nat.card_fun, Nat.card_prod, card_congr, card_fun, card_prod, equivProd
-/
theorem card [Finite Q] : Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q := by
  rw [Nat.card_congr (equivProd D Q)]; rw [Nat.card_prod (Q -> D) Q]; rw [Nat.card_fun]

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {D₁ Q₁ D₂ Q₂ : Type*} [Group D₁] [Group Q₁] [Group D₂] [Group Q₂]
  body: ⟨f ∘ (x.left ∘ g.symm), g x.right⟩
  invFun x := ⟨(f.symm ∘ x.left) ∘ g, g.symm x.right⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp

中文:
定义 congr
  签名: {D₁ Q₁ D₂ Q₂ : 类型} [Group D₁] [Group Q₁] [Group D₂] [Group Q₂]
  定义体: ⟨f ∘ (x.left ∘ g.symm), g x.right⟩
  invFun x := ⟨(f.symm ∘ x.left) ∘ g, g.symm x.right⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp

Depends on / 依赖: g.symm, x.left, x.right
-/
def congr {D₁ Q₁ D₂ Q₂ : Type*} [Group D₁] [Group Q₁] [Group D₂] [Group Q₂]
    (f : D₁ ≃* D₂) (g : Q₁ ≃* Q₂) :
    D₁ ≀ᵣ Q₁ ≃* D₂ ≀ᵣ Q₂ where
  toFun x := ⟨f ∘ (x.left ∘ g.symm), g x.right⟩
  invFun x := ⟨(f.symm ∘ x.left) ∘ g, g.symm x.right⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp

section perm

variable (D Q) (Λ : Type*) [MulAction D Λ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (D ≀ᵣ Q) (Λ × Q)
  body: ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

@[simp]

中文:
实例 :
  签名: SMul (D ≀ᵣ Q) (Λ × Q)
  定义体: ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

@[simp]

Depends on / 依赖: w.left, w.right
-/
instance : SMul (D ≀ᵣ Q) (Λ × Q) where
  smul w p := ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

@[simp]
/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: {w : D ≀ᵣ Q} {p : Λ × Q}
  statement: w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 * p.2⟩
  proof: rfl

中文:
引理 smul_def
  条件: {w : D ≀ᵣ Q} {p : Λ × Q}
  结论: w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 * p.2⟩
  证明: rfl
-/
lemma smul_def {w : D ≀ᵣ Q} {p : Λ × Q} : w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 * p.2⟩ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (D ≀ᵣ Q) (Λ × Q)
  body: by simp
  mul_smul := by simp [smul_smul, mul_assoc]

中文:
实例 :
  签名: MulAction (D ≀ᵣ Q) (Λ × Q)
  定义体: by simp
  mul_smul := by simp [smul_smul, mul_assoc]

Depends on / 依赖: mul_assoc, mul_smul, smul_smul
-/
instance : MulAction (D ≀ᵣ Q) (Λ × Q) where
  one_smul := by simp
  mul_smul := by simp [smul_smul, mul_assoc]

variable [FaithfulSMul D Λ]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: Q] [Nonempty Λ] : FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  body: by
    simp only [smul_def, Prod.mk.injEq, mul_left_inj, Prod.forall]
    intro m₁ m₂ h
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1
      rw [← (h a b).2] at hh
      group at hh
      exact FaithfulSMul.eq_of_smul_eq_smul hh
 

中文:
实例 [Nonempty
  签名: Q] [Nonempty Λ] : FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  定义体: by
    simp only [smul_def, Prod.mk.injEq, mul_left_inj, Prod.forall]
    intro m₁ m₂ h
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1
      rw [← (h a b).2] at hh
      group at hh
      exact FaithfulSMul.eq_of_smul_eq_smul hh
 

Depends on / 依赖: FaithfulSMul, FaithfulSMul.eq_of_smul_eq_smul, Nonempty, Prod.forall, Prod.mk.injEq, eq_of_smul_eq_smul, mul_left_inj, smul_def
-/
instance [Nonempty Q] [Nonempty Λ] : FaithfulSMul (D ≀ᵣ Q) (Λ × Q) where
  eq_of_smul_eq_smul := by
    simp only [smul_def, Prod.mk.injEq, mul_left_inj, Prod.forall]
    intro m₁ m₂ h
    let ⟨a⟩ := ‹Nonempty Λ›
    let ⟨b⟩ := ‹Nonempty Q›
    ext q
    · have hh := fun a => (h a (m₁.right⁻¹ * q)).1
      rw [← (h a b).2] at hh
      group at hh
      exact FaithfulSMul.eq_of_smul_eq_smul hh
    · exact (h a b).2

/--
Definition of `toPerm` / `toPerm` 的定义

English:
definition toPerm
  signature: : D ≀ᵣ Q ->* Equiv.Perm (Λ × Q)
  body: MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

中文:
定义 toPerm
  签名: : D ≀ᵣ Q ->* Equiv.Perm (Λ × Q)
  定义体: MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

Depends on / 依赖: MulAction, MulAction.toPermHom, toPermHom
-/
def toPerm : D ≀ᵣ Q ->* Equiv.Perm (Λ × Q) :=
  MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)

/--
theorem `toPermInj` / 定理 `toPermInj`

English:
theorem toPermInj
  given: [Nonempty Λ]
  statement: Function.Injective (toPerm D Q Λ)
  proof: MulAction.toPerm_injective

中文:
定理 toPermInj
  条件: [Nonempty Λ]
  结论: Function.Injective (toPerm D Q Λ)
  证明: MulAction.toPerm_injective

Depends on / 依赖: MulAction, MulAction.toPerm_injective, toPerm_injective
-/
theorem toPermInj [Nonempty Λ] : Function.Injective (toPerm D Q Λ) := MulAction.toPerm_injective

end perm

end RegularWreathProduct

section iterated

universe u

/--
Definition of `IteratedWreathProduct` / `IteratedWreathProduct` 的定义

English:
definition IteratedWreathProduct
  signature: (G : Type u)

中文:
定义 IteratedWreathProduct
  签名: (G : 类型u)
-/
def IteratedWreathProduct (G : Type u) : (n : Nat) -> Type u
| 0 => PUnit
| n + 1 => (IteratedWreathProduct G n) ≀ᵣ G

variable (G : Type u) (n : Nat)

@[simp]
/--
lemma `IteratedWreathProduct_zero` / 引理 `IteratedWreathProduct_zero`

English:
lemma IteratedWreathProduct_zero
  statement: IteratedWreathProduct G 0 = PUnit
  proof: rfl

@[simp]

中文:
引理 IteratedWreathProduct_zero
  结论: IteratedWreathProduct G 0 = PUnit
  证明: rfl

@[simp]
-/
lemma IteratedWreathProduct_zero : IteratedWreathProduct G 0 = PUnit := rfl

@[simp]
/--
lemma `IteratedWreathProduct_succ` / 引理 `IteratedWreathProduct_succ`

English:
lemma IteratedWreathProduct_succ
  proof: rfl

中文:
引理 IteratedWreathProduct_succ
  证明: rfl
-/
lemma IteratedWreathProduct_succ :
    IteratedWreathProduct G (n + 1) = (IteratedWreathProduct G n) ≀ᵣ G := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: G] : Finite (IteratedWreathProduct G n)
  body: by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n h => rw [IteratedWreathProduct_succ]; infer_instance

中文:
实例 [Finite
  签名: G] : Finite (IteratedWreathProduct G n)
  定义体: by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n h => rw [IteratedWreathProduct_succ]; infer_instance

Depends on / 依赖: IteratedWreathProduct_succ, IteratedWreathProduct_zero, infer_instance
-/
instance [Finite G] : Finite (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n h => rw [IteratedWreathProduct_succ]; infer_instance

/--
theorem `IteratedWreathProduct.card` / 定理 `IteratedWreathProduct.card`

English:
theorem IteratedWreathProduct.card
  given: [Finite G]
  statement: Nat.card (IteratedWreathProduct G n) =
  proof: by
  induction n with
  | zero => simp
  | succ n h => rw [IteratedWreathProduct_succ, RegularWreathProduct.card,
      h, geom_sum_succ, pow_succ, pow_mul']

中文:
定理 IteratedWreathProduct.card
  条件: [Finite G]
  结论: 自然数.card (IteratedWreathProduct G n) =
  证明: by
  induction n with
  | zero => simp
  | succ n h => rw [IteratedWreathProduct_succ, RegularWreathProduct.card,
      h, geom_sum_succ, pow_succ, pow_mul']

Depends on / 依赖: IteratedWreathProduct_succ, RegularWreathProduct, RegularWreathProduct.card, geom_sum_succ, pow_mul, pow_succ
-/
theorem IteratedWreathProduct.card [Finite G] : Nat.card (IteratedWreathProduct G n) =
    Nat.card G ^ (∑ i in Finset.range n, Nat.card G ^ i) := by
  induction n with
  | zero => simp
  | succ n h => rw [IteratedWreathProduct_succ, RegularWreathProduct.card,
      h, geom_sum_succ, pow_succ, pow_mul']

variable [Group G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (IteratedWreathProduct G n)
  body: by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n ih => rw [IteratedWreathProduct_succ]; infer_instance

中文:
实例 :
  签名: Group (IteratedWreathProduct G n)
  定义体: by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n ih => rw [IteratedWreathProduct_succ]; infer_instance

Depends on / 依赖: IteratedWreathProduct_succ, IteratedWreathProduct_zero, infer_instance
-/
instance : Group (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n ih => rw [IteratedWreathProduct_succ]; infer_instance

/--
Definition of `iteratedWreathToPermHom` / `iteratedWreathToPermHom` 的定义

English:
definition iteratedWreathToPermHom
  signature: (G : Type*) [Group G]
  body: MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      exact (Fin.succFunEquiv G n).symm.permCongrHom.toMonoidHom.comp
        (RegularWreathProduct.toPerm (IteratedWreathProduct G n) G (Fin n -> G))

中文:
定义 iteratedWreathToPermHom
  签名: (G : 类型) [Group G]
  定义体: MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      exact (Fin.succFunEquiv G n).symm.permCongrHom.toMonoidHom.comp
        (RegularWreathProduct.toPerm (IteratedWreathProduct G n) G (Fin n -> G))

Depends on / 依赖: MulAction, MulAction.compHom, compHom, iteratedWreathToPermHom
-/
def iteratedWreathToPermHom (G : Type*) [Group G] :
    (n : Nat) -> (IteratedWreathProduct G n ->* Equiv.Perm (Fin n -> G))
  | 0 => 1
  | n + 1 => by
      let _ := MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      exact (Fin.succFunEquiv G n).symm.permCongrHom.toMonoidHom.comp
        (RegularWreathProduct.toPerm (IteratedWreathProduct G n) G (Fin n -> G))

/--
lemma `iteratedWreathToPermHomInj` / 引理 `iteratedWreathToPermHomInj`

English:
lemma iteratedWreathToPermHomInj
  given: (G : Type*) [Group G]
  proof: MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      have : FaithfulSMul (IteratedWreathProduct G n) (Fin n -> G) :=
        ⟨fun h => iteratedWreathToPermHomInj G n (Equiv.ext h)⟩
      exact ((Fin.succFunEquiv G n).symm.permCongrHom.toEquiv.comp_injective _).mpr
        (RegularWreat

中文:
引理 iteratedWreathToPermHomInj
  条件: (G : 类型) [Group G]
  证明: MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      have : FaithfulSMul (IteratedWreathProduct G n) (Fin n -> G) :=
        ⟨fun h => iteratedWreathToPermHomInj G n (Equiv.ext h)⟩
      exact ((Fin.succFunEquiv G n).symm.permCongrHom.toEquiv.comp_injective _).mpr
        (RegularWreat

Depends on / 依赖: MulAction, MulAction.compHom, compHom, iteratedWreathToPermHom
-/
lemma iteratedWreathToPermHomInj (G : Type*) [Group G] :
    (n : Nat) -> Function.Injective (iteratedWreathToPermHom G n)
  | 0 => by
      simp only [IteratedWreathProduct_zero]
      apply Function.injective_of_subsingleton
  | n + 1 => by
      let _ := MulAction.compHom (Fin n -> G) (iteratedWreathToPermHom G n)
      have : FaithfulSMul (IteratedWreathProduct G n) (Fin n -> G) :=
        ⟨fun h => iteratedWreathToPermHomInj G n (Equiv.ext h)⟩
      exact ((Fin.succFunEquiv G n).symm.permCongrHom.toEquiv.comp_injective _).mpr
        (RegularWreathProduct.toPermInj (IteratedWreathProduct G n) G (Fin n -> G))

/--
Definition of `Sylow.mulEquivIteratedWreathProduct` / `Sylow.mulEquivIteratedWreathProduct` 的定义

English:
definition Sylow.mulEquivIteratedWreathProduct
  signature: (p : Nat) [hp : Fact (Nat.Prime p)] (n : Nat)
  body: by
  let e1 : α ≃ (Fin n -> G) := (Finite.equivFinOfCardEq hα).trans
    (Finite.equivFinOfCardEq (by rw [Nat.card_fun, Nat.card_fin, hG])).symm
  let f := e1.symm.permCongrHom.toMonoidHom.comp (iteratedWreathToPermHom G n)
  have hf : Function.Injective f :=
    (e1.symm.permCongrHom.comp_injective

中文:
定义 Sylow.mulEquivIteratedWreathProduct
  签名: (p : 自然数) [hp : Fact (自然数.Prime p)] (n : 自然数)
  定义体: by
  let e1 : α ≃ (Fin n -> G) := (Finite.equivFinOfCardEq hα).trans
    (Finite.equivFinOfCardEq (by rw [Nat.card_fun, Nat.card_fin, hG])).symm
  let f := e1.symm.permCongrHom.toMonoidHom.comp (iteratedWreathToPermHom G n)
  have hf : Function.Injective f :=
    (e1.symm.permCongrHom.comp_injective

Depends on / 依赖: Equiv.Perm, Finite, Finite.equivFinOfCardEq, Function, Function.Injective, Injective, IteratedWreathProduct, IteratedWreathProduct.car, MonoidHom, MonoidHom.ofInjective, MonoidHom.range, Nat.card_congr, Nat.card_fin, Nat.card_fun, Sylow.ofCard, card_congr, card_fin, card_fun, comp_injective, e1.symm.permCongrHom.comp_injective
-/
noncomputable def Sylow.mulEquivIteratedWreathProduct (p : Nat) [hp : Fact (Nat.Prime p)] (n : Nat)
    (α : Type*) [Finite α] (hα : Nat.card α = p ^ n)
    (G : Type*) [Group G] [Finite G] (hG : Nat.card G = p)
    (P : Sylow p (Equiv.Perm α)) :
    P ≃* IteratedWreathProduct G n := by
  let e1 : α ≃ (Fin n -> G) := (Finite.equivFinOfCardEq hα).trans
    (Finite.equivFinOfCardEq (by rw [Nat.card_fun, Nat.card_fin, hG])).symm
  let f := e1.symm.permCongrHom.toMonoidHom.comp (iteratedWreathToPermHom G n)
  have hf : Function.Injective f :=
    (e1.symm.permCongrHom.comp_injective _).mpr (iteratedWreathToPermHomInj G n)
  let g := (MonoidHom.ofInjective hf).symm
  let P' : Sylow p (Equiv.Perm α) := Sylow.ofCard (MonoidHom.range f) (by
    rw [Nat.card_congr g.toEquiv]; rw [IteratedWreathProduct.card]; rw [hG]; rw [Nat.card_perm]; rw [hα]; rw [← Nat.multiplicity_eq_factorization hp.out (p ^ n).factorial_ne_zero]; rw [Nat.Prime.multiplicity_factorial_pow hp.out])
  exact (P.equiv P').trans g

end iterated
