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
/-
**RegularWreathProduct** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_2 → Type (max u_1 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The regular wreath product of groups `Q` and `D`. It is the product `(Q → D) × Q
` with the group
operation `⟨a₁, a₂⟩ * ⟨b₁, b₂⟩ = ⟨a₁ * (fun x ↦ b₁ (a₂⁻¹ * x)), a₂ * b₂⟩`.
-/
structure RegularWreathProduct where
  /-- The function of Q → D -/
  left : Q → D
  /-- The element of Q -/
  right : Q

@[inherit_doc] infix:65 " ≀ᵣ " => RegularWreathProduct

namespace RegularWreathProduct
variable {D Q}

/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (D ≀ᵣ Q) where
  mul a b := ⟨a.1 * (fun x ↦ b.1 (a.2⁻¹ * x)), a.2 * b.2⟩
/-
**RegularWreathProduct.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `RegularWreathProduct`。
形式化陈述：mul_def (a b : D ≀ᵣ Q) : a * b = ⟨a.1 * fun x => b.1 (a.2⁻¹ * x), a.2 * b.
2⟩
参数：a b : D ≀ᵣ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (a b : D ≀ᵣ Q) : a * b = ⟨a.1 * fun x ↦ b.1 (a.2⁻¹ * x), a.2 * b.2⟩ := rfl

@[simp]
/-
**RegularWreathProduct.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`
。
形式化陈述：mul_left (a b : D ≀ᵣ Q) : (a * b).1 = a.1 * fun x => b.1 (a.2⁻¹ * x)
参数：a b : D ≀ᵣ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_left (a b : D ≀ᵣ Q) : (a * b).1 = a.1 * fun x ↦ b.1 (a.2⁻¹ * x) := rfl

@[simp]
/-
**RegularWreathProduct.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct
`。
形式化陈述：mul_right (a b : D ≀ᵣ Q) : (a * b).right = a.right * b.right
参数：a b : D ≀ᵣ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_right (a b : D ≀ᵣ Q) : (a * b).right = a.right * b.right := rfl
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (RegularWreathProduct D Q) where one := ⟨1, 1⟩

@[simp]
/-
**RegularWreathProduct.one_left** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`
。
形式化陈述：one_left : (1 : D ≀ᵣ Q).left = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_left : (1 : D ≀ᵣ Q).left = 1 := rfl

@[simp]
/-
**RegularWreathProduct.one_right** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct
`。
形式化陈述：one_right : (1 : D ≀ᵣ Q).right = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_right : (1 : D ≀ᵣ Q).right = 1 := rfl
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (RegularWreathProduct D Q) where
  inv x := ⟨fun k ↦ x.1⁻¹ (x.2 * k), x.2⁻¹⟩

@[simp]
/-
**RegularWreathProduct.inv_left** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`
。
形式化陈述：inv_left (a : D ≀ᵣ Q) : a⁻¹.left = fun x => a.left⁻¹ (a.right * x)
参数：a : D ≀ᵣ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_left (a : D ≀ᵣ Q) : a⁻¹.left = fun x ↦ a.left⁻¹ (a.right * x) := rfl

@[simp]
/-
**RegularWreathProduct.inv_right** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct
`。
形式化陈述：inv_right (a : D ≀ᵣ Q) : a⁻¹.right = a.right⁻¹
参数：a : D ≀ᵣ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_right (a : D ≀ᵣ Q) : a⁻¹.right = a.right⁻¹ := rfl
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (RegularWreathProduct D Q) where
  mul_assoc a b c := by ext <;> simp [mul_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RegularWreathProduct D Q) := ⟨1⟩

/-- The canonical projection map `D ≀ᵣ Q →* Q`, as a group hom. -/
/-
**RegularWreathProduct.rightHom** 是 Mathlib 中的一个定义，位于命名空间 `RegularWreathProduct`
。
形式化陈述：rightHom : D ≀ᵣ Q ->* Q where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection map `D ≀ᵣ Q →* Q`, as a group hom.
-/
def rightHom : D ≀ᵣ Q →* Q where
  toFun := RegularWreathProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical map `Q →* D ≀ᵣ Q` sending `q` to `⟨1, q⟩` -/
/-
**RegularWreathProduct.inl** 是 Mathlib 中的一个定义，位于命名空间 `RegularWreathProduct`。
形式化陈述：inl : Q ->* D ≀ᵣ Q where toFun q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Q →* D ≀ᵣ Q` sending `q` to `⟨1, q⟩`
-/
def inl : Q →* D ≀ᵣ Q where
  toFun q := ⟨1, q⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

@[simp]
/-
**RegularWreathProduct.left_inl** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`
。
形式化陈述：left_inl (q : Q) : (inl q : D ≀ᵣ Q).left = 1
参数：q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_inl (q : Q) : (inl q : D ≀ᵣ Q).left = 1 := rfl

@[simp]
/-
**RegularWreathProduct.right_inl** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct
`。
形式化陈述：right_inl (q : Q) : (inl q : D ≀ᵣ Q).right = q
参数：q : Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem right_inl (q : Q) : (inl q : D ≀ᵣ Q).right = q := rfl

@[simp]
/-
**RegularWreathProduct.rightHom_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreat
hProduct`。
形式化陈述：rightHom_eq_right : (rightHom : D ≀ᵣ Q -> Q) = right
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightHom_eq_right : (rightHom : D ≀ᵣ Q → Q) = right := rfl

@[simp]
/-
**RegularWreathProduct.rightHom_comp_inl_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Regula
rWreathProduct`。
形式化陈述：rightHom_comp_inl_eq_id : (rightHom : D ≀ᵣ Q ->* Q).comp inl = MonoidHom.i
d _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightHom_comp_inl_eq_id : (rightHom : D ≀ᵣ Q →* Q).comp inl = MonoidHom.id _ := by ext; simp

@[simp]
/-
**RegularWreathProduct.fun_id** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`。
形式化陈述：fun_id (q : Q) : rightHom (inl q : D ≀ᵣ Q) = q
参数：q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fun_id (q : Q) : rightHom (inl q : D ≀ᵣ Q) = q := by simp

/-- The equivalence map for the representation as a product. -/
/-
**RegularWreathProduct.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `RegularWreathProduct
`。
形式化陈述：equivProd D Q : D ≀ᵣ Q ≃ (Q -> D) × Q where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence map for the representation as a product.
-/
def equivProd D Q : D ≀ᵣ Q ≃ (Q → D) × Q where
  toFun := fun ⟨d, q⟩ => ⟨d, q⟩
  invFun := fun ⟨d, q⟩ => ⟨d, q⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite D] [Finite Q] : Finite (D ≀ᵣ Q) :=
  Finite.of_equiv _ (equivProd D Q).symm

omit [Group D] [Group Q] in
/-
**RegularWreathProduct.card** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct`。
形式化陈述：card [Finite Q] : Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_fun`：card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat
.card α
-/
theorem card [Finite Q] : Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q := by
  rw [Nat.card_congr (equivProd D Q), Nat.card_prod (Q → D) Q, Nat.card_fun]

/-- Define an isomorphism from `D₁ ≀ᵣ Q₁` to `D₂ ≀ᵣ Q₂`
given isomorphisms `D₁ ≀ᵣ Q₁` and `Q₁ ≃* Q₂`. -/
/-
**RegularWreathProduct.congr** 是 Mathlib 中的一个定义，位于命名空间 `RegularWreathProduct`。
形式化陈述：congr {D₁ Q₁ D₂ Q₂ : Type*} [Group D₁] [Group Q₁] [Group D₂] [Group Q₂] (f
 : D₁ ≃* D₂) (g : Q₁ ≃* Q₂) : D₁ ≀ᵣ Q₁ ≃* D₂ ≀ᵣ Q₂ where toFun x
参数：f : D₁ ≃* D₂；g : Q₁ ≃* Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define an isomorphism from `D₁ ≀ᵣ Q₁` to `D₂ ≀ᵣ Q₂`
given isomorphisms `D₁ ≀ᵣ Q₁` and `Q₁ ≃* Q₂`.
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

/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (D ≀ᵣ Q) (Λ × Q) where
  smul w p := ⟨(w.left (w.right * p.2)) • p.1, w.right * p.2⟩

@[simp]
/-
**RegularWreathProduct.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `RegularWreathProduct`
。
形式化陈述：smul_def {w : D ≀ᵣ Q} {p : Λ × Q} : w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 
* p.2⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def {w : D ≀ᵣ Q} {p : Λ × Q} : w • p = ⟨(w.1 (w.2 * p.2)) • p.1, w.2 * p.2⟩ := rfl
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (D ≀ᵣ Q) (Λ × Q) where
  one_smul := by simp
  mul_smul := by simp [smul_smul, mul_assoc]

variable [FaithfulSMul D Λ]
/-
**RegularWreathProduct.** 是 Mathlib 中的一个实例，位于命名空间 `RegularWreathProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- The map sending the wreath product `D ≀ᵣ Q` to its representation as a permutation of `Λ × Q`
given `D`-set `Λ`. -/
/-
**RegularWreathProduct.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `RegularWreathProduct`。
形式化陈述：toPerm : D ≀ᵣ Q ->* Equiv.Perm (Λ × Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map sending the wreath product `D ≀ᵣ Q` to its representation as a permutati
on of `Λ × Q`
given `D`-set `Λ`.
-/
def toPerm : D ≀ᵣ Q →* Equiv.Perm (Λ × Q) :=
  MulAction.toPermHom (D ≀ᵣ Q) (Λ × Q)
/-
**RegularWreathProduct.toPermInj** 是 Mathlib 中的一个定理，位于命名空间 `RegularWreathProduct
`。
形式化陈述：toPermInj [Nonempty Λ] : Function.Injective (toPerm D Q Λ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.toPerm_injective`：MulAction.toPerm_injective [FaithfulSMul α β
] : Function.Injective (MulAction.toPerm : α -> Equiv.Perm β)
· 使用定理 `RegularWreathProduct.instFaithfulSMulProdOfNonempty`：∀ (D : Type u_1) (Q
 : Type u_2) [inst : Group D] [inst_1 : Group Q] (Λ : Type u_3) [inst_2 : MulAct
ion D Λ]   [FaithfulSMul D Λ] [Nonempty Q…
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem toPermInj [Nonempty Λ] : Function.Injective (toPerm D Q Λ) := MulAction.toPerm_injective

end perm

end RegularWreathProduct

section iterated

universe u

/-- The wreath product of group `G` iterated `n` times. -/
/-
**IteratedWreathProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Type u → ℕ → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The wreath product of group `G` iterated `n` times.
-/
def IteratedWreathProduct (G : Type u) : (n : ℕ) → Type u
| 0 => PUnit
| n + 1 => (IteratedWreathProduct G n) ≀ᵣ G

variable (G : Type u) (n : ℕ)

@[simp]
/-
**IteratedWreathProduct_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IteratedWreathProduct_zero : IteratedWreathProduct G 0 = PUnit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IteratedWreathProduct_zero : IteratedWreathProduct G 0 = PUnit := rfl

@[simp]
/-
**IteratedWreathProduct_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IteratedWreathProduct_succ : IteratedWreathProduct G (n + 1) = (IteratedWr
eathProduct G n) ≀ᵣ G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IteratedWreathProduct_succ :
    IteratedWreathProduct G (n + 1) = (IteratedWreathProduct G n) ≀ᵣ G := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite G] : Finite (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n h => rw [IteratedWreathProduct_succ]; infer_instance
/-
**IteratedWreathProduct.card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IteratedWreathProduct.card [Finite G] : Nat.card (IteratedWreathProduct G 
n) = Nat.card G ^ (∑ i in Finset.range n, Nat.card G ^ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IteratedWreathProduct_succ`：IteratedWreathProduct_succ : IteratedWreathP
roduct G (n + 1) = (IteratedWreathProduct G n) ≀ᵣ G
· 使用定理 `RegularWreathProduct.card`：card [Finite Q] : Nat.card (D ≀ᵣ Q) = Nat.car
d D ^ Nat.card Q * Nat.card Q
· 使用引理 `geom_sum_succ`：geom_sum_succ {x : R} {n : Nat} : ∑ i in range (n + 1), x
 ^ i = (x * ∑ i in range n, x ^ i) + 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem IteratedWreathProduct.card [Finite G] : Nat.card (IteratedWreathProduct G n) =
    Nat.card G ^ (∑ i ∈ Finset.range n, Nat.card G ^ i) := by
  induction n with
  | zero => simp
  | succ n h => rw [IteratedWreathProduct_succ, RegularWreathProduct.card,
      h, geom_sum_succ, pow_succ, pow_mul']

variable [Group G]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (IteratedWreathProduct G n) := by
  induction n with
  | zero => rw [IteratedWreathProduct_zero]; infer_instance
  | succ n ih => rw [IteratedWreathProduct_succ]; infer_instance

/-- The homomorphism from `IteratedWreathProduct G n` to `Perm (Fin n → G)`. -/
/-
**iteratedWreathToPermHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iteratedWreathToPermHom (G : Type*) [Group G] : (n : Nat) -> (IteratedWrea
thProduct G n ->* Equiv.Perm (Fin n -> G)) | 0 => 1 | n + 1 => by let _
参数：G : Type*。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from `IteratedWreathProduct G n` to `Perm (Fin n → G)`.
-/
def iteratedWreathToPermHom (G : Type*) [Group G] :
    (n : ℕ) → (IteratedWreathProduct G n →* Equiv.Perm (Fin n → G))
  | 0 => 1
  | n + 1 => by
      let _ := MulAction.compHom (Fin n → G) (iteratedWreathToPermHom G n)
      exact (Fin.succFunEquiv G n).symm.permCongrHom.toMonoidHom.comp
        (RegularWreathProduct.toPerm (IteratedWreathProduct G n) G (Fin n → G))
/-
**iteratedWreathToPermHomInj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedWreathToPermHomInj (G : Type*) [Group G] : (n : Nat) -> Function.I
njective (iteratedWreathToPermHom G n) | 0 => by simp only [IteratedWreathProduc
t_zero] apply Function.injective_of_subsingleton | n + 1 => by let _
参数：G : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iteratedWreathToPermHomInj (G : Type*) [Group G] :
    (n : ℕ) → Function.Injective (iteratedWreathToPermHom G n)
  | 0 => by
      simp only [IteratedWreathProduct_zero]
      apply Function.injective_of_subsingleton
  | n + 1 => by
      let _ := MulAction.compHom (Fin n → G) (iteratedWreathToPermHom G n)
      have : FaithfulSMul (IteratedWreathProduct G n) (Fin n → G) :=
        ⟨fun h ↦ iteratedWreathToPermHomInj G n (Equiv.ext h)⟩
      exact ((Fin.succFunEquiv G n).symm.permCongrHom.toEquiv.comp_injective _).mpr
        (RegularWreathProduct.toPermInj (IteratedWreathProduct G n) G (Fin n → G))

/-- The encoding of the Sylow `p`-subgroups of `Perm α` as an iterated wreath product. -/
/-
**Sylow.mulEquivIteratedWreathProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Sylow.mulEquivIteratedWreathProduct (p : Nat) [hp : Fact (Nat.Prime p)] (n
 : Nat) (α : Type*) [Finite α] (hα : Nat.card α = p ^ n) (G : Type*) [Group G] [
Finite G] (hG : Nat.card G = p) (P : Sylow p (Equiv.Perm α)) : P ≃* IteratedWrea
thProduct G n
参数：p : Nat；Nat.Prime p；n : Nat；α : Type*；hα : Nat.card α = p ^ n；G : Type*；hG : 
Nat.card G = p；P : Sylow p (Equiv.Perm α)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The encoding of the Sylow `p`-subgroups of `Perm α` as an iterated wreath produc
t.
-/
noncomputable def Sylow.mulEquivIteratedWreathProduct (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)
    (α : Type*) [Finite α] (hα : Nat.card α = p ^ n)
    (G : Type*) [Group G] [Finite G] (hG : Nat.card G = p)
    (P : Sylow p (Equiv.Perm α)) :
    P ≃* IteratedWreathProduct G n := by
  let e1 : α ≃ (Fin n → G) := (Finite.equivFinOfCardEq hα).trans
    (Finite.equivFinOfCardEq (by rw [Nat.card_fun, Nat.card_fin, hG])).symm
  let f := e1.symm.permCongrHom.toMonoidHom.comp (iteratedWreathToPermHom G n)
  have hf : Function.Injective f :=
    (e1.symm.permCongrHom.comp_injective _).mpr (iteratedWreathToPermHomInj G n)
  let g := (MonoidHom.ofInjective hf).symm
  let P' : Sylow p (Equiv.Perm α) := Sylow.ofCard (MonoidHom.range f) (by
    rw [Nat.card_congr g.toEquiv, IteratedWreathProduct.card, hG, Nat.card_perm, hα,
        ← Nat.multiplicity_eq_factorization hp.out (p ^ n).factorial_ne_zero,
        Nat.Prime.multiplicity_factorial_pow hp.out])
  exact (P.equiv P').trans g

end iterated

