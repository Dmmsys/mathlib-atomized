/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Convolution product on Hopf algebra maps

This file constructs the ring structure on bialgebra homs `C → A` where `C` and `A` are Hopf
algebras and multiplication is given by
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

variable {R A C : Type*} [CommSemiring R]

namespace HopfAlgebra
section Semiring
variable [Semiring A] [HopfAlgebra R A]

/-
**HopfAlgebra.antipode_comp_mul_comp_comm** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgebra
`。
形式化陈述：antipode_comp_mul_comp_comm : antipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.co
mm R A A).toLinearMap = .mul' R A ∘ₗ map (antipode R) (antipode R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Coalgebra.Repr.convMul_apply`：∀ {R : Type u_1} {A : Type u_3} {C : Type 
u_5} {ι : Type u_6} [inst : CommSemiring R]   [inst_1 : NonUnitalNonAssocSemirin
g A] [inst_2 : _ro…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Coalgebra.Repr.tmul_index`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3
} {ι : Type u_4} {κ : Type u_5} [inst : CommSemiring R]   [inst_1 : Semiring A] 
[inst_2 : Bialg…
· 使用定理 `Coalgebra.Repr.tmul_left`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3}
 {ι : Type u_4} {κ : Type u_5} [inst : CommSemiring R]   [inst_1 : Semiring A] [
inst_2 : Bialg…
· 使用定理 `Coalgebra.Repr.tmul_right`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3
} {ι : Type u_4} {κ : Type u_5} [inst : CommSemiring R]   [inst_1 : Semiring A] 
[inst_2 : Bialg…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit`：sum_antipode_mul_eq_a
lgebraMap_counit (repr : Repr R a ι) : ∑ i in repr.index, antipode R (repr.left 
i) * repr.right i = algebraMap R A (cou…
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `Coalgebra.Repr.mul_index`：∀ {R : Type u_1} {A : Type u_2} {ι : Type u_4}
 {κ : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Bialge
bra R A] {a b …
· 使用定理 `Finset.map_swap_product`：map_swap_product (s : Finset α) (t : Finset β) 
: (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t
· 使用定理 `Coalgebra.Repr.mul_left`：∀ {R : Type u_1} {A : Type u_2} {ι : Type u_4} 
{κ : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Bialgeb
ra R A] {a b …
· 使用定理 `Coalgebra.Repr.mul_right`：∀ {R : Type u_1} {A : Type u_2} {ι : Type u_4}
 {κ : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Bialge
bra R A] {a b …
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
（共 37 条，此处仅展示前 30 条）
-/
lemma antipode_comp_mul_comp_comm :
    antipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.comm R A A).toLinearMap =
      .mul' R A ∘ₗ map (antipode R) (antipode R) := by
  apply WithConv.toConv_injective
  apply left_inv_eq_right_inv (a := toConv <| LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A) <;>
    ext a b
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply, ← Bialgebra.counit_mul,
      ← sum_antipode_mul_eq_algebraMap_counit ((ℛ R b).mul (ℛ R a)),
      ← Finset.map_swap_product (ℛ R b).index (ℛ R a).index]
  · simp [((ℛ R a).tmul (ℛ R b)).convMul_apply,
      ← Finset.map_swap_product (ℛ R a).index (ℛ R b).index,
      Finset.sum_product (ℛ R b).index, ← Finset.mul_sum, mul_assoc ((ℛ R b).left _),
      ← mul_assoc ((ℛ R a).left _), ← Finset.sum_mul, sum_mul_antipode_eq_algebraMap_counit,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).left_comm,
      ← (Algebra.commute_algebraMap_left (ε a) (_ : A)).eq]
/-
**HopfAlgebra.antipode_mul_antidistrib** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgebra`。
形式化陈述：antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * a
ntipode R a
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `HopfAlgebra.antipode_comp_mul_comp_comm`：antipode_comp_mul_comp_comm : a
ntipode R ∘ₗ .mul' R A ∘ₗ (TensorProduct.comm R A A).toLinearMap = .mul' R A ∘ₗ 
map (antipode R) (antipode R)
-/
lemma antipode_mul_antidistrib (a b : A) : antipode R (a * b) = antipode R b * antipode R a := by
  exact congr($antipode_comp_mul_comp_comm (b ⊗ₜ a))

@[deprecated (since := "2026-06-05")] alias antipode_mul := antipode_mul_antidistrib

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an anti-algebra hom. -/
@[expose, simps!]
/-
**HopfAlgebra.antipodeAlgHomOp** 是 Mathlib 中的一个定义，位于命名空间 `HopfAlgebra`。
形式化陈述：antipodeAlgHomOp : A ->ₐ[R] Aᵐᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antipode of a commutative Hopf algebra as an anti-algebra hom.
-/
def antipodeAlgHomOp : A →ₐ[R] Aᵐᵒᵖ := .ofLinearMap
    ((MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ antipode R)
    (MulOpposite.op_injective (by simp))
    (fun x y ↦ MulOpposite.op_injective (by simp [antipode_mul_antidistrib]))

end Semiring

variable [CommSemiring A] [HopfAlgebra R A]

/-
**HopfAlgebra.antipode_mul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `HopfAlgebra`。
形式化陈述：antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antip
ode R b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HopfAlgebra.antipode_mul_antidistrib`：antipode_mul_antidistrib (a b : A)
 : antipode R (a * b) = antipode R b * antipode R a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma antipode_mul_distrib (a b : A) : antipode R (a * b) = antipode R a * antipode R b := by
  rw [antipode_mul_antidistrib, mul_comm]

variable (R A) in
/-- The antipode of a commutative Hopf algebra as an algebra hom. -/
@[expose, simps!]
/-
**HopfAlgebra.antipodeAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `HopfAlgebra`。
形式化陈述：antipodeAlgHom : A ->ₐ[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HopfAlgebra.antipode_mul_distrib`：antipode_mul_distrib (a b : A) : antip
ode R (a * b) = antipode R a * antipode R b

--- 原说明 ---
The antipode of a commutative Hopf algebra as an algebra hom.
-/
def antipodeAlgHom : A →ₐ[R] A := .ofLinearMap (antipode R) antipode_one antipode_mul_distrib
/-
**HopfAlgebra.toLinearMap_antipodeAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `HopfAlgebra`
。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : HopfAlgebra R A],   (HopfAlgebra.antipodeAlgHom R A).toLinearM
ap = HopfAlgebraStruct.antipode R
参数：HopfAlgebra.antipodeAlgHom R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearMap_antipodeAlgHom : (antipodeAlgHom R A).toLinearMap = antipode R := rfl

end HopfAlgebra

namespace LinearMap

variable [Semiring C] [HopfAlgebra R C]

/-
**LinearMap.antipode_mul_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {C : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring
 C] [inst_2 : HopfAlgebra R C],   WithConv.toConv (HopfAlgebraStruct.antipode R)
 * WithConv.toConv LinearMap.id = 1
参数：HopfAlgebraStruct.antipode R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coalgebra.Repr.convMul_apply`：∀ {R : Type u_1} {A : Type u_3} {C : Type 
u_5} {ι : Type u_6} [inst : CommSemiring R]   [inst_1 : NonUnitalNonAssocSemirin
g A] [inst_2 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit`：sum_antipode_mul_eq_a
lgebraMap_counit (repr : Repr R a ι) : ∑ i in repr.index, antipode R (repr.left 
i) * repr.right i = algebraMap R A (cou…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma antipode_mul_id : toConv (antipode R (A := C)) * toConv id = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_antipode_mul_eq_algebraMap_counit (ℛ R c)]
/-
**LinearMap.id_mul_antipode** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {C : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring
 C] [inst_2 : HopfAlgebra R C],   WithConv.toConv LinearMap.id * WithConv.toConv
 (HopfAlgebraStruct.antipode R) = 1
参数：HopfAlgebraStruct.antipode R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Coalgebra.Repr.convMul_apply`：∀ {R : Type u_1} {A : Type u_3} {C : Type 
u_5} {ι : Type u_6} [inst : CommSemiring R]   [inst_1 : NonUnitalNonAssocSemirin
g A] [inst_2 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit`：sum_mul_antipode_eq_a
lgebraMap_counit (repr : Repr R a ι) : ∑ i in repr.index, repr.left i * antipode
 R (repr.right i) = algebraMap R A (cou…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma id_mul_antipode : toConv id * toConv (antipode R (A := C)) = 1 := by
  ext c; rw [(ℛ R c).convMul_apply]; simp [sum_mul_antipode_eq_algebraMap_counit (ℛ R c)]

end LinearMap

namespace LinearMap
variable [Semiring C] [HopfAlgebra R C]

local notation "𝑺" => antipode R (A := C)
local notation "𝑭" => δ ∘ₗ 𝑺
local notation "𝑮" => (𝑺 ⊗ₘ 𝑺) ∘ₗ TensorProduct.comm R C C ∘ₗ δ

/-
**LinearMap.comul_right_inv** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：comul_right_inv : toConv δ * toConv 𝑭 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `Bialgebra.comul_mul`：comul_mul (a b : A) : comul (R
· 使用定理 `LinearMap.id_mul_antipode`：∀ {R : Type u_1} {C : Type u_3} [inst : CommS
emiring R] [inst_1 : Semiring C] [inst_2 : HopfAlgebra R C],   WithConv.toConv L
inearMap.id * W…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Bialgebra.comul_one`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R}
 {inst_1 : Semiring A} [self : Bialgebra R A],   CoalgebraStruct.comul 1 = 1
-/
lemma comul_right_inv : toConv δ * toConv 𝑭 = 1 := by
  apply WithConv.ext
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, ofConv_toConv]
  calc μ ∘ₗ map δ (δ ∘ₗ 𝑺) ∘ₗ δ
      = μ ∘ₗ ((δ ∘ₗ id) ⊗ₘ (δ ∘ₗ 𝑺)) ∘ₗ δ := rfl
    _ = μ ∘ₗ (δ ⊗ₘ δ) ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ := by
        simp only [_root_.TensorProduct.map_comp, comp_assoc]
    _ = δ ∘ₗ μ ∘ₗ (id ⊗ₘ 𝑺) ∘ₗ δ := by
        have : (μ ∘ₗ (δ ⊗ₘ δ) : C ⊗[R] C →ₗ[R] C ⊗[R] C) = δ ∘ₗ μ := by ext; simp
        simp [this, ← comp_assoc]
    _ = δ ∘ₗ (toConv id * toConv 𝑺).ofConv := by simp [LinearMap.convMul_def]
    _ = δ ∘ₗ (1 : WithConv (C →ₗ[R] C)).ofConv := by rw [id_mul_antipode]
    _ = η ∘ₗ ε := by
        simp [LinearMap.convOne_def, show (δ ∘ₗ η : R →ₗ[R] C ⊗[R] C) = η by ext; simp; rfl,
          ← comp_assoc]

end LinearMap

namespace AlgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R C] [HopfAlgebra R A]

/-
**AlgHom.convInv** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：convInv : Inv (WithConv <| A ->ₐ[R] C) where inv f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance convInv : Inv (WithConv <| A →ₐ[R] C) where
  inv f := toConv <| f.ofConv.comp (HopfAlgebra.antipodeAlgHom R A)
/-
**AlgHom.convGroup** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
形式化陈述：convGroup : Group (WithConv <| A ->ₐ[R] C) where inv_mul_cancel f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance convGroup : Group (WithConv <| A →ₐ[R] C) where
  inv_mul_cancel f := by
    have H : (lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv) =
      f.ofConv.comp (lmul' R) := by ext <;> simp
    trans toConv <| ((lmul' R).comp (Algebra.TensorProduct.map f.ofConv f.ofConv)).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R A) (.id _ _)).comp (comulAlgHom R A))
    · rw [AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.map f.ofConv f.ofConv),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change f.ofConv.toLinearMap.comp (toConv (antipode R (A := A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| A →ₗ[R] C)
    rw [LinearMap.antipode_mul_id]
    ext
    simp
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsCocomm R A] : CommGroup (WithConv <| A →ₐ[R] C) where
/-
**AlgHom.antipode_id_cancel** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：antipode_id_cancel : toConv (HopfAlgebra.antipodeAlgHom R A) * toConv (Alg
Hom.id R A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithConv.ofConv_injective`：ofConv_injective : Function.Injective (@ofCon
v A)
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgHom.toLinearMap_convMul`：toLinearMap_convMul (f g : WithConv <| C ->ₐ
[R] A) : toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toCon
v g.ofConv.toLin…
· 使用引理 `AlgHom.toLinearMap_convOne`：toLinearMap_convOne : toConv (1 : WithConv <
| C ->ₐ[R] A).ofConv.toLinearMap = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.antipode_mul_id`：∀ {R : Type u_1} {C : Type u_3} [inst : CommS
emiring R] [inst_1 : Semiring C] [inst_2 : HopfAlgebra R C],   WithConv.toConv (
HopfAlgebraStru…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma antipode_id_cancel :
    toConv (HopfAlgebra.antipodeAlgHom R A) * toConv (AlgHom.id R A) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  simp [LinearMap.antipode_mul_id]
/-
**AlgHom.counitAlgHom_comp_antipodeAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom`。
形式化陈述：counitAlgHom_comp_antipodeAlgHom : (counitAlgHom R A).comp (HopfAlgebra.an
tipodeAlgHom R A) = counitAlgHom R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HopfAlgebra.counit_comp_antipode`：∀ {R : Type u} {A : Type v} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A],   CoalgebraStruc
t.counit ∘ₗ HopfAlgebr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma counitAlgHom_comp_antipodeAlgHom :
    (counitAlgHom R A).comp (HopfAlgebra.antipodeAlgHom R A) = counitAlgHom R A :=
  AlgHom.toLinearMap_injective <| by simp

end AlgHom

