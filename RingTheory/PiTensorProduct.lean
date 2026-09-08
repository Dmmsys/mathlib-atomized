/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Data.Finset.NoncommProd

/-!
# Tensor product of `R`-algebras and rings

If `(Aᵢ)` is a family of `R`-algebras then the `R`-tensor product `⨂ᵢ Aᵢ` is an `R`-algebra as well
with structure map defined by `r ↦ r • 1`.

In particular if we take `R` to be `ℤ`, then this collapses into the tensor product of rings.
-/

@[expose] public section

open TensorProduct Function

variable {ι R' R : Type*} {A : ι → Type*}

namespace PiTensorProduct

noncomputable section AddCommMonoidWithOne

variable [CommSemiring R] [∀ i, AddCommMonoidWithOne (A i)] [∀ i, Module R (A i)]

/-
**PiTensorProduct.instOne** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instOne : One (⨂[R] i, A i) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (⨂[R] i, A i) where
  one := tprod R 1
/-
**PiTensorProduct.one_def** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：one_def : 1 = tprod R (1 : Π i, A i)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def : 1 = tprod R (1 : Π i, A i) := rfl
/-
**PiTensorProduct.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorPr
oduct`。
形式化陈述：instAddCommMonoidWithOne : AddCommMonoidWithOne (⨂[R] i, A i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne : AddCommMonoidWithOne (⨂[R] i, A i) where
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  __ := instOne

end AddCommMonoidWithOne

noncomputable section NonUnitalNonAssocSemiring

variable [CommSemiring R] [∀ i, NonUnitalNonAssocSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

attribute [aesop safe] mul_add mul_smul_comm smul_mul_assoc add_mul in
/--
The multiplication in tensor product of rings is induced by `(xᵢ) * (yᵢ) = (xᵢ * yᵢ)`
-/
/-
**PiTensorProduct.mul** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：mul : (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i) ->ₗ[R] (⨂[R] i, A i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication in tensor product of rings is induced by `(xᵢ) * (yᵢ) = (xᵢ *
 yᵢ)`
-/
def mul : (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) →ₗ[R] (⨂[R] i, A i) :=
  PiTensorProduct.piTensorHomMap₂ <| tprod R fun _ ↦ LinearMap.mul _ _
/-
**PiTensorProduct.mul_tprod_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
   [inst_1 : (i : ι) → NonUnitalNonAssocSemiring (A i)] [inst_2 : (i : ι) → _roo
t_.Module R (A i)]   [inst_3 : ∀ (i : ι), SMulCommClass R (A i) (A i)] [inst_4 :
 ∀ (i : ι), IsScalarTower R (A i) (A i)]   (x y : (i : ι) → A i),   (PiTensorPro
duct.mul ((PiTensorProduct.tprod R) x)) ((PiTensorProduct.tprod R) y) = (PiTenso
rProduct.tprod R) (x * y)
参数：i : ι；A i；i : ι；A i；i : ι；A i；A i；i : ι；A i；A i；x y : (i : ι) → A i；PiTensorP
roduct.mul ((PiTensorProduct.tprod R) x)；(PiTensorProduct.tprod R) y；PiTensorPro
duct.tprod R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.piTensorHomMap₂_tprod_tprod_tprod`：∀ {ι : Type u_1} {R :
 Type u_4} [inst : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCom
mMonoid (s i)]   [inst_2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mul_tprod_tprod (x y : (i : ι) → A i) :
    mul (tprod R x) (tprod R y) = tprod R (x * y) := by
  simp only [mul, piTensorHomMap₂_tprod_tprod_tprod, LinearMap.mul_apply', Pi.mul_def]
/-
**PiTensorProduct.instMul** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instMul : Mul (⨂[R] i, A i) where mul x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (⨂[R] i, A i) where
  mul x y := mul x y
/-
**PiTensorProduct.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：mul_def (x y : ⨂[R] i, A i) : x * y = mul x y
参数：x y : ⨂[R] i, A i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def (x y : ⨂[R] i, A i) : x * y = mul x y := rfl
/-
**PiTensorProduct.tprod_mul_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
   [inst_1 : (i : ι) → NonUnitalNonAssocSemiring (A i)] [inst_2 : (i : ι) → _roo
t_.Module R (A i)]   [inst_3 : ∀ (i : ι), SMulCommClass R (A i) (A i)] [inst_4 :
 ∀ (i : ι), IsScalarTower R (A i) (A i)]   (x y : (i : ι) → A i), (PiTensorProdu
ct.tprod R) x * (PiTensorProduct.tprod R) y = (PiTensorProduct.tprod R) (x * y)
参数：i : ι；A i；i : ι；A i；i : ι；A i；A i；i : ι；A i；A i；x y : (i : ι) → A i；PiTensorP
roduct.tprod R；PiTensorProduct.tprod R；PiTensorProduct.tprod R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mul_tprod_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
-/
@[simp] lemma tprod_mul_tprod (x y : (i : ι) → A i) :
    tprod R x * tprod R y = tprod R (x * y) :=
  mul_tprod_tprod x y
/-
**PiTensorProduct._root_.SemiconjBy.tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorPro
duct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SemiconjBy.tprod {a₁ a₂ a₃ : Π i, A i}
    (ha : SemiconjBy a₁ a₂ a₃) :
    SemiconjBy (tprod R a₁) (tprod R a₂) (tprod R a₃) := by
  rw [SemiconjBy, tprod_mul_tprod, tprod_mul_tprod, ha]

nonrec theorem _root_.Commute.tprod {a₁ a₂ : Π i, A i} (ha : Commute a₁ a₂) :
    Commute (tprod R a₁) (tprod R a₂) :=
  ha.tprod

set_option backward.isDefEq.respectTransparency false in
/-
**PiTensorProduct.smul_tprod_mul_smul_tprod** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorP
roduct`。
形式化陈述：smul_tprod_mul_smul_tprod (r s : R) (x y : Π i, A i) : (r • tprod R x) * (
s • tprod R y) = (r * s) • tprod R (x * y)
参数：r s : R；x y : Π i, A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PiTensorProduct.mul_tprod_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_tprod_mul_smul_tprod (r s : R) (x y : Π i, A i) :
    (r • tprod R x) * (s • tprod R y) = (r * s) • tprod R (x * y) := by
  simp only [mul_def, map_smul, LinearMap.smul_apply, mul_tprod_tprod, mul_comm r s, mul_smul]
/-
**PiTensorProduct.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `PiTen
sorProduct`。
形式化陈述：instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (⨂[R] i, A i) wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (⨂[R] i, A i) where
  __ := instMul
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  left_distrib _ _ _ := (mul _).map_add _ _
  right_distrib _ _ _ := mul.map_add₂ _ _ _
  zero_mul _ := mul.map_zero₂ _
  mul_zero _ := map_zero (mul _)

end NonUnitalNonAssocSemiring

noncomputable section NonAssocSemiring

variable [CommSemiring R] [∀ i, NonAssocSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

/-
**PiTensorProduct.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → NonAssocSemiring (A i)]   [inst_2 : (i : ι) → _root_.Module
 R (A i)] [inst_3 : ∀ (i : ι), SMulCommClass R (A i) (A i)]   [inst_4 : ∀ (i : ι
), IsScalarTower R (A i) (A i)] (x : PiTensorProduct R fun i => A i),   (PiTenso
rProduct.mul ((PiTensorProduct.tprod R) 1)) x = x
参数：i : ι；A i；i : ι；A i；i : ι；A i；A i；i : ι；A i；A i；x : PiTensorProduct R fun i =
> A i；PiTensorProduct.mul ((PiTensorProduct.tprod R) 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PiTensorProduct.mul_tprod_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
protected lemma one_mul (x : ⨂[R] i, A i) : mul (tprod R 1) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [map_add, h1, h2]
/-
**PiTensorProduct.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → NonAssocSemiring (A i)]   [inst_2 : (i : ι) → _root_.Module
 R (A i)] [inst_3 : ∀ (i : ι), SMulCommClass R (A i) (A i)]   [inst_4 : ∀ (i : ι
), IsScalarTower R (A i) (A i)] (x : PiTensorProduct R fun i => A i),   (PiTenso
rProduct.mul x) ((PiTensorProduct.tprod R) 1) = x
参数：i : ι；A i；i : ι；A i；i : ι；A i；A i；i : ι；A i；A i；x : PiTensorProduct R fun i =
> A i；PiTensorProduct.mul x；(PiTensorProduct.tprod R) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.induction_on`：∀ {ι : Type u_1} {R : Type u_4} [inst : Co
mmSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [ins
t_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PiTensorProduct.mul_tprod_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
protected lemma mul_one (x : ⨂[R] i, A i) : mul x (tprod R 1) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod => simp
  | add _ _ h1 h2 => simp [h1, h2]
/-
**PiTensorProduct.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduc
t`。
形式化陈述：instNonAssocSemiring : NonAssocSemiring (⨂[R] i, A i) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.one_mul`：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u
_4} [inst : CommSemiring R] [inst_1 : (i : ι) → NonAssocSemiring (A i)]   [inst_
2 : (i : ι) →…
· 使用定理 `PiTensorProduct.mul_one`：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u
_4} [inst : CommSemiring R] [inst_1 : (i : ι) → NonAssocSemiring (A i)]   [inst_
2 : (i : ι) →…
-/
instance instNonAssocSemiring : NonAssocSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  one_mul := PiTensorProduct.one_mul
  mul_one := PiTensorProduct.mul_one

variable (R) in
/-- `PiTensorProduct.tprod` as a `MonoidHom`. -/
@[simps]
/-
**PiTensorProduct.tprodMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：tprodMonoidHom : (Π i, A i) ->* ⨂[R] i, A i where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PiTensorProduct.tprod` as a `MonoidHom`.
-/
def tprodMonoidHom : (Π i, A i) →* ⨂[R] i, A i where
  toFun := tprod R
  map_one' := rfl
  map_mul' x y := (tprod_mul_tprod x y).symm

end NonAssocSemiring

noncomputable section NonUnitalSemiring

variable [CommSemiring R] [∀ i, NonUnitalSemiring (A i)]
variable [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

/-
**PiTensorProduct.mul_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → NonUnitalSemiring (A i)]   [inst_2 : (i : ι) → _root_.Modul
e R (A i)] [inst_3 : ∀ (i : ι), SMulCommClass R (A i) (A i)]   [inst_4 : ∀ (i : 
ι), IsScalarTower R (A i) (A i)] (x y z : PiTensorProduct R fun i => A i),   (Pi
TensorProduct.mul ((PiTensorProduct.mul x) y)) z = (PiTensorProduct.mul x) ((PiT
ensorProduct.mul y) z)
参数：i : ι；A i；i : ι；A i；i : ι；A i；A i；i : ι；A i；A i；x y z : PiTensorProduct R fun
 i => A i；PiTensorProduct.mul ((PiTensorProduct.mul x) y)；PiTensorProduct.mul x；
(PiTensorProduct.mul y) z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiTensorProduct.tprod_mul_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected lemma mul_assoc (x y z : ⨂[R] i, A i) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip.toLinearMap <|
        LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext x y z
  dsimp [← mul_def]
  simpa only [tprod_mul_tprod] using congr_arg (tprod R) (mul_assoc x y z)
/-
**PiTensorProduct.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：instNonUnitalSemiring : NonUnitalSemiring (⨂[R] i, A i) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mul_assoc`：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type
 u_4} [inst : CommSemiring R] [inst_1 : (i : ι) → NonUnitalSemiring (A i)]   [in
st_2 : (i : ι) …
-/
instance instNonUnitalSemiring : NonUnitalSemiring (⨂[R] i, A i) where
  __ := instNonUnitalNonAssocSemiring
  mul_assoc := PiTensorProduct.mul_assoc

end NonUnitalSemiring

noncomputable section Semiring

variable [CommSemiring R'] [CommSemiring R] [∀ i, Semiring (A i)]
variable [Algebra R' R] [∀ i, Algebra R (A i)] [∀ i, Algebra R' (A i)]
variable [∀ i, IsScalarTower R' R (A i)]

/-
**PiTensorProduct.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instSemiring : Semiring (⨂[R] i, A i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring : Semiring (⨂[R] i, A i) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
/-
**PiTensorProduct.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instAlgebra : Algebra R' (⨂[R] i, A i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra R' (⨂[R] i, A i) where
  __ := hasSMul'
  algebraMap :=
  { toFun := (· • 1)
    map_one' := by simp
    map_mul' r s := show (r * s) • 1 = mul (r • 1) (s • 1) by
      rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, mul_comm,
        mul_smul]
      congr
      change (1 : ⨂[R] i, A i) = 1 * 1
      rw [mul_one]
    map_zero' := by simp
    map_add' := by simp [add_smul] }
  commutes' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change mul _ _ = mul _ _
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    change r • (1 * x) = r • (x * 1)
    rw [mul_one, one_mul]
  smul_def' r x := by
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    change _ = mul _ _
    rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]
    change _ = r • (1 * x)
    rw [one_mul]
/-
**PiTensorProduct.algebraMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiTensorProduct`。
形式化陈述：algebraMap_apply (r : R') (i : ι) [DecidableEq ι] : algebraMap R' (⨂[R] i,
 A i) r = tprod R (Pi.mulSingle i (algebraMap R' (A i) r))
参数：r : R'；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Pi.one_def`：one_def : (1 : forall i, M i) = fun _ => 1
-/
lemma algebraMap_apply (r : R') (i : ι) [DecidableEq ι] :
    algebraMap R' (⨂[R] i, A i) r = tprod R (Pi.mulSingle i (algebraMap R' (A i) r)) := by
  change r • tprod R 1 = _
  have : Pi.mulSingle i (algebraMap R' (A i) r) = update (fun i ↦ 1) i (r • 1) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [this, ← smul_one_smul R r (1 : A i), MultilinearMap.map_update_smul, update_eq_self,
    smul_one_smul, Pi.one_def]

/--
The map `Aᵢ ⟶ ⨂ᵢ Aᵢ` given by `a ↦ 1 ⊗ ... ⊗ a ⊗ 1 ⊗ ...`
-/
@[simps]
/-
**PiTensorProduct.singleAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：singleAlgHom [DecidableEq ι] (i : ι) : A i ->ₐ[R] ⨂[R] i, A i where toFun 
a
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Aᵢ ⟶ ⨂ᵢ Aᵢ` given by `a ↦ 1 ⊗ ... ⊗ a ⊗ 1 ⊗ ...`
-/
def singleAlgHom [DecidableEq ι] (i : ι) : A i →ₐ[R] ⨂[R] i, A i where
  toFun a := tprod R (MonoidHom.mulSingle _ i a)
  map_one' := by simp only [map_one]; rfl
  map_mul' a a' := by simp [map_mul]
  map_zero' := MultilinearMap.map_update_zero _ _ _
  map_add' _ _ := MultilinearMap.map_update_add _ _ _ _ _
  commutes' r := show tprodCoeff R _ _ = r • tprodCoeff R _ _ by
    rw [Algebra.algebraMap_eq_smul_one, ← Pi.one_apply, MonoidHom.mulSingle_apply, Pi.mulSingle,
      smul_tprodCoeff]
    rfl

/--
Lifting a multilinear map to an algebra homomorphism from tensor product
-/
@[simps!]
/-
**PiTensorProduct.liftAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：liftAlgHom {S : Type*} [Semiring S] [Algebra R S] (f : MultilinearMap R A 
S) (one : f 1 = 1) (mul : forall x y, f (x * y) = f x * f y) : (⨂[R] i, A i) ->ₐ
[R] S
参数：f : MultilinearMap R A S；one : f 1 = 1；mul : forall x y, f (x * y) = f x * f 
y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting a multilinear map to an algebra homomorphism from tensor product
-/
def liftAlgHom {S : Type*} [Semiring S] [Algebra R S]
    (f : MultilinearMap R A S)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : (⨂[R] i, A i) →ₐ[R] S :=
  AlgHom.ofLinearMap (lift f) (show lift f (tprod R 1) = 1 by simp [one]) <|
    LinearMap.map_mul_iff _ |>.mpr <| by aesop
/-
**PiTensorProduct.tprod_noncommProd** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → Semiring (A i)]   [inst_2 : (i : ι) → Algebra R (A i)] {κ :
 Type u_5} (s : Finset κ) (x : κ → (i : ι) → A i)   (hx : (↑s).Pairwise (Functio
n.onFun Commute x)),   (PiTensorProduct.tprod R) (s.noncommProd x hx) = s.noncom
mProd (fun k => (PiTensorProduct.tprod R) (x k)) ⋯
参数：i : ι；A i；i : ι；A i；s : Finset κ；x : κ → (i : ι) → A i；hx : (↑s).Pairwise (Fu
nction.onFun Commute x)；PiTensorProduct.tprod R；s.noncommProd x hx；fun k => (PiT
ensorProduct.tprod R) (x k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_noncommProd`：map_noncommProd [MonoidHomClass F β γ] (s : Fins
et α) (f : α -> β) (comm) (g : F) : g (s.noncommProd f comm) = s.noncommProd (fu
n i => g (f …
-/
@[simp] lemma tprod_noncommProd {κ : Type*} (s : Finset κ) (x : κ → Π i, A i) (hx) :
    tprod R (s.noncommProd x hx) = s.noncommProd (fun k => tprod R (x k))
      (hx.imp fun _ _ => Commute.tprod) :=
  Finset.map_noncommProd s x _ (tprodMonoidHom R)

/-- To show two algebra morphisms from finite tensor products are equal, it suffices to show that
they agree on elements of the form $1 ⊗ ⋯ ⊗ a ⊗ 1 ⊗ ⋯$. -/
@[ext high]
/-
**PiTensorProduct.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：algHom_ext {S : Type*} [Finite ι] [DecidableEq ι] [Semiring S] [Algebra R 
S] ⦃f g : (⨂[R] i, A i) ->ₐ[R] S⦄ (h : forall i, f.comp (singleAlgHom i) = g.com
p (singleAlgHom i)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `MonoidHom.pi_ext`：∀ {ι : Type u_2} {γ : Type u_5} [inst : Monoid γ] {M :
 ι → Type u_6} [inst_1 : (i : ι) → Monoid (M i)] [Finite ι]   [inst_3 : Decidabl
eEq ι]…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
To show two algebra morphisms from finite tensor products are equal, it suffices
 to show that
they agree on elements of the form $1 ⊗ ⋯ ⊗ a ⊗ 1 ⊗ ⋯$.
-/
theorem algHom_ext {S : Type*} [Finite ι] [DecidableEq ι] [Semiring S] [Algebra R S]
    ⦃f g : (⨂[R] i, A i) →ₐ[R] S⦄ (h : ∀ i, f.comp (singleAlgHom i) = g.comp (singleAlgHom i)) :
    f = g :=
  AlgHom.toLinearMap_injective <| PiTensorProduct.ext <| MultilinearMap.ext fun x =>
    suffices f.toMonoidHom.comp (tprodMonoidHom R) = g.toMonoidHom.comp (tprodMonoidHom R) from
      DFunLike.congr_fun this x
    MonoidHom.pi_ext fun i xi => DFunLike.congr_fun (h i) xi

end Semiring

noncomputable section Ring

variable [CommRing R] [∀ i, Ring (A i)] [∀ i, Algebra R (A i)]

/-
**PiTensorProduct.instRing** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instRing : Ring (⨂[R] i, A i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing : Ring (⨂[R] i, A i) where
  __ := instSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

end Ring

noncomputable section CommSemiring

variable [CommSemiring R] [∀ i, CommSemiring (A i)] [∀ i, Algebra R (A i)]

/-
**PiTensorProduct.mul_comm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → CommSemiring (A i)]   [inst_2 : (i : ι) → Algebra R (A i)] 
(x y : PiTensorProduct R fun i => A i),   (PiTensorProduct.mul x) y = (PiTensorP
roduct.mul y) x
参数：i : ι；A i；i : ι；A i；x y : PiTensorProduct R fun i => A i；PiTensorProduct.mul 
x；PiTensorProduct.mul y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.mul_tprod_tprod`：∀ {ι : Type u_1} {R : Type u_3} {A : ι 
→ Type u_4} [inst : CommSemiring R]   [inst_1 : (i : ι) → NonUnitalNonAssocSemir
ing (A i)] [inst_2 : …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected lemma mul_comm (x y : ⨂[R] i, A i) : mul x y = mul y x := by
  suffices mul (R := R) (A := A) = mul.flip from
    DFunLike.congr_fun (DFunLike.congr_fun this x) y
  ext x y
  dsimp
  simp only [mul_tprod_tprod, mul_tprod_tprod, mul_comm x y]
/-
**PiTensorProduct.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instCommSemiring : CommSemiring (⨂[R] i, A i) where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.mul_comm`：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type 
u_4} [inst : CommSemiring R] [inst_1 : (i : ι) → CommSemiring (A i)]   [inst_2 :
 (i : ι) → Alg…
-/
instance instCommSemiring : CommSemiring (⨂[R] i, A i) where
  __ := instSemiring
  __ := (inferInstance : AddCommMonoid (⨂[R] i, A i))
  mul_comm := PiTensorProduct.mul_comm
/-
**PiTensorProduct.tprod_prod** 是 Mathlib 中的一个定理，位于命名空间 `PiTensorProduct`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : ι → Type u_4} [inst : CommSemiring R]
 [inst_1 : (i : ι) → CommSemiring (A i)]   [inst_2 : (i : ι) → Algebra R (A i)] 
{κ : Type u_5} (s : Finset κ) (x : κ → (i : ι) → A i),   (PiTensorProduct.tprod 
R) (∏ k ∈ s, x k) = ∏ k ∈ s, (PiTensorProduct.tprod R) (x k)
参数：i : ι；A i；i : ι；A i；s : Finset κ；x : κ → (i : ι) → A i；PiTensorProduct.tprod 
R；∏ k ∈ s, x k；PiTensorProduct.tprod R；x k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
@[simp] lemma tprod_prod {κ : Type*} (s : Finset κ) (x : κ → Π i, A i) :
    tprod R (∏ k ∈ s, x k) = ∏ k ∈ s, tprod R (x k) :=
  map_prod (tprodMonoidHom R) x s

section

variable [Fintype ι]

variable (R ι)

/--
The algebra equivalence from the tensor product of the constant family with
value `R` to `R`, given by multiplication of the entries.
-/
/-
**PiTensorProduct.constantBaseRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProdu
ct`。
形式化陈述：constantBaseRingEquiv : (⨂[R] _ : ι, R) ≃ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra equivalence from the tensor product of the constant family with
value `R` to `R`, given by multiplication of the entries.
-/
noncomputable def constantBaseRingEquiv : (⨂[R] _ : ι, R) ≃ₐ[R] R :=
  letI toFun := lift (MultilinearMap.mkPiAlgebra R ι R)
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap
      toFun
      ((lift.tprod _).trans Finset.prod_const_one)
      (by
        -- one of these is required, the other is a performance optimization
        let : IsScalarTower R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          IsScalarTower.right (R := R) (A := ⨂[R] (x : ι), R)
        let : SMulCommClass R (⨂[R] x : ι, R) (⨂[R] x : ι, R) :=
          Algebra.to_smulCommClass (R := R) (A := ⨂[R] x : ι, R)
        rw [LinearMap.map_mul_iff]
        ext
        change toFun (tprod R _ * tprod R _) = toFun (tprod R _) * toFun (tprod R _)
        simp_rw [tprod_mul_tprod, toFun, lift.tprod, MultilinearMap.mkPiAlgebra_apply,
          Pi.mul_apply, Finset.prod_mul_distrib]))
    (Algebra.ofId _ _)
    (by ext)
    (by classical ext)

variable {R ι}

@[simp]
/-
**PiTensorProduct.constantBaseRingEquiv_tprod** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：constantBaseRingEquiv_tprod (x : ι -> R) : constantBaseRingEquiv ι R (tpro
d R x) = ∏ i, x i
参数：x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `AlgHom.ofLinearMap_apply`：∀ {R : Type u} {A : Type v} {B : Type w} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algeb
ra R A] [inst_…
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantBaseRingEquiv_tprod (x : ι → R) :
    constantBaseRingEquiv ι R (tprod R x) = ∏ i, x i := by
  simp [constantBaseRingEquiv]

@[simp]
/-
**PiTensorProduct.constantBaseRingEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `PiTensor
Product`。
形式化陈述：constantBaseRingEquiv_symm (r : R) : (constantBaseRingEquiv ι R).symm r = 
algebraMap _ _ r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem constantBaseRingEquiv_symm (r : R) :
    (constantBaseRingEquiv ι R).symm r = algebraMap _ _ r := rfl

end

end CommSemiring

noncomputable section CommRing

variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
/-
**PiTensorProduct.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `PiTensorProduct`。
形式化陈述：instCommRing : CommRing (⨂[R] i, A i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing (⨂[R] i, A i) where
  __ := instCommSemiring
  __ := (inferInstance : AddCommGroup (⨂[R] i, A i))

end CommRing

end PiTensorProduct

