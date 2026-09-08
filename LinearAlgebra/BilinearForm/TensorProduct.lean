/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The bilinear form on a tensor product

## Main definitions

* `LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by
  applying `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.BilinMap.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite
  free modules.

-/

@[expose] public section

universe u v w uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open TensorProduct

namespace LinearMap

open LinearMap (BilinMap BilinForm)

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

namespace BilinMap

variable (R A) in
/-- The tensor product of two bilinear maps injects into bilinear maps on tensor products.

Note this is heterobasic; the bilinear map on the left can take values in a module over a
(commutative) algebra over the ring of the module in which the right bilinear map is valued. -/
/-
**LinearMap.BilinMap.tensorDistrib** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinMap
`。
形式化陈述：tensorDistrib : (BilinMap A M₁ N₁ otimes[R] BilinMap R M₂ N₂) ->ₗ[A] Bilin
Map A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two bilinear maps injects into bilinear maps on tensor pro
ducts.

Note this is heterobasic; the bilinear map on the left can take values in a modu
le over a
(commutative) algebra over the ring of the module in which the right bilinear ma
p is valued.
-/
def tensorDistrib :
    (BilinMap A M₁ N₁ ⊗[R] BilinMap R M₂ N₂) →ₗ[A] BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  (TensorProduct.lift.equiv (.id A) (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _ _ _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv (.id A) M₁ M₁ N₁)
    (TensorProduct.lift.equiv (.id R) _ _ _)).toLinearMap

@[simp]
/-
**LinearMap.BilinMap.tensorDistrib_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：tensorDistrib_tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M
₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) : tensorDistrib R A (B₁ otimesₜ B₂) (m₁ otime
sₜ m₂) (m₁' otimesₜ m₂') = B₁ m₁ m₁' otimesₜ B₂ m₂ m₂'
参数：B₁ : BilinMap A M₁ N₁；B₂ : BilinMap R M₂ N₂；m₁ : M₁；m₂ : M₂；m₁' : M₁；m₂' : M₂
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem tensorDistrib_tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₁ m₁ m₁' ⊗ₜ B₂ m₂ m₂' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
/-
**LinearMap.BilinMap.tmul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinMap`。
形式化陈述：{R : Type uR} →   {A : Type uA} →     {M₁ : Type uM₁} →       {M₂ : Type u
M₂} →         {N₁ : Type uN₁} →           {N₂ : Type uN₂} →             [inst : 
CommSemiring R] →               [inst_1 : CommSemiring A] →                 [ins
t_2 : AddCommMonoid M₁] →                   [inst_3 : AddCommMonoid M₂] →       
              [inst_4 : AddCommMonoid N₁] →                       [inst_5 : AddC
ommMonoid N₂] →                         [inst_6 : Algebra R A] →                
           [inst_7 : _root_.Module R M₁] →                             [inst_8 :
 _root_.Module A M₁] →                               [inst_9 : _root_.Module R N
₁] →                                 [inst_10 : _root_.Module A N₁] →           
                        [inst_11 : SMulCommClass R A M₁] →                      
               [IsScalarTower R A M₁] →                                       [i
nst_13 : SMulCommClass R A N₁] →                                         [IsScal
arTower R A N₁] →                                           [inst_15 : _root_.Mo
dule R M₂] →                                             [inst_16 : _root_.Modul
e R N₂] →                                               LinearMap.BilinMap A M₁ 
N₁ →                                                 LinearMap.BilinMap R M₂ N₂ 
→                                                   LinearMap.BilinMap A (Tensor
Product R M₁ M₂) (TensorProduct R N₁ N₂)
参数：TensorProduct R M₁ M₂；TensorProduct R N₁ N₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two bilinear forms, a shorthand for dot notation.
-/
protected abbrev tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) :
    BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear maps is symmetric. -/
/-
**LinearMap.BilinMap.tmul_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinMap`。
形式化陈述：tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂} (hB₁ : forall 
x y, B₁ x y = B₁ y x) (hB₂ : forall x y, B₂ x y = B₂ y x) (x y : M₁ otimes[R] M₂
) : B₁.tmul B₂ x y = B₁.tmul B₂ y x
参数：hB₁ : forall x y, B₁ x y = B₁ y x；hB₂ : forall x y, B₂ x y = B₂ y x；x y : M₁ 
otimes[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinMap.isSymm_iff_eq_flip`：∀ {R : Type u_1} {M : Type u_5} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Type u_20} [inst_3 : …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A tensor product of symmetric bilinear maps is symmetric.
-/
lemma tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂}
    (hB₁ : ∀ x y, B₁ x y = B₁ y x) (hB₂ : ∀ x y, B₂ x y = B₂ y x)
    (x y : M₁ ⊗[R] M₂) :
    B₁.tmul B₂ x y = B₁.tmul B₂ y x := by
  revert x y
  rw [isSymm_iff_eq_flip]
  aesop

variable (A) in
/-- The base change of a bilinear map (also known as "extension of scalars"). -/
/-
**LinearMap.BilinMap.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinMap`。
形式化陈述：{R : Type uR} →   (A : Type uA) →     {M₂ : Type uM₂} →       {N₂ : Type u
N₂} →         [inst : CommSemiring R] →           [inst_1 : CommSemiring A] →   
          [inst_2 : AddCommMonoid M₂] →               [inst_3 : AddCommMonoid N₂
] →                 [inst_4 : Algebra R A] →                   [inst_5 : _root_.
Module R M₂] →                     [inst_6 : _root_.Module R N₂] →              
         LinearMap.BilinMap R M₂ N₂ → LinearMap.BilinMap A (TensorProduct R A M₂
) (TensorProduct R A N₂)
参数：A : Type uA；TensorProduct R A M₂；TensorProduct R A N₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change of a bilinear map (also known as "extension of scalars").
-/
protected def baseChange (B : BilinMap R M₂ N₂) : BilinMap A (A ⊗[R] M₂) (A ⊗[R] N₂) :=
  BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
/-
**LinearMap.BilinMap.baseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinM
ap`。
形式化陈述：baseChange_tmul (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂) (a' : A) (m₂' : 
M₂) : B₂.baseChange A (a otimesₜ m₂) (a' otimesₜ m₂') = (a * a') otimesₜ (B₂ m₂ 
m₂')
参数：B₂ : BilinMap R M₂ N₂；a : A；m₂ : M₂；a' : A；m₂' : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem baseChange_tmul (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (a * a') ⊗ₜ (B₂ m₂ m₂') :=
  rfl
/-
**LinearMap.BilinMap.baseChange_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bili
nMap`。
形式化陈述：baseChange_isSymm {B₂ : BilinMap R M₂ N₂} (hB₂ : forall x y, B₂ x y = B₂ y
 x) (x y : A otimes[R] M₂) : B₂.baseChange A x y = B₂.baseChange A y x
参数：hB₂ : forall x y, B₂ x y = B₂ y x；x y : A otimes[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinMap.tmul_isSymm`：tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ 
: BilinMap R M₂ N₂} (hB₁ : forall x y, B₁ x y = B₁ y x) (hB₂ : forall x y, B₂ x 
y = B₂ y x) (x y : M…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma baseChange_isSymm {B₂ : BilinMap R M₂ N₂} (hB₂ : ∀ x y, B₂ x y = B₂ y x) (x y : A ⊗[R] M₂) :
    B₂.baseChange A x y = B₂.baseChange A y x :=
  tmul_isSymm mul_comm hB₂ x y

end BilinMap

namespace BilinForm

variable (R A) in
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products.

Note this is heterobasic; the bilinear form on the left can take values in an (commutative) algebra
over the ring in which the right bilinear form is valued. -/
/-
**LinearMap.BilinForm.tensorDistrib** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：tensorDistrib : BilinForm A M₁ otimes[R] BilinForm R M₂ ->ₗ[A] BilinForm A
 (M₁ otimes[R] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two bilinear forms injects into bilinear forms on tensor p
roducts.

Note this is heterobasic; the bilinear form on the left can take values in an (c
ommutative) algebra
over the ring in which the right bilinear form is valued.
-/
def tensorDistrib : BilinForm A M₁ ⊗[R] BilinForm R M₂ →ₗ[A] BilinForm A (M₁ ⊗[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrRight₂.toLinearMap ∘ₗ (BilinMap.tensorDistrib R A)

variable (R A) in
-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in https://github.com/leanprover-community/mathlib4/pull/6306.
@[simp]
/-
**LinearMap.BilinForm.tensorDistrib_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：tensorDistrib_tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (
m₂ : M₂) (m₁' : M₁) (m₂' : M₂) : tensorDistrib R A (B₁ otimesₜ B₂) (m₁ otimesₜ m
₂) (m₁' otimesₜ m₂') = B₂ m₂ m₂' • B₁ m₁ m₁'
参数：B₁ : BilinForm A M₁；B₂ : BilinForm R M₂；m₁ : M₁；m₂ : M₂；m₁' : M₁；m₂' : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem tensorDistrib_tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
/-
**LinearMap.BilinForm.tmul** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：{R : Type uR} →   {A : Type uA} →     {M₁ : Type uM₁} →       {M₂ : Type u
M₂} →         [inst : CommSemiring R] →           [inst_1 : CommSemiring A] →   
          [inst_2 : AddCommMonoid M₁] →               [inst_3 : AddCommMonoid M₂
] →                 [inst_4 : Algebra R A] →                   [inst_5 : _root_.
Module R M₁] →                     [inst_6 : _root_.Module A M₁] →              
         [inst_7 : SMulCommClass R A M₁] →                         [IsScalarTowe
r R A M₁] →                           [inst_9 : _root_.Module R M₂] →           
                  LinearMap.BilinForm A M₁ →                               Linea
rMap.BilinMap R M₂ R → LinearMap.BilinMap A (TensorProduct R M₁ M₂) A
参数：TensorProduct R M₁ M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two bilinear forms, a shorthand for dot notation.
-/
protected abbrev tmul (B₁ : BilinForm A M₁) (B₂ : BilinMap R M₂ R) : BilinMap A (M₁ ⊗[R] M₂) A :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear forms is symmetric. -/
/-
**LinearMap.BilinForm._root_.LinearMap.IsSymm.tmul** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tensor product of symmetric bilinear forms is symmetric.
-/
lemma _root_.LinearMap.IsSymm.tmul {B₁ : BilinForm A M₁} {B₂ : BilinForm R M₂}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂.eq x₂ y₂) (hB₁.eq x₁ y₁)

variable (A) in
/-- The base change of a bilinear form. -/
/-
**LinearMap.BilinForm.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：{R : Type uR} →   (A : Type uA) →     {M₂ : Type uM₂} →       [inst : Comm
Semiring R] →         [inst_1 : CommSemiring A] →           [inst_2 : AddCommMon
oid M₂] →             [inst_3 : Algebra R A] →               [inst_4 : _root_.Mo
dule R M₂] → LinearMap.BilinForm R M₂ → LinearMap.BilinForm A (TensorProduct R A
 M₂)
参数：A : Type uA；TensorProduct R A M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change of a bilinear form.
-/
protected def baseChange (B : BilinForm R M₂) : BilinForm A (A ⊗[R] M₂) :=
  BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
/-
**LinearMap.BilinForm.baseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：baseChange_tmul (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂) (a' : A) (m₂' : M₂
) : B₂.baseChange A (a otimesₜ m₂) (a' otimesₜ m₂') = (B₂ m₂ m₂') • (a * a')
参数：B₂ : BilinForm R M₂；a : A；m₂ : M₂；a' : A；m₂' : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem baseChange_tmul (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl
/-
**LinearMap.BilinForm.baseChange_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M₂ : Type uM₂} [inst : CommSemiring R] [ins
t_1 : CommSemiring A]   [inst_2 : AddCommMonoid M₂] [inst_3 : Algebra R A] [inst
_4 : _root_.Module R M₂],   LinearMap.BilinForm.baseChange A 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma baseChange_zero : (0 : BilinForm R M₂).baseChange A = 0 := by ext; simp
/-
**LinearMap.BilinForm.baseChange_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.BilinForm`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M₂ : Type uM₂} [inst : CommSemiring R] [ins
t_1 : CommSemiring A]   [inst_2 : AddCommMonoid M₂] [inst_3 : Algebra R A] [inst
_4 : _root_.Module R M₂] [FaithfulSMul R A]   (B : LinearMap.BilinForm R M₂), Li
nearMap.BilinForm.baseChange A B = 0 ↔ B = 0
参数：B : LinearMap.BilinForm R M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LinearMap.congr_fun₂`：congr_fun₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : 
f = g) (x y) : f x y = g x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.BilinForm.baseChange_zero`：∀ {R : Type uR} {A : Type uA} {M₂ :
 Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddComm
Monoid M₂] [inst_3 : Alge…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma baseChange_eq_zero_iff [FaithfulSMul R A]
    (B : BilinForm R M₂) : B.baseChange A = 0 ↔ B = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext m m'
  simpa [← Algebra.algebraMap_eq_smul_one] using LinearMap.congr_fun₂ h (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] m')

variable (A) in
/-- The base change of a symmetric bilinear form is symmetric. -/
/-
**LinearMap.BilinForm.IsSymm.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm.IsSymm`。
形式化陈述：∀ {R : Type uR} (A : Type uA) {M₂ : Type uM₂} [inst : CommSemiring R] [ins
t_1 : CommSemiring A]   [inst_2 : AddCommMonoid M₂] [inst_3 : Algebra R A] [inst
_4 : _root_.Module R M₂] {B₂ : LinearMap.BilinForm R M₂},   LinearMap.IsSymm B₂ 
→ LinearMap.IsSymm (LinearMap.BilinForm.baseChange A B₂)
参数：A : Type uA；LinearMap.BilinForm.baseChange A B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymm.tmul`：∀ {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂
 : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCo
mmMonoid M₁…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The base change of a symmetric bilinear form is symmetric.
-/
lemma IsSymm.baseChange {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm) : (B₂.baseChange A).IsSymm :=
  IsSymm.tmul ⟨mul_comm⟩ hB₂

end BilinForm

end CommSemiring

section CommRing

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Module.Free R M₁] [Module.Finite R M₁]
variable [Module.Free R M₂] [Module.Finite R M₂]

namespace BilinForm

variable (R) in
/-- `tensorDistrib` as an equivalence. -/
/-
**LinearMap.BilinForm.tensorDistribEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：tensorDistribEquiv : BilinForm R M₁ otimes[R] BilinForm R M₂ ≃ₗ[R] BilinFo
rm R (M₁ otimes[R] M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tensorDistrib` as an equivalence.
-/
noncomputable def tensorDistribEquiv :
    BilinForm R M₁ ⊗[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr
    (TensorProduct.lift.equiv (.id R) _ _ _) (TensorProduct.lift.equiv (.id R) _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv (.id R) _ _ _).symm

@[simp]
/-
**LinearMap.BilinForm.tensorDistribEquiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinForm`。
形式化陈述：tensorDistribEquiv_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : 
M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) : tensorDistribEquiv R (M₁
参数：B₁ : BilinForm R M₁；B₂ : BilinForm R M₂；m₁ : M₁；m₂ : M₂；m₁' : M₁；m₂' : M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem tensorDistribEquiv_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) (B₁ ⊗ₜ[R] B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl

variable (R M₁ M₂) in
-- TODO: make this `rfl`
@[simp]
/-
**LinearMap.BilinForm.tensorDistribEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.BilinForm`。
形式化陈述：tensorDistribEquiv_toLinearMap : (tensorDistribEquiv R (M₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem tensorDistribEquiv_toLinearMap :
    (tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂)).toLinearMap = tensorDistrib R R := by
  ext B₁ B₂ : 3
  ext
  exact mul_comm _ _

@[simp]
/-
**LinearMap.BilinForm.tensorDistribEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm`。
形式化陈述：tensorDistribEquiv_apply (B : BilinForm R M₁ otimes BilinForm R M₂) : tens
orDistribEquiv R (M₁
参数：B : BilinForm R M₁ otimes BilinForm R M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.BilinForm.tensorDistribEquiv_toLinearMap`：tensorDistribEquiv_t
oLinearMap : (tensorDistribEquiv R (M₁
-/
theorem tensorDistribEquiv_apply (B : BilinForm R M₁ ⊗ BilinForm R M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) B = tensorDistrib R R B :=
  DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

end BilinForm

end CommRing

end LinearMap

