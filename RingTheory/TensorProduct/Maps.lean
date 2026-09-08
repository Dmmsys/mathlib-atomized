/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Module.Rat
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Maps between tensor products of R-algebras

This file provides results about maps between tensor products of `R`-algebras.

## Main declarations

- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[S] C) ⊗[R] D) ≃ₐ[T] (A ⊗[S] (C ⊗[R] D))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

@[expose] public section

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct

namespace Module.End

open LinearMap

variable (R M N : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The map `LinearMap.lTensorHom` which sends `f ↦ 1 ⊗ f` as a morphism of algebras. -/
@[simps!]
/-
**Module.End.lTensorAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：lTensorAlgHom : Module.End R M ->ₐ[R] Module.End R (N otimes[R] M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `LinearMap.lTensor_mul`：lTensor_mul (f g : Module.End R N) : (f * g).lTen
sor M = f.lTensor M * g.lTensor M

--- 原说明 ---
The map `LinearMap.lTensorHom` which sends `f ↦ 1 ⊗ f` as a morphism of algebras
.
-/
def lTensorAlgHom : Module.End R M →ₐ[R] Module.End R (N ⊗[R] M) :=
  .ofLinearMap (lTensorHom (M := N)) (lTensor_id N M) (lTensor_mul N)

/-- The map `LinearMap.rTensorHom` which sends `f ↦ f ⊗ 1` as a morphism of algebras. -/
@[simps!]
/-
**Module.End.rTensorAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：rTensorAlgHom : Module.End R M ->ₐ[R] Module.End R (M otimes[R] N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
· 使用定理 `LinearMap.rTensor_mul`：rTensor_mul (f g : Module.End R N) : (f * g).rTen
sor M = f.rTensor M * g.rTensor M

--- 原说明 ---
The map `LinearMap.rTensorHom` which sends `f ↦ f ⊗ 1` as a morphism of algebras
.
-/
def rTensorAlgHom : Module.End R M →ₐ[R] Module.End R (M ⊗[R] N) :=
  .ofLinearMap (rTensorHom (M := N)) (rTensor_id N M) (rTensor_mul N)

end Module.End

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {R' : Type*} {S : Type uS} {T : Type*}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
We build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra S C]
variable [Semiring D] [Algebra R D]

set_option backward.defeqAttrib.useBackward true in
/-- To check a linear map preserves multiplication, it suffices to check it on pure tensors. See
`algHomOfLinearMapTensorProduct` for a bundled version. -/
/-
**Algebra.TensorProduct._root_.LinearMap.map_mul_of_map_mul_tmul** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To check a linear map preserves multiplication, it suffices to check it on pure 
tensors. See
`algHomOfLinearMapTensorProduct` for a bundled version.
-/
lemma _root_.LinearMap.map_mul_of_map_mul_tmul {f : A ⊗[R] B →ₗ[S] C}
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (x y : A ⊗[R] B) : f (x * y) = f x * f y :=
  f.map_mul_iff.2 (by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    let : Algebra R C := .restrictScalars R S C
    let : IsScalarTower R S C := .restrictScalars R S C
    ext
    dsimp
    exact hf _ _ _ _) x y

/-- Build an algebra morphism from a linear map out of a tensor product, and evidence that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
/-
**Algebra.TensorProduct.algHomOfLinearMapTensorProduct** 是 Mathlib 中的一个定义，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：algHomOfLinearMapTensorProduct (f : A otimes[R] B ->ₗ[S] C) (h_mul : foral
l (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) *
 f (a₂ otimesₜ b₂)) (h_one : f (1 otimesₜ[R] 1) = 1) : A otimes[R] B ->ₐ[S] C
参数：f : A otimes[R] B ->ₗ[S] C；h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a
₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) * f (a₂ otimesₜ b₂)；h_one : f (1 otime
sₜ[R] 1) = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_mul_of_map_mul_tmul`：∀ {R : Type uR} {S : Type uS} {A : Ty
pe uA} {B : Type uB} {C : Type uC} [inst : CommSemiring R]   [inst_1 : CommSemir
ing S] [inst_2 : Algebr…

--- 原说明 ---
Build an algebra morphism from a linear map out of a tensor product, and evidenc
e that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about
 `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.on
e_def`).
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  AlgHom.ofLinearMap f h_one (f.map_mul_of_map_mul_tmul h_mul)

@[simp]
/-
**Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply** 是 Mathlib 中的一个定理，
位于命名空间 `Algebra.TensorProduct`。
形式化陈述：algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) : (algHomOfLinearMa
pTensorProduct f h_mul h_one : A otimes[R] B ->ₐ[S] C) x = f x
参数：f h_mul h_one x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl

/-- Build an algebra equivalence from a linear equivalence out of a tensor product, and evidence
that on pure tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
/-
**Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct** 是 Mathlib 中的一个定义，位于
命名空间 `Algebra.TensorProduct`。
形式化陈述：algEquivOfLinearEquivTensorProduct (f : A otimes[R] B ≃ₗ[S] C) (h_mul : fo
rall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁
) * f (a₂ otimesₜ b₂)) (h_one : f (1 otimesₜ[R] 1) = 1) : A otimes[R] B ≃ₐ[S] C
参数：f : A otimes[R] B ≃ₗ[S] C；h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂
) otimesₜ (b₁ * b₂)) = f (a₁ otimesₜ b₁) * f (a₂ otimesₜ b₂)；h_one : f (1 otimes
ₜ[R] 1) = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an algebra equivalence from a linear equivalence out of a tensor product, 
and evidence
that on pure tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about
 `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.on
e_def`).
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }

@[simp]
/-
**Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply** 是 Mathlib 中的一
个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) : (algEquivOfLi
nearEquivTensorProduct f h_mul h_one : A otimes[R] B ≃ₐ[S] C) x = f x
参数：f h_mul h_one x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl

variable [Algebra R C]
/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
/-
**Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct** 是 Mathlib 中的一
个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：algEquivOfLinearEquivTripleTensorProduct (f : A otimes[R] B otimes[R] C ≃ₗ
[R] D) (h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C), f ((a₁ * a₂) otimesₜ
 (b₁ * b₂) otimesₜ (c₁ * c₂)) = f (a₁ otimesₜ b₁ otimesₜ c₁) * f (a₂ otimesₜ b₂ 
otimesₜ c₂)) (h_one : f (((1 : A) otimesₜ[R] (1 : B)) otimesₜ[R] (1 : C)) = 1) :
 A otimes[R] B otimes[R] C ≃ₐ[R] D
参数：f : A otimes[R] B otimes[R] C ≃ₗ[R] D；h_mul : forall (a₁ a₂ : A) (b₁ b₂ : B) 
(c₁ c₂ : C), f ((a₁ * a₂) otimesₜ (b₁ * b₂) otimesₜ (c₁ * c₂)) = f (a₁ otimesₜ b
₁ otimesₜ c₁) * f (a₂ otimesₜ b₂ otimesₜ c₂)；h_one : f (((1 : A) otimesₜ[R] (1 :
 B)) otimesₜ[R] (1 : C)) = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an algebra equivalence from a linear equivalence out of a triple tensor pr
oduct,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : A ⊗[R] B ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    A ⊗[R] B ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    simpa using h_mul _ _ _ _ _ _

@[simp]
/-
**Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) : (algEqu
ivOfLinearEquivTripleTensorProduct f h_mul h_one : A otimes[R] B otimes[R] C ≃ₐ[
R] D) x = f x
参数：f h_mul h_one x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : A ⊗[R] B ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl

section lift
variable [IsScalarTower R S C]

/-- The forward direction of the universal property of tensor products of algebras; any algebra
morphism from the tensor product can be factored as the product of two algebra morphisms that
commute.

See `Algebra.TensorProduct.liftEquiv` for the fact that every morphism factors this way. -/
/-
**Algebra.TensorProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：lift (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g
 y)) : (A otimes[R] B) ->ₐ[S] C
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C；hfg : forall x y, Commute (f x) (g y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The forward direction of the universal property of tensor products of algebras; 
any algebra
morphism from the tensor product can be factored as the product of two algebra m
orphisms that
commute.

See `Algebra.TensorProduct.liftEquiv` for the fact that every morphism factors t
his way.
-/
def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun _ _ => LinearMap.ext fun _ => rfl
          map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [map_mul, map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [map_one, map_one, one_mul])

@[simp]
/-
**Algebra.TensorProduct.lift_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：lift_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f 
x) (g y)) (a : A) (b : B) : lift f g hfg (a otimesₜ b) = f a * g b
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C；hfg : forall x y, Commute (f x) (g y)；a : A；b :
 B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.TensorProduct.lift_includeLeft_includeRight** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.TensorProduct`。
形式化陈述：lift_includeLeft_includeRight : lift includeLeft includeRight (fun _ _ => 
(Commute.one_right _).tmul (Commute.one_left _)) = .id S (A otimes[R] B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Commute.tmul`：∀ {R : Type uR} {A : Type uA} {B : Type uB} [inst : CommSe
miring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] 
[i…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun _ _ => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp

@[simp]
/-
**Algebra.TensorProduct.lift_comp_includeLeft** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：lift_comp_includeLeft (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y,
 Commute (f x) (g y)) : (lift f g hfg).comp includeLeft = f
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C；hfg : forall x y, Commute (f x) (g y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp

@[simp]
/-
**Algebra.TensorProduct.lift_comp_includeRight** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：lift_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y
, Commute (f x) (g y)) : ((lift f g hfg).restrictScalars R).comp includeRight = 
g
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C；hfg : forall x y, Commute (f x) (g y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- Variant with the same base that doesn't need `restrictScalars`. -/
@[simp]
/-
**Algebra.TensorProduct.lift_comp_includeRight'** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.TensorProduct`。
形式化陈述：lift_comp_includeRight' (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (hfg : forall x 
y, Commute (f x) (g y)) : (lift f g hfg).comp includeRight = g
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；hfg : forall x y, Commute (f x) (g y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Variant with the same base that doesn't need `restrictScalars`.
-/
theorem lift_comp_includeRight' (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
/-
**Algebra.TensorProduct.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：liftEquiv : {fg : (A ->ₐ[S] C) × (B ->ₐ[R] C) // forall x y, Commute (fg.1
 x) (fg.2 y)} ≃ ((A otimes[R] B) ->ₐ[S] C) where toFun fg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from
 the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requir
ement for graded
algebra.
-/
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun _ _ =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

variable (R S B) in
/--
Algebra maps `S ⊗[R] B →ₐ[S] C` are the same as algebra maps `B →ₐ[R] C`.
Variant of `Algebra.TensorProduct.liftEquiv` where the left map is fixed.
-/
@[simps]
/-
**Algebra.TensorProduct.liftEquivRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：liftEquivRight (C : Type*) [CommRing C] [Algebra R C] [Algebra S C] [IsSca
larTower R S C] : (B ->ₐ[R] C) ≃ (S otimes[R] B ->ₐ[S] C) where toFun f
参数：C : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra maps `S ⊗[R] B →ₐ[S] C` are the same as algebra maps `B →ₐ[R] C`.
Variant of `Algebra.TensorProduct.liftEquiv` where the left map is fixed.
-/
def liftEquivRight (C : Type*) [CommRing C] [Algebra R C] [Algebra S C] [IsScalarTower R S C] :
    (B →ₐ[R] C) ≃ (S ⊗[R] B →ₐ[S] C) where
  toFun f := Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ ↦ .all _ _
  invFun f := AlgHom.comp (f.restrictScalars R) Algebra.TensorProduct.includeRight
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
/-
**Algebra.TensorProduct.restrictScalars_lift** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：restrictScalars_lift [CommSemiring R'] [Algebra R R'] [Algebra R' S] [Alge
bra R' A] [IsScalarTower R R' A] [IsScalarTower R' S A] [Algebra R' C] [IsScalar
Tower R R' C] [IsScalarTower R' S C] (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : fo
rall (x : A) (y : B), Commute (f x) (g y)) : (Algebra.TensorProduct.lift f g hfg
).restrictScalars R' = Algebra.TensorProduct.lift (f.restrictScalars R') g hfg
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C；hfg : forall (x : A) (y : B), Commute (f x) (g 
y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem restrictScalars_lift [CommSemiring R'] [Algebra R R'] [Algebra R' S]
    [Algebra R' A] [IsScalarTower R R' A] [IsScalarTower R' S A]
    [Algebra R' C] [IsScalarTower R R' C] [IsScalarTower R' S C]
    (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ (x : A) (y : B), Commute (f x) (g y)) :
    (Algebra.TensorProduct.lift f g hfg).restrictScalars R' =
      Algebra.TensorProduct.lift (f.restrictScalars R') g hfg :=
  rfl

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])

/-
**Algebra.TensorProduct.lid_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：∀ (R : Type uR) (A : Type uA) [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A],   ↑(Algebra.TensorProduct.lid R A) = TensorProduct.lid
 R A
参数：R : Type uR；A : Type uA；Algebra.TensorProduct.lid R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl

variable {R} {A} in
@[simp]
/-
**Algebra.TensorProduct.lid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r otimesₜ a) = r • a
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl

variable {A} in
@[simp]
/-
**Algebra.TensorProduct.lid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 otimesₜ a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul_comm r₁ a₁ r₂ a₂ |>.symm)
    (one_smul R _)

/-
**Algebra.TensorProduct.rid_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：∀ (R : Type uR) (S : Type uS) (A : Type uA) [inst : CommSemiring R] [inst_
1 : CommSemiring S] [inst_2 : Algebra R S]   [inst_3 : Semiring A] [inst_4 : Alg
ebra R A] [inst_5 : Algebra S A] [inst_6 : IsScalarTower R S A],   ↑(Algebra.Ten
sorProduct.rid R S A) = TensorProduct.AlgebraTensorModule.rid R S A
参数：R : Type uR；S : Type uS；A : Type uA；Algebra.TensorProduct.rid R S A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl

variable {R A} in
@[simp]
/-
**Algebra.TensorProduct.rid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a otimesₜ r) = r • a
参数：r : R；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl

variable {A} in
@[simp]
/-
**Algebra.TensorProduct.rid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a otimesₜ 1
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl

variable (T) in
/-
**Algebra.TensorProduct.linearMap_comp_rid** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：linearMap_comp_rid : (Algebra.linearMap S (S otimes[R] B)).restrictScalars
 R ∘ₗ (TensorProduct.rid R R S).toLinearMap = (Algebra.linearMap R B).lTensor S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearMap_comp_rid : (Algebra.linearMap S (S ⊗[R] B)).restrictScalars R ∘ₗ
    (TensorProduct.rid R R S).toLinearMap = (Algebra.linearMap R B).lTensor S := by
  ext; simp
/-
**Algebra.TensorProduct.rid_comp_includeLeftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：∀ (R : Type uR) (S : Type uS) (A : Type uA) [inst : CommSemiring R] [inst_
1 : CommSemiring S] [inst_2 : Algebra R S]   [inst_3 : Semiring A] [inst_4 : Alg
ebra R A] [inst_5 : Algebra S A] [inst_6 : IsScalarTower R S A],   (↑(Algebra.Te
nsorProduct.rid R S A)).comp Algebra.TensorProduct.includeLeftRingHom = RingHom.
id A
参数：R : Type uR；S : Type uS；A : Type uA；↑(Algebra.TensorProduct.rid R S A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma rid_comp_includeLeftRingHom :
    (Algebra.TensorProduct.rid R S A : A ⊗[R] R →+* A).comp includeLeftRingHom = .id A := by
  ext; simp

section

variable (R A B C : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [Semiring C] [Algebra R C]

/-
**Algebra.TensorProduct.tmul_one_tmul_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：tmul_one_tmul_one_tmul (x : A) (y : C) : x otimesₜ[R] (1 : B) otimesₜ[A] (
(1 : A) otimesₜ[R] y) = 1 otimesₜ[A] (x otimesₜ[R] y)
参数：x : A；y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
-/
lemma tmul_one_tmul_one_tmul (x : A) (y : C) :
    x ⊗ₜ[R] (1 : B) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] y) = 1 ⊗ₜ[A] (x ⊗ₜ[R] y) := by
  trans x • 1 ⊗ₜ[A] (1 ⊗ₜ[R] y)
  · simp [Algebra.smul_def]
  · simp [← tmul_smul, smul_tmul' (M := A)]

end

section CompatibleSMul

variable (R S T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring A]
  [Semiring B]
variable [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
variable [Algebra T A] [SMulCommClass R T A] [SMulCommClass S T A]
variable [SMulCommClass R S A] [CompatibleSMul R S A B]

/-- If A and B are both R- and S-algebras and their actions on them commute,
and if the S-action on `A ⊗[R] B` can switch between the two factors, then there is a
canonical T-algebra homomorphism from `A ⊗[S] B` to `A ⊗[R] B`,
where `T` is any other ring acting on `A` and whose action commutes with the `R` and `S`-actions. -/
/-
**Algebra.TensorProduct.mapOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：mapOfCompatibleSMul : A otimes[S] B ->ₐ[T] A otimes[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If A and B are both R- and S-algebras and their actions on them commute,
and if the S-action on `A ⊗[R] B` can switch between the two factors, then there
 is a
canonical T-algebra homomorphism from `A ⊗[S] B` to `A ⊗[R] B`,
where `T` is any other ring acting on `A` and whose action commutes with the `R`
 and `S`-actions.
-/
def mapOfCompatibleSMul : A ⊗[S] B →ₐ[T] A ⊗[R] B :=
  .ofLinearMap (_root_.TensorProduct.mapOfCompatibleSMul R S T A B) rfl fun x ↦
    x.induction_on (by simp) (fun _ _ y ↦ y.induction_on (by simp) (by simp)
      fun _ _ h h' ↦ by simp only [mul_add, map_add, h, h'])
      fun _ _ h h' _ ↦ by simp only [add_mul, map_add, h, h']
/-
**Algebra.TensorProduct.mapOfCompatibleSMul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.TensorProduct`。
形式化陈述：∀ (R : Type u_3) (S : Type u_4) (T : Type u_5) (A : Type u_6) (B : Type u_
7) [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : CommSemiring T]
 [inst_3 : Semiring A] [inst_4 : Semiring B] [inst_5 : Algebra R A]   [inst_6 : 
Algebra R B] [inst_7 : Algebra S A] [inst_8 : Algebra S B] [inst_9 : Algebra T A
]   [inst_10 : SMulCommClass R T A] [inst_11 : SMulCommClass S T A] [inst_12 : S
MulCommClass R S A]   [inst_13 : TensorProduct.CompatibleSMul R S A B] (m : A) (
n : B),   (Algebra.TensorProduct.mapOfCompatibleSMul R S T A B) (m ⊗ₜ[S] n) = m 
⊗ₜ[R] n
参数：R : Type u_3；S : Type u_4；T : Type u_5；A : Type u_6；B : Type u_7；m : A；n : B；
Algebra.TensorProduct.mapOfCompatibleSMul R S T A B；m ⊗ₜ[S] n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R S T A B (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl
/-
**Algebra.TensorProduct.mapOfCompatibleSMul_surjective** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul 
R S T A B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.mapOfCompatibleSMul_surjective`：mapOfCompatibleSMul_surjec
tive : Function.Surjective (mapOfCompatibleSMul R A S M N)
-/
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R S T A B) :=
  _root_.TensorProduct.mapOfCompatibleSMul_surjective R S T A B

attribute [local instance] SMulCommClass.symm

@[deprecated (since := "2026-02-21")]
alias mapOfCompatibleSMul' := mapOfCompatibleSMul

/-- If the R- and S-actions on A and B satisfy `CompatibleSMul` both ways,
then `A ⊗[S] B` is canonically isomorphic to `A ⊗[R] B`. -/
/-
**Algebra.TensorProduct.equivOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：equivOfCompatibleSMul [CompatibleSMul S R A B] : A otimes[S] B ≃ₐ[T] A oti
mes[R] B where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the R- and S-actions on A and B satisfy `CompatibleSMul` both ways,
then `A ⊗[S] B` is canonically isomorphic to `A ⊗[R] B`.
-/
def equivOfCompatibleSMul [CompatibleSMul S R A B] : A ⊗[S] B ≃ₐ[T] A ⊗[R] B where
  __ := mapOfCompatibleSMul R S T A B
  invFun := mapOfCompatibleSMul S R T A B
  __ := _root_.TensorProduct.equivOfCompatibleSMul R S T A B

variable [Algebra R S] [CompatibleSMul R S S A] [CompatibleSMul S R S A]
omit [SMulCommClass R S A]

/-- If the R- and S- action on S and A satisfy `CompatibleSMul` both ways,
then `S ⊗[R] A` is canonically isomorphic to `A`. -/
/-
**Algebra.TensorProduct.lidOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：lidOfCompatibleSMul : S otimes[R] A ≃ₐ[S] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the R- and S- action on S and A satisfy `CompatibleSMul` both ways,
then `S ⊗[R] A` is canonically isomorphic to `A`.
-/
def lidOfCompatibleSMul : S ⊗[R] A ≃ₐ[S] A :=
  (equivOfCompatibleSMul R S S S A).symm.trans (TensorProduct.lid _ _)
/-
**Algebra.TensorProduct.lidOfCompatibleSMul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.TensorProduct`。
形式化陈述：lidOfCompatibleSMul_tmul (s a) : lidOfCompatibleSMul R S A (s otimesₜ[R] a
) = s • a
参数：s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem lidOfCompatibleSMul_tmul (s a) : lidOfCompatibleSMul R S A (s ⊗ₜ[R] a) = s • a := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M N : Type*} [CommSemiring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module ℚ M] [Module ℚ N] : CompatibleSMul R ℚ M N where
  smul_tmul q m n := by
    have : IsAddTorsionFree (M ⊗[R] N) := .of_module_rat _
    suffices q.den • ((q • m) ⊗ₜ[R] n) = q.den • (m ⊗ₜ[R] (q • n)) from
      smul_right_injective (M ⊗[R] N) q.den_nz <| by norm_cast
    rw [smul_tmul', ← tmul_smul, ← smul_assoc, ← smul_assoc, nsmul_eq_mul, Rat.den_mul_eq_num]
    norm_cast
    rw [smul_tmul]

end CompatibleSMul

section

variable (B)

unseal mul in
/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
/-
**Algebra.TensorProduct.comm** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：(R : Type uR) →   (A : Type uA) →     (B : Type uB) →       [inst : CommSe
miring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] →  
           [inst_3 : Semiring B] → [inst_4 : Algebra R B] → TensorProduct R A B 
≃ₐ[R] TensorProduct R B A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl
/-
**Algebra.TensorProduct.comm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：∀ (R : Type uR) (A : Type uA) (B : Type uB) [inst : CommSemiring R] [inst_
1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] [inst_4 : Algebra
 R B], ↑(Algebra.TensorProduct.comm R A B) = TensorProduct.comm R A B
参数：R : Type uR；A : Type uA；B : Type uB；Algebra.TensorProduct.comm R A B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl

variable {A B} in
@[simp]
/-
**Algebra.TensorProduct.comm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：comm_tmul (a : A) (b : B) : TensorProduct.comm R A B (a otimesₜ b) = b oti
mesₜ a
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl

variable {A B} in
@[simp]
/-
**Algebra.TensorProduct.comm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：comm_symm_tmul (a : A) (b : B) : (TensorProduct.comm R A B).symm (b otimes
ₜ a) = a otimesₜ b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b :=
  rfl
/-
**Algebra.TensorProduct.comm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：comm_symm : (TensorProduct.comm R A B).symm = TensorProduct.comm R B A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
-/
theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl

@[simp]
/-
**Algebra.TensorProduct.comm_comp_includeLeft** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：comm_comp_includeLeft : (TensorProduct.comm R A B : A otimes[R] B ->ₐ[R] B
 otimes[R] A).comp includeLeft = includeRight
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm_comp_includeLeft :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeLeft = includeRight := rfl

@[simp]
/-
**Algebra.TensorProduct.comm_comp_includeRight** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：comm_comp_includeRight : (TensorProduct.comm R A B : A otimes[R] B ->ₐ[R] 
B otimes[R] A).comp includeRight = includeLeft
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm_comp_includeRight :
    (TensorProduct.comm R A B : A ⊗[R] B →ₐ[R] B ⊗[R] A).comp includeRight = includeLeft := rfl
/-
**Algebra.TensorProduct.adjoin_tmul_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：adjoin_tmul_eq_top : adjoin R { t : A otimes[R] B | exists a b, a otimesₜ[
R] b = t } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Algebra.span_le_adjoin`：span_le_adjoin (s : Set A) : span R s <= Subalge
bra.toSubmodule (adjoin R s)
-/
theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)

section

omit [Algebra S A] [IsScalarTower R S A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `S`-linear version of `Algebra.TensorProduct.comm` when `A ⊗[R] S`
is viewed as an `S`-algebra via the right component. -/
/-
**Algebra.TensorProduct.commRight** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：commRight : S otimes[R] A ≃ₐ[S] A otimes[R] S where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S`-linear version of `Algebra.TensorProduct.comm` when `A ⊗[R] S`
is viewed as an `S`-algebra via the right component.
-/
def commRight : S ⊗[R] A ≃ₐ[S] A ⊗[R] S where
  __ := Algebra.TensorProduct.comm R S A
  commutes' _ := rfl

variable {S A} in
@[simp]
/-
**Algebra.TensorProduct.commRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：commRight_tmul (s : S) (a : A) : commRight R S A (s otimesₜ a) = a otimesₜ
 s
参数：s : S；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma commRight_tmul (s : S) (a : A) : commRight R S A (s ⊗ₜ a) = a ⊗ₜ s := rfl

variable {S A} in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
/-
**Algebra.TensorProduct.commRight_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：commRight_symm_tmul (s : S) (a : A) : (commRight R S A).symm (a otimesₜ[R]
 s) = s otimesₜ a
参数：s : S；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma commRight_symm_tmul (s : S) (a : A) :
    (commRight R S A).symm (a ⊗ₜ[R] s) = s ⊗ₜ a := rfl

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias Algebra.TensorProduct.commRight_symm_tmul := commRight_symm_tmul

end

end

section

variable [CommSemiring T] [Algebra R T] [Algebra S T]
    [Algebra T A] [IsScalarTower R T A] [IsScalarTower S T A]

variable (T C D) in
/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
/-
**Algebra.TensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：(R : Type uR) →   (S : Type uS) →     (T : Type u_2) →       (A : Type uA)
 →         (C : Type uC) →           (D : Type uD) →             [inst : CommSem
iring R] →               [inst_1 : CommSemiring S] →                 [inst_2 : A
lgebra R S] →                   [inst_3 : Semiring A] →                     [ins
t_4 : Algebra R A] →                       [inst_5 : Algebra S A] →             
            [inst_6 : IsScalarTower R S A] →                           [inst_7 :
 Semiring C] →                             [inst_8 : Algebra R C] →             
                  [inst_9 : Algebra S C] →                                 [inst
_10 : IsScalarTower R S C] →                                   [inst_11 : Semiri
ng D] →                                     [inst_12 : Algebra R D] →           
                            [inst_13 : CommSemiring T] →                        
                 [inst_14 : Algebra R T] →                                      
     [inst_15 : Algebra S T] →                                             [inst
_16 : Algebra T A] →                                               [inst_17 : Is
ScalarTower R T A] →                                                 [inst_18 : 
IsScalarTower S T A] →                                                   TensorP
roduct R (TensorProduct S A C) D ≃ₐ[T]                                          
           TensorProduct S A (TensorProduct R C D)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for tensor product of R-algebras, as an algebra isomorphism.
-/
protected def assoc : (A ⊗[S] C) ⊗[R] D ≃ₐ[T] A ⊗[S] (C ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv
    (AlgebraTensorModule.assoc R S T A C D)
    (by simp [Algebra.TensorProduct.one_def])
    ((LinearMap.map_mul_iff _).mpr <| by ext; simp)

variable (T C D) in
/-
**Algebra.TensorProduct.assoc_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：∀ (R : Type uR) (S : Type uS) (T : Type u_2) (A : Type uA) (C : Type uC) (
D : Type uD) [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : Algeb
ra R S] [inst_3 : Semiring A] [inst_4 : Algebra R A] [inst_5 : Algebra S A]   [i
nst_6 : IsScalarTower R S A] [inst_7 : Semiring C] [inst_8 : Algebra R C] [inst_
9 : Algebra S C]   [inst_10 : IsScalarTower R S C] [inst_11 : Semiring D] [inst_
12 : Algebra R D] [inst_13 : CommSemiring T]   [inst_14 : Algebra R T] [inst_15 
: Algebra S T] [inst_16 : Algebra T A] [inst_17 : IsScalarTower R T A]   [inst_1
8 : IsScalarTower S T A],   ↑(Algebra.TensorProduct.assoc R S T A C D) = TensorP
roduct.AlgebraTensorModule.assoc R S T A C D
参数：R : Type uR；S : Type uS；T : Type u_2；A : Type uA；C : Type uC；D : Type uD；Alge
bra.TensorProduct.assoc R S T A C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem assoc_toLinearEquiv :
    (TensorProduct.assoc R S T A C D).toLinearEquiv = AlgebraTensorModule.assoc R S T A C D := rfl

@[simp]
/-
**Algebra.TensorProduct.assoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：assoc_tmul (a : A) (b : C) (c : D) : TensorProduct.assoc R S T A C D ((a o
timesₜ b) otimesₜ c) = a otimesₜ (b otimesₜ c)
参数：a : A；b : C；c : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem assoc_tmul (a : A) (b : C) (c : D) :
    TensorProduct.assoc R S T A C D ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) := rfl

@[simp]
/-
**Algebra.TensorProduct.assoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：assoc_symm_tmul (a : A) (b : C) (c : D) : (TensorProduct.assoc R S T A C D
).symm (a otimesₜ (b otimesₜ c)) = (a otimesₜ b) otimesₜ c
参数：a : A；b : C；c : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_symm_tmul (a : A) (b : C) (c : D) :
    (TensorProduct.assoc R S T A C D).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c := rfl

end

section

variable (T A B : Type*) [CommSemiring T] [CommSemiring A] [CommSemiring B]
  [Algebra R T] [Algebra R A] [Algebra R B] [Algebra T A] [IsScalarTower R T A] [Algebra S A]
  [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]

/-- The natural isomorphism `A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`. -/
/-
**Algebra.TensorProduct.cancelBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：cancelBaseChange : A otimes[S] (S otimes[R] B) ≃ₐ[T] A otimes[R] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B`.
-/
def cancelBaseChange : A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)

@[simp]
/-
**Algebra.TensorProduct.cancelBaseChange_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：cancelBaseChange_tmul (a : A) (s : S) (b : B) : Algebra.TensorProduct.canc
elBaseChange R S T A B (a otimesₜ (s otimesₜ b)) = (s • a) otimesₜ b
参数：a : A；s : S；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul`：cancelBaseChang
e_tmul (m : M) (n : N) (a : A) : cancelBaseChange R A B M N (m otimesₜ (a otimes
ₜ n)) = (a • m) otimesₜ n
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma cancelBaseChange_tmul (a : A) (s : S) (b : B) :
    Algebra.TensorProduct.cancelBaseChange R S T A B (a ⊗ₜ (s ⊗ₜ b)) = (s • a) ⊗ₜ b :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]
/-
**Algebra.TensorProduct.cancelBaseChange_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.TensorProduct`。
形式化陈述：cancelBaseChange_symm_tmul (a : A) (b : B) : (Algebra.TensorProduct.cancel
BaseChange R S T A B).symm (a otimesₜ b) = a otimesₜ (1 otimesₜ b)
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul`：cancelBase
Change_symm_tmul (m : M) (n : N) : (cancelBaseChange R A B M N).symm (m otimesₜ 
n) = m otimesₜ (1 otimesₜ n)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma cancelBaseChange_symm_tmul (a : A) (b : B) :
    (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (a ⊗ₜ b) = a ⊗ₜ (1 ⊗ₜ b) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b

end

variable {R S A}

section mapRingHom
variable {R S T R' S' T' : Type*}
  [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S] [Algebra R T]
  [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra R' T']
  (fR : R →+* R') (fS : S →+* S') (fT : T →+* T')
  (HS : fS.comp (algebraMap _ _) = (algebraMap _ _).comp fR)
  (HT : fT.comp (algebraMap _ _) = (algebraMap _ _).comp fR)

/-- Heterobasic version of `Algebra.TensorProduct.map` as a ring homomorphism.

Note that this would generalise `map` if we were to have `SemiAlgHom`. -/
/-
**Algebra.TensorProduct.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：mapRingHom : S otimes[R] T ->+* S' otimes[R'] T'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Heterobasic version of `Algebra.TensorProduct.map` as a ring homomorphism.

Note that this would generalise `map` if we were to have `SemiAlgHom`.
-/
def mapRingHom : S ⊗[R] T →+* S' ⊗[R'] T' :=
  letI := fR.toAlgebra
  letI := ((algebraMap R' S').comp fR).toAlgebra
  letI := ((algebraMap R' T').comp fR).toAlgebra
  letI := fS.toAlgebra
  letI := fT.toAlgebra
  letI : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R R' T' := .of_algebraMap_eq' rfl
  letI : IsScalarTower R S S' := .of_algebraMap_eq' HS.symm
  letI : IsScalarTower R T T' := .of_algebraMap_eq' HT.symm
  (lift (R := R) (S := R) (includeLeft.comp (IsScalarTower.toAlgHom R S S'))
    ((includeRight.restrictScalars R).comp (IsScalarTower.toAlgHom R T T'))
    (fun _ _ ↦ .all _ _)).toRingHom

@[simp]
/-
**Algebra.TensorProduct.mapRingHom_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：mapRingHom_tmul (s : S) (t : T) : mapRingHom fR fS fT HS HT (s otimesₜ t) 
= fS s otimesₜ fT t
参数：s : S；t : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_tmul (s : S) (t : T) : mapRingHom fR fS fT HS HT (s ⊗ₜ t) = fS s ⊗ₜ fT t := by
  trans (fS s * 1 : S') ⊗ₜ[R'] (1 * fT t : T')
  · dsimp [mapRingHom, lift_tmul, algebraMap]
  · simp

@[simp]
/-
**Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom** 是 Mathlib 中的一个引理，位于
命名空间 `Algebra.TensorProduct`。
形式化陈述：mapRingHom_comp_includeLeftRingHom : (mapRingHom fR fS fT HS HT).comp (inc
ludeLeftRingHom) = includeLeftRingHom.comp fS
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用引理 `Algebra.TensorProduct.mapRingHom_tmul`：mapRingHom_tmul (s : S) (t : T) :
 mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_comp_includeLeftRingHom :
    (mapRingHom fR fS fT HS HT).comp (includeLeftRingHom) = includeLeftRingHom.comp fS := by
  ext; simp

@[simp]
/-
**Algebra.TensorProduct.mapRingHom_comp_includeRight** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.TensorProduct`。
形式化陈述：mapRingHom_comp_includeRight : (mapRingHom fR fS fT HS HT).comp (RingHomCl
ass.toRingHom includeRight) = (RingHomClass.toRingHom includeRight).comp fT
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.TensorProduct.mapRingHom_tmul`：mapRingHom_tmul (s : S) (t : T) :
 mapRingHom fR fS fT HS HT (s otimesₜ t) = fS s otimesₜ fT t
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapRingHom_comp_includeRight :
    (mapRingHom fR fS fT HS HT).comp (RingHomClass.toRingHom includeRight) =
      (RingHomClass.toRingHom includeRight).comp fT := by ext; simp

end mapRingHom

/-- The tensor product of a pair of algebra morphisms. -/
/-
**Algebra.TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : A otimes[R] B ->ₐ[S] C otimes[R] D
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of a pair of algebra morphisms.
-/
def map (f : A →ₐ[S] C) (g : B →ₐ[R] D) : A ⊗[R] B →ₐ[S] C ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])
/-
**Algebra.TensorProduct.toLinearMap_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} {C : Type uC} {D
 : Type uD} [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : Algebr
a R S] [inst_3 : Semiring A] [inst_4 : Algebra R A] [inst_5 : Algebra S A]   [in
st_6 : IsScalarTower R S A] [inst_7 : Semiring B] [inst_8 : Algebra R B] [inst_9
 : Semiring C]   [inst_10 : Algebra R C] [inst_11 : Algebra S C] [inst_12 : IsSc
alarTower R S C] [inst_13 : Semiring D]   [inst_14 : Algebra R D] (f : A →ₐ[S] C
) (g : B →ₐ[R] D),   (Algebra.TensorProduct.map f g).toLinearMap = TensorProduct
.AlgebraTensorModule.map f.toLinearMap g.toLinearMap
参数：f : A →ₐ[S] C；g : B →ₐ[R] D；Algebra.TensorProduct.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] lemma toLinearMap_map (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).toLinearMap = TensorProduct.AlgebraTensorModule.map f.toLinearMap g.toLinearMap := rfl

@[simp]
/-
**Algebra.TensorProduct.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) (a : A) (b : B) : map f g (a ot
imesₜ b) = f a otimesₜ g b
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] D；a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] D) (a : A) (b : B) : map f g (a ⊗ₜ b) = f a ⊗ₜ g b :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduct`
。
形式化陈述：map_id : map (.id S A) (.id R B) = .id S _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem map_id : map (.id S A) (.id R B) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
/-
**Algebra.TensorProduct.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：map_comp (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S] C) (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ
[R] D) : map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁)
参数：f₂ : C ->ₐ[S] E；f₁ : A ->ₐ[S] C；g₂ : D ->ₐ[R] F；g₁ : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem map_comp
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
/-
**Algebra.TensorProduct.map_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：map_id_comp (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D) : map (AlgHom.id S A) (g₂.
comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁)
参数：g₂ : D ->ₐ[R] F；g₁ : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
lemma map_id_comp (g₂ : D →ₐ[R] F) (g₁ : B →ₐ[R] D) :
    map (AlgHom.id S A) (g₂.comp g₁) = (map (AlgHom.id S A) g₂).comp (map (AlgHom.id S A) g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)
/-
**Algebra.TensorProduct.map_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：map_comp_id (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S] C) : map (f₂.comp f₁) (AlgHom
.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E))
参数：f₂ : C ->ₐ[S] E；f₁ : A ->ₐ[S] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
lemma map_comp_id
    (f₂ : C →ₐ[S] E) (f₁ : A →ₐ[S] C) :
    map (f₂.comp f₁) (AlgHom.id R E) = (map f₂ (AlgHom.id R E)).comp (map f₁ (AlgHom.id R E)) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]
/-
**Algebra.TensorProduct.map_comp_includeLeft** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：map_comp_includeLeft (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp in
cludeLeft = includeLeft.comp f
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by simp
/-
**Algebra.TensorProduct.map_comp_includeLeftRingHom** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} {C : Type uC} {D
 : Type uD} [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : Algebr
a R S] [inst_3 : Semiring A] [inst_4 : Algebra R A] [inst_5 : Algebra S A]   [in
st_6 : IsScalarTower R S A] [inst_7 : Semiring B] [inst_8 : Algebra R B] [inst_9
 : Semiring C]   [inst_10 : Algebra R C] [inst_11 : Algebra S C] [inst_12 : IsSc
alarTower R S C] [inst_13 : Semiring D]   [inst_14 : Algebra R D] (f : A →ₐ[S] C
) (g : B →ₐ[R] D),   (↑(Algebra.TensorProduct.map f g)).comp Algebra.TensorProdu
ct.includeLeftRingHom =     Algebra.TensorProduct.includeLeftRingHom.comp ↑f
参数：f : A →ₐ[S] C；g : B →ₐ[R] D；↑(Algebra.TensorProduct.map f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_comp_includeLeftRingHom (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    (map f g : A ⊗[R] B →+* C ⊗[R] D).comp includeLeftRingHom =
      includeLeftRingHom.comp (f : A →+* C) := by ext; simp

@[simp]
/-
**Algebra.TensorProduct.map_restrictScalars_comp_includeRight** 是 Mathlib 中的一个定理
，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：map_restrictScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : 
((map f g).restrictScalars R).comp includeRight = includeRight.comp g
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_restrictScalars_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by simp

@[simp]
/-
**Algebra.TensorProduct.map_comp_includeRight** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：map_comp_includeRight (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) : (map f g).comp i
ncludeRight = includeRight.comp g
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.map_restrictScalars_comp_includeRight`：map_restric
tScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : ((map f g).restri
ctScalars R).comp includeRight = includeRight.com…
-/
theorem map_comp_includeRight (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g
/-
**Algebra.TensorProduct.map_range** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：map_range (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) : (map f g).range = (includeLe
ft.comp f).range ⊔ (includeRight.comp g).range
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Algebra.TensorProduct.adjoin_tmul_eq_top`：adjoin_tmul_eq_top : adjoin R 
{ t : A otimes[R] B | exists a b, a otimesₜ[R] b = t } = ⊤
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Algebra.TensorProduct.map_tmul`：map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] 
D) (a : A) (b : B) : map f g (a otimesₜ b) = f a otimesₜ g b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `Algebra.mul_mem_sup`：mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : 
x in S) (hy : y in T) : x * y in S ⊔ T
· 使用定理 `AlgHom.mem_range_self`：mem_range_self (φ : A ->ₐ[R] B) (x : A) : φ x in 
φ.range
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
· 使用定理 `Algebra.TensorProduct.map_comp_includeRight`：map_comp_includeRight (f : 
A ->ₐ[R] C) (g : B ->ₐ[R] D) : (map f g).comp includeRight = includeRight.comp g
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `AlgHom.range_comp_le_range`：range_comp_le_range (f : A ->ₐ[R] B) (g : B 
->ₐ[R] C) : (g.comp f).range <= g.range
-/
theorem map_range (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← mul_one (f a), ← one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)
/-
**Algebra.TensorProduct.comm_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：comm_comp_map (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) : (TensorProduct.comm R C 
D : C otimes[R] D ->ₐ[R] D otimes[R] C).comp (Algebra.TensorProduct.map f g) = (
Algebra.TensorProduct.map g f).comp (TensorProduct.comm R A B).toAlgHom
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
lemma comm_comp_map (f : A →ₐ[R] C) (g : B →ₐ[R] D) :
    (TensorProduct.comm R C D : C ⊗[R] D →ₐ[R] D ⊗[R] C).comp (Algebra.TensorProduct.map f g) =
    (Algebra.TensorProduct.map g f).comp (TensorProduct.comm R A B).toAlgHom := by
  ext <;> rfl
/-
**Algebra.TensorProduct.comm_comp_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：comm_comp_map_apply (f : A ->ₐ[R] C) (g : B ->ₐ[R] D) (x) : TensorProduct.
comm R C D (Algebra.TensorProduct.map f g x) = (Algebra.TensorProduct.map g f) (
TensorProduct.comm R A B x)
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] D；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.TensorProduct.comm_comp_map`：comm_comp_map (f : A ->ₐ[R] C) (g :
 B ->ₐ[R] D) : (TensorProduct.comm R C D : C otimes[R] D ->ₐ[R] D otimes[R] C).c
omp (Algebra.TensorProduc…
-/
lemma comm_comp_map_apply (f : A →ₐ[R] C) (g : B →ₐ[R] D) (x) :
    TensorProduct.comm R C D (Algebra.TensorProduct.map f g x) =
    (Algebra.TensorProduct.map g f) (TensorProduct.comm R A B x) :=
  congr($(comm_comp_map f g) x)

variable (A) in
/-- `lTensor A g : A ⊗ B →ₐ A ⊗ D` is the natural algebra morphism induced by `g : B →ₐ D`. -/
/-
**Algebra.TensorProduct.lTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：lTensor (g : B ->ₐ[R] D) : (A otimes[R] B) ->ₐ[S] (A otimes[R] D)
参数：g : B ->ₐ[R] D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lTensor A g : A ⊗ B →ₐ A ⊗ D` is the natural algebra morphism induced by `g : B
 →ₐ D`.
-/
abbrev lTensor (g : B →ₐ[R] D) : (A ⊗[R] B) →ₐ[S] (A ⊗[R] D) := map (.id S A) g

variable (B) in
/-- `rTensor B f : A ⊗ B →ₐ C ⊗ B` is the natural algebra morphism induced by `f : A →ₐ C`. -/
/-
**Algebra.TensorProduct.rTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：rTensor (f : A ->ₐ[S] C) : A otimes[R] B ->ₐ[S] C otimes[R] B
参数：f : A ->ₐ[S] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rTensor B f : A ⊗ B →ₐ C ⊗ B` is the natural algebra morphism induced by `f : A
 →ₐ C`.
-/
abbrev rTensor (f : A →ₐ[S] C) : A ⊗[R] B →ₐ[S] C ⊗[R] B := map f (.id R B)

/-- Construct an isomorphism between tensor products of an S-algebra with an R-algebra
from S- and R- isomorphisms between the tensor factors.
-/
/-
**Algebra.TensorProduct.congr** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A otimes[R] B ≃ₐ[S] C otimes[R] D
参数：f : A ≃ₐ[S] C；g : B ≃ₐ[R] D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between tensor products of an S-algebra with an R-algeb
ra
from S- and R- isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : A ⊗[R] B ≃ₐ[S] C ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)
/-
**Algebra.TensorProduct.congr_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} {C : Type uC} {D
 : Type uD} [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : Algebr
a R S] [inst_3 : Semiring A] [inst_4 : Algebra R A] [inst_5 : Algebra S A]   [in
st_6 : IsScalarTower R S A] [inst_7 : Semiring B] [inst_8 : Algebra R B] [inst_9
 : Semiring C]   [inst_10 : Algebra R C] [inst_11 : Algebra S C] [inst_12 : IsSc
alarTower R S C] [inst_13 : Semiring D]   [inst_14 : Algebra R D] (f : A ≃ₐ[S] C
) (g : B ≃ₐ[R] D),   ↑(Algebra.TensorProduct.congr f g) = TensorProduct.AlgebraT
ensorModule.congr ↑f ↑g
参数：f : A ≃ₐ[S] C；g : B ≃ₐ[R] D；Algebra.TensorProduct.congr f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp]
/-
**Algebra.TensorProduct.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：congr_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) : congr f g x = (map (f : 
A ->ₐ[S] C) (g : B ->ₐ[R] D)) x
参数：f : A ≃ₐ[S] C；g : B ≃ₐ[R] D；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem congr_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A →ₐ[S] C) (g : B →ₐ[R] D)) x :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.congr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：congr_symm_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) : (congr f g).symm x 
= (map (f.symm : C ->ₐ[S] A) (g.symm : D ->ₐ[R] B)) x
参数：f : A ≃ₐ[S] C；g : B ≃ₐ[R] D；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem congr_symm_apply (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : C →ₐ[S] A) (g.symm : D →ₐ[R] B)) x :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.map_id`：map_id : map (.id S A) (.id R B) = .id S _
-/
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : B ≃ₐ[R] B) = .refl :=
  AlgEquiv.coe_toAlgHom_injective <| map_id
/-
**Algebra.TensorProduct.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：congr_trans (f₁ : A ≃ₐ[S] C) (f₂ : C ≃ₐ[S] E) (g₁ : B ≃ₐ[R] D) (g₂ : D ≃ₐ[
R] F) : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂)
参数：f₁ : A ≃ₐ[S] C；f₂ : C ≃ₐ[S] E；g₁ : B ≃ₐ[R] D；g₂ : D ≃ₐ[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.map_comp`：map_comp (f₂ : C ->ₐ[S] E) (f₁ : A ->ₐ[S
] C) (g₂ : D ->ₐ[R] F) (g₁ : B ->ₐ[R] D) : map (f₂.comp f₁) (g₂.comp g₁) = (map 
f₂ g₂).comp (map f₁ …
-/
theorem congr_trans
    (f₁ : A ≃ₐ[S] C) (f₂ : C ≃ₐ[S] E) (g₁ : B ≃ₐ[R] D) (g₂ : D ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  AlgEquiv.coe_toAlgHom_injective <| map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom
/-
**Algebra.TensorProduct.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：congr_symm (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : congr f.symm g.symm = (congr 
f g).symm
参数：f : A ≃ₐ[S] C；g : B ≃ₐ[R] D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem congr_symm (f : A ≃ₐ[S] C) (g : B ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl

variable (R A B C) in
/-- Tensor product of algebras analogue of `mul_left_comm`.

This is the algebra version of `TensorProduct.leftComm`. -/
/-
**Algebra.TensorProduct.leftComm** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduc
t`。
形式化陈述：leftComm : A otimes[R] (B otimes[R] C) ≃ₐ[R] B otimes[R] (A otimes[R] C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product of algebras analogue of `mul_left_comm`.

This is the algebra version of `TensorProduct.leftComm`.
-/
def leftComm : A ⊗[R] (B ⊗[R] C) ≃ₐ[R] B ⊗[R] (A ⊗[R] C) :=
  (Algebra.TensorProduct.assoc R R R A B C).symm.trans <|
    (congr (Algebra.TensorProduct.comm R A B) .refl).trans <| TensorProduct.assoc R R R B A C

@[simp]
/-
**Algebra.TensorProduct.leftComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：leftComm_tmul (m : A) (n : B) (p : C) : leftComm R A B C (m otimesₜ (n oti
mesₜ p)) = n otimesₜ (m otimesₜ p)
参数：m : A；n : B；p : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftComm_tmul (m : A) (n : B) (p : C) :
    leftComm R A B C (m ⊗ₜ (n ⊗ₜ p)) = n ⊗ₜ (m ⊗ₜ p) :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.leftComm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Te
nsorProduct`。
形式化陈述：leftComm_symm_tmul (m : A) (n : B) (p : C) : (leftComm R A B C).symm (n ot
imesₜ (m otimesₜ p)) = m otimesₜ (n otimesₜ p)
参数：m : A；n : B；p : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftComm_symm_tmul (m : A) (n : B) (p : C) :
    (leftComm R A B C).symm (n ⊗ₜ (m ⊗ₜ p)) = m ⊗ₜ (n ⊗ₜ p) :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.leftComm_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：leftComm_toLinearEquiv : ↑(leftComm R A B C) = _root_.TensorProduct.leftCo
mm R A B C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem leftComm_toLinearEquiv : ↑(leftComm R A B C) = _root_.TensorProduct.leftComm R A B C :=
  LinearEquiv.toLinearMap_injective (by ext; rfl)

variable [CommSemiring T] [Algebra R T] [Algebra T A] [IsScalarTower R T A] [SMulCommClass S T A]
  [Algebra S T] [IsScalarTower S T A] [CommSemiring R'] [Algebra R R'] [Algebra R' T] [Algebra R' A]
  [Algebra R' B] [IsScalarTower R R' A] [SMulCommClass S R' A] [SMulCommClass R' S A]
  [IsScalarTower R' T A] [IsScalarTower R R' B]

variable (R R' S T A B C D) in
/-- Tensor product of algebras analogue of `mul_mul_mul_comm`.

This is the algebra version of `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`. -/
/-
**Algebra.TensorProduct.tensorTensorTensorComm** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：tensorTensorTensorComm : A otimes[R'] B otimes[S] (C otimes[R] D) ≃ₐ[T] A 
otimes[S] C otimes[R'] (B otimes[R] D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product of algebras analogue of `mul_mul_mul_comm`.

This is the algebra version of `TensorProduct.AlgebraTensorModule.tensorTensorTe
nsorComm`.
-/
def tensorTensorTensorComm : A ⊗[R'] B ⊗[S] (C ⊗[R] D) ≃ₐ[T] A ⊗[S] C ⊗[R'] (B ⊗[R] D) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D)
    rfl (LinearMap.map_mul_iff _ |>.mpr <| by ext; simp)

@[simp]
/-
**Algebra.TensorProduct.tensorTensorTensorComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) : tensorTensor
TensorComm R R' S T A B C D (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ p ot
imesₜ (n otimesₜ q)
参数：m : A；n : B；p : C；q : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_tmul (m : A) (n : B) (p : C) (q : D) :
    tensorTensorTensorComm R R' S T A B C D (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.tensorTensorTensorComm_symm_tmul** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.TensorProduct`。
形式化陈述：tensorTensorTensorComm_symm_tmul (m : A) (n : C) (p : B) (q : D) : (tensor
TensorTensorComm R R' S T A B C D).symm (m otimesₜ n otimesₜ (p otimesₜ q)) = m 
otimesₜ p otimesₜ (n otimesₜ q)
参数：m : A；n : C；p : B；q : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_symm_tmul (m : A) (n : C) (p : B) (q : D) :
    (tensorTensorTensorComm R R' S T A B C D).symm (m ⊗ₜ n ⊗ₜ (p ⊗ₜ q)) = m ⊗ₜ p ⊗ₜ (n ⊗ₜ q) :=
  rfl
/-
**Algebra.TensorProduct.tensorTensorTensorComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：tensorTensorTensorComm_symm : (tensorTensorTensorComm R R' S T A B C D).sy
mm = tensorTensorTensorComm R S R' T A C B D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R R' S T A B C D).symm = tensorTensorTensorComm R S R' T A C B D := rfl
/-
**Algebra.TensorProduct.tensorTensorTensorComm_toLinearEquiv** 是 Mathlib 中的一个定理，
位于命名空间 `Algebra.TensorProduct`。
形式化陈述：tensorTensorTensorComm_toLinearEquiv : (tensorTensorTensorComm R R' S T A 
B C D).toLinearEquiv = TensorProduct.AlgebraTensorModule.tensorTensorTensorComm 
R R' S T A B C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_toLinearEquiv :
    (tensorTensorTensorComm R R' S T A B C D).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' S T A B C D := rfl

@[simp]
/-
**Algebra.TensorProduct.toLinearEquiv_tensorTensorTensorComm** 是 Mathlib 中的一个定理，
位于命名空间 `Algebra.TensorProduct`。
形式化陈述：toLinearEquiv_tensorTensorTensorComm : (tensorTensorTensorComm R R R R A B
 C D).toLinearEquiv = _root_.TensorProduct.tensorTensorTensorComm R A B C D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem toLinearEquiv_tensorTensorTensorComm :
    (tensorTensorTensorComm R R R R A B C D).toLinearEquiv =
      _root_.TensorProduct.tensorTensorTensorComm R A B C D := rfl
/-
**Algebra.TensorProduct.map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.TensorP
roduct`。
形式化陈述：map_bijective {f : A ->ₐ[R] B} {g : C ->ₐ[R] D} (hf : Function.Bijective f
) (hg : Function.Bijective g) : Function.Bijective (map f g)
参数：hf : Function.Bijective f；hg : Function.Bijective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.map_bijective`：map_bijective {f : M ->ₗ[R] N} {g : P ->ₗ[R
] Q} (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijectiv
e (map f g)
-/
lemma map_bijective {f : A →ₐ[R] B} {g : C →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  _root_.TensorProduct.map_bijective hf hg
/-
**Algebra.TensorProduct.includeLeft_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：includeLeft_bijective (h : Function.Bijective (algebraMap R B)) : Function
.Bijective (includeLeft : A ->ₐ[S] A otimes[R] B)
参数：h : Function.Bijective (algebraMap R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用引理 `Algebra.TensorProduct.map_bijective`：map_bijective {f : A ->ₐ[R] B} {g :
 C ->ₐ[R] D} (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.
Bijective (map f g)
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma includeLeft_bijective (h : Function.Bijective (algebraMap R B)) :
    Function.Bijective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  have : (includeLeft : A →ₐ[S] A ⊗[R] B).comp (TensorProduct.rid R S A).toAlgHom =
      map (.id S A) (Algebra.ofId R B) := by ext; simp
  rw [← Function.Bijective.of_comp_iff _ (TensorProduct.rid R S A).bijective]
  convert_to Function.Bijective (map (.id R A) (Algebra.ofId R B))
  · exact DFunLike.coe_fn_eq.mpr this
  · exact Algebra.TensorProduct.map_bijective Function.bijective_id h
/-
**Algebra.TensorProduct.includeRight_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：includeRight_bijective (h : Function.Bijective (algebraMap R A)) : Functio
n.Bijective (includeRight : B ->ₐ[R] A otimes[R] B)
参数：h : Function.Bijective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用引理 `Algebra.TensorProduct.includeLeft_bijective`：includeLeft_bijective (h : 
Function.Bijective (algebraMap R B)) : Function.Bijective (includeLeft : A ->ₐ[S
] A otimes[R] B)
-/
lemma includeRight_bijective (h : Function.Bijective (algebraMap R A)) :
    Function.Bijective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  rw [← Function.Bijective.of_comp_iff' (TensorProduct.comm R A B).bijective]
  exact Algebra.TensorProduct.includeLeft_bijective (S := R) h

end

end Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A`, `B`, `C` are `R`-algebras, `A` and `C` are also `S`-algebras (forming a tower as
`·/S/R`), then the product map of `f : A →ₐ[S] C` and `g : B →ₐ[R] C` is an `S`-algebra
homomorphism.

This is just a special case of `Algebra.TensorProduct.lift` for when `C` is commutative. -/
/-
**Algebra.TensorProduct.productLeftAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：productLeftAlgHom (f : A ->ₐ[S] C) (g : B ->ₐ[R] C) : A otimes[R] B ->ₐ[S]
 C
参数：f : A ->ₐ[S] C；g : B ->ₐ[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A`, `B`, `C` are `R`-algebras, `A` and `C` are also `S`-algebras (forming a 
tower as
`·/S/R`), then the product map of `f : A →ₐ[S] C` and `g : B →ₐ[R] C` is an `S`-
algebra
homomorphism.

This is just a special case of `Algebra.TensorProduct.lift` for when `C` is comm
utative.
-/
abbrev productLeftAlgHom (f : A →ₐ[S] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)
/-
**Algebra.TensorProduct.tmul_one_eq_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.
TensorProduct`。
形式化陈述：tmul_one_eq_one_tmul (r : R) : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ a
lgebraMap R B r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
lemma tmul_one_eq_one_tmul (r : R) : algebraMap R A r ⊗ₜ[R] 1 = 1 ⊗ₜ algebraMap R B r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

end

section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)
variable (R)

/-- `LinearMap.mul'` as an `AlgHom` over the algebra. -/
/-
**Algebra.TensorProduct.lmul''** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`
。
形式化陈述：lmul'' : S otimes[R] S ->ₐ[S] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.mul'` as an `AlgHom` over the algebra.
-/
def lmul'' : S ⊗[R] S →ₐ[S] S :=
  algHomOfLinearMapTensorProduct
    { __ := LinearMap.mul' R S
      map_smul' := fun s x ↦ x.induction_on (by simp)
        (fun _ _ ↦ by simp [TensorProduct.smul_tmul', mul_assoc])
        fun x y hx hy ↦ by simp_all [mul_add] }
    (fun a₁ a₂ b₁ b₂ => by simp [mul_mul_mul_comm]) <| by simp
/-
**Algebra.TensorProduct.lmul''_eq_lid_comp_mapOfCompatibleSMul** 是 Mathlib 中的一个定
理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：∀ (R : Type uR) {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S] [inst_2 : Algebra R S],   Algebra.TensorProduct.lmul'' R =     (↑(Algebra.
TensorProduct.lid S S)).comp (Algebra.TensorProduct.mapOfCompatibleSMul S R S S 
S)
参数：R : Type uR；↑(Algebra.TensorProduct.lid S S)；Algebra.TensorProduct.mapOfCompa
tibleSMul S R S S S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem lmul''_eq_lid_comp_mapOfCompatibleSMul :
    lmul'' R = (TensorProduct.lid S S).toAlgHom.comp (mapOfCompatibleSMul ..) := by
  ext; rfl

/-- `LinearMap.mul'` as an `AlgHom` over the base ring. -/
/-
**Algebra.TensorProduct.lmul'** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：lmul' : S otimes[R] S ->ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.mul'` as an `AlgHom` over the base ring.
-/
def lmul' : S ⊗[R] S →ₐ[R] S := (lmul'' R).restrictScalars R

variable {R}
/-
**Algebra.TensorProduct.lmul'_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ten
sorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S] [inst_2 : Algebra R S],   (Algebra.TensorProduct.lmul' R).toLinearMap = Li
nearMap.mul' R S
参数：Algebra.TensorProduct.lmul' R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lmul'_toLinearMap : (lmul' R : _ →ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.lmul'_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S] [inst_2 : Algebra R S] (a b : S),   (Algebra.TensorProduct.lmul' R) (a ⊗ₜ[
R] b) = a * b
参数：a b : S；Algebra.TensorProduct.lmul' R；a ⊗ₜ[R] b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.lmul'_comp_includeLeft** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S] [inst_2 : Algebra R S],   (Algebra.TensorProduct.lmul' R).comp Algebra.Ten
sorProduct.includeLeft = AlgHom.id R S
参数：Algebra.TensorProduct.lmul' R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem lmul'_comp_includeLeft : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext <| mul_one

@[simp]
/-
**Algebra.TensorProduct.lmul'_comp_includeRight** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.TensorProduct`。
形式化陈述：∀ {R : Type uR} {S : Type uS} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S] [inst_2 : Algebra R S],   (Algebra.TensorProduct.lmul' R).comp Algebra.Ten
sorProduct.includeRight = AlgHom.id R S
参数：Algebra.TensorProduct.lmul' R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lmul'_comp_includeRight : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext <| one_mul
/-
**Algebra.TensorProduct.lmul'_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tensor
Product`。
形式化陈述：∀ {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : CommSemiring S] 
[inst_4 : Algebra R A] [inst_5 : Algebra R B] [inst_6 : Algebra R S]   (f : A →ₐ
[R] S) (g : B →ₐ[R] S),   (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorPr
oduct.map f g) = Algebra.TensorProduct.lift f g ⋯
参数：f : A →ₐ[R] S；g : B →ₐ[R] S；Algebra.TensorProduct.lmul' R；Algebra.TensorProdu
ct.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
lemma lmul'_comp_map (f : A →ₐ[R] S) (g : B →ₐ[R] S) :
    (lmul' R).comp (map f g) = lift f g (fun _ _ ↦ .all _ _) := by ext <;> rfl

variable (R S) in
/-- If multiplication by elements of S can switch between the two factors of `S ⊗[R] S`,
then `lmul''` is an isomorphism. -/
/-
**Algebra.TensorProduct.lmulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProdu
ct`。
形式化陈述：lmulEquiv [CompatibleSMul R S S S] : S otimes[R] S ≃ₐ[S] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If multiplication by elements of S can switch between the two factors of `S ⊗[R]
 S`,
then `lmul''` is an isomorphism.
-/
def lmulEquiv [CompatibleSMul R S S S] : S ⊗[R] S ≃ₐ[S] S :=
  .ofAlgHom (lmul'' R) includeLeft lmul'_comp_includeLeft <| AlgHom.ext fun x ↦ x.induction_on
    (by simp) (fun x y ↦ show (x * y) ⊗ₜ[R] 1 = x ⊗ₜ[R] y by
      rw [mul_comm, ← smul_eq_mul, smul_tmul, smul_eq_mul, mul_one])
    fun _ _ hx hy ↦ by simp_all [add_tmul]
/-
**Algebra.TensorProduct.lmulEquiv_eq_lidOfCompatibleSMul** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.TensorProduct`。
形式化陈述：lmulEquiv_eq_lidOfCompatibleSMul [CompatibleSMul R S S S] : lmulEquiv R S 
= lidOfCompatibleSMul R S S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.coe_toAlgHom_injective`：coe_toAlgHom_injective : Function.Injec
tive ((↑) : (A₁ ≃ₐ[R] A₂) -> A₁ ->ₐ[R] A₂)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem lmulEquiv_eq_lidOfCompatibleSMul [CompatibleSMul R S S S] :
    lmulEquiv R S = lidOfCompatibleSMul R S S :=
  AlgEquiv.coe_toAlgHom_injective <| by ext; rfl

/-- If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.

This is a special case of `Algebra.TensorProduct.productLeftAlgHom` for when the two base rings are
the same.
-/
/-
**Algebra.TensorProduct.productMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.TensorProd
uct`。
形式化陈述：productMap : A otimes[R] B ->ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a)
 * g(b)`.

This is a special case of `Algebra.TensorProduct.productLeftAlgHom` for when the
 two base rings are
the same.
-/
def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g
/-
**Algebra.TensorProduct.productMap_eq_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.ma
p f g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl

@[simp]
/-
**Algebra.TensorProduct.productMap_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：productMap_apply_tmul (a : A) (b : B) : productMap f g (a otimesₜ b) = f a
 * g b
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl
/-
**Algebra.TensorProduct.productMap_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：productMap_left_apply (a : A) : productMap f g (a otimesₜ 1) = f a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp

@[simp]
/-
**Algebra.TensorProduct.productMap_left** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tenso
rProduct`。
形式化陈述：productMap_left : (productMap f g).comp includeLeft = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.lift_comp_includeLeft`：lift_comp_includeLeft (f : 
A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) : (lift f g
 hfg).comp includeLeft = f
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
/-
**Algebra.TensorProduct.productMap_right_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：productMap_right_apply (b : B) : productMap f g (1 otimesₜ b) = g b
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp

@[simp]
/-
**Algebra.TensorProduct.productMap_right** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：productMap_right : (productMap f g).comp includeRight = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.lift_comp_includeRight`：lift_comp_includeRight (f 
: A ->ₐ[S] C) (g : B ->ₐ[R] C) (hfg : forall x y, Commute (f x) (g y)) : ((lift 
f g hfg).restrictScalars R).comp i…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
/-
**Algebra.TensorProduct.productMap_range** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Tens
orProduct`。
形式化陈述：productMap_range : (productMap f g).range = f.range ⊔ g.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.TensorProduct.productMap_eq_comp_map`：productMap_eq_comp_map : p
roductMap f g = (lmul' R).comp (TensorProduct.map f g)
· 使用定理 `AlgHom.range_comp`：range_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) : (g.com
p f).range = f.range.map g
· 使用定理 `Algebra.TensorProduct.map_range`：map_range (f : A ->ₐ[R] C) (g : B ->ₐ[R
] D) : (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).rang
e
· 使用定理 `Algebra.map_sup`：map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ 
T).map f = S.map f ⊔ T.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `Algebra.TensorProduct.lmul'_comp_includeLeft`：∀ {R : Type uR} {S : Type 
uS} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   
(Algebra.TensorProduct.lmul' R).co…
· 使用定理 `Algebra.TensorProduct.lmul'_comp_includeRight`：∀ {R : Type uR} {S : Type
 uS} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],  
 (Algebra.TensorProduct.lmul' R).co…
· 使用定理 `AlgHom.id_comp`：id_comp : (AlgHom.id R B).comp φ = φ
-/
theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp,
    ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]

end

end TensorProduct

end Algebra

namespace LinearMap

variable (R A M N : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Module
open scoped TensorProduct

/-- The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism. -/
@[simps!]
/-
**LinearMap.tensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：tensorProduct : A otimes[R] (M ->ₗ[R] N) ->ₗ[A] (A otimes[R] M) ->ₗ[A] (A 
otimes[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension 
of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism.
-/
def tensorProduct : A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

/-- The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M)$,
where `M` is an `R`-module, and `A` an `R`-algebra. -/
@[simps!]
/-
**LinearMap.tensorProductEnd** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：tensorProductEnd : A otimes[R] (End R M) ->ₐ[A] End A (A otimes[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M
)$,
where `M` is an `R`-module, and `A` an `R`-algebra.
-/
def tensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, Module.End.mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, Module.End.one_eq_id,
        lTensor_id, LinearMap.id_apply])

/-- If `R →+* S` is surjective, the multiplication map `S ⊗[R] S →+* S` is an isomorphism. This
is the algebraic version of closed immersions are monomorphisms. -/
/-
**LinearMap.mul'_bijective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ (R : Type u_1) (A : Type u_2) [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A],   Function.Surjective ⇑(algebraMap R A) → Functi
on.Bijective ⇑(LinearMap.mul' R A)
参数：R : Type u_1；A : Type u_2；algebraMap R A；LinearMap.mul' R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.CompatibleSMul.of_algebraMap_surjective`：∀ {R : Type u_1} 
[inst : CommSemiring R] (M : Type u_5) (N : Type u_6) [inst_1 : AddCommMonoid M]
   [inst_2 : AddCommMonoid N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
If `R →+* S` is surjective, the multiplication map `S ⊗[R] S →+* S` is an isomor
phism. This
is the algebraic version of closed immersions are monomorphisms.
-/
lemma mul'_bijective_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Function.Bijective (LinearMap.mul' R A) :=
  have : TensorProduct.CompatibleSMul R A A A := .of_algebraMap_surjective _ _ h
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end LinearMap

namespace Module

variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `TensorProduct.map f g`, the tensor product of the two maps.

This is an `AlgHom` version of `TensorProduct.AlgebraTensorModule.homTensorHomMap`. Like that
definition, this is generalized across many different rings; namely a tower of algebras `A/S/R`. -/
/-
**Module.endTensorEndAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：endTensorEndAlgHom : End A M otimes[R] End R N ->ₐ[S] End A (M otimes[R] N
)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` 
to
the `TensorProduct.map f g`, the tensor product of the two maps.

This is an `AlgHom` version of `TensorProduct.AlgebraTensorModule.homTensorHomMa
p`. Like that
definition, this is generalized across many different rings; namely a tower of a
lgebras `A/S/R`.
-/
def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)
/-
**Module.endTensorEndAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：endTensorEndAlgHom_apply (f : End A M) (g : End R N) : endTensorEndAlgHom 
(R
参数：f : End A M；g : End R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl

end Module

/-- Given a subalgebra `C` of an `R`-algebra `A`, and an `R`-algebra `B`, the base change of `C` to
a subalgebra of `B ⊗[R] A` -/
/-
**Subalgebra.baseChange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subalgebra.baseChange {R A : Type*} [CommSemiring R] [Semiring A] [Algebra
 R A] (B : Type*) [CommSemiring B] [Algebra R B] (C : Subalgebra R A) : Subalgeb
ra B (B otimes[R] A)
参数：B : Type*；C : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subalgebra `C` of an `R`-algebra `A`, and an `R`-algebra `B`, the base c
hange of `C` to
a subalgebra of `B ⊗[R] A`
-/
def Subalgebra.baseChange {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (B : Type*) [CommSemiring B] [Algebra R B] (C : Subalgebra R A) : Subalgebra B (B ⊗[R] A) :=
  AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

variable {R A B : Type*} [CommSemiring R] [Semiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
variable {C : Subalgebra R A}
/-
**Subalgebra.tmul_mem_baseChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.tmul_mem_baseChange {x : A} (hx : x in C) (b : B) : b otimesₜ[R
] x in C.baseChange B
参数：hx : x in C；b : B。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subalgebra.tmul_mem_baseChange {x : A} (hx : x ∈ C) (b : B) : b ⊗ₜ[R] x ∈ C.baseChange B :=
  ⟨(b ⊗ₜ[R] ⟨x, hx⟩), rfl⟩

section

universe u₁ u₂ u₃ u₄ u₅

variable (R S A B : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Semiring B] [Algebra R B]

attribute [local instance] ULift.algebra' in
/-- `ULift` commutes with tensor products of algebras. -/
/-
**Algebra.TensorProduct.uliftEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.uliftEquiv : ULift.{u₁} (A otimes[R] B) ≃ₐ[S] ULift.
{u₂} A otimes[ULift.{u₃} R] ULift.{u₄} B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift` commutes with tensor products of algebras.
-/
def Algebra.TensorProduct.uliftEquiv :
    ULift.{u₁} (A ⊗[R] B) ≃ₐ[S] ULift.{u₂} A ⊗[ULift.{u₃} R] ULift.{u₄} B :=
  AlgEquiv.trans ULift.algEquiv
    (.trans (congr ULift.algEquiv.symm ULift.algEquiv.symm) <|
      Algebra.TensorProduct.equivOfCompatibleSMul _ _ _ _ _)

variable {A B}

@[simp]
/-
**Algebra.TensorProduct.uliftEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.uliftEquiv_tmul (a : A) (b : B) : uliftEquiv R S A B
 ⟨a otimesₜ b⟩ = ⟨a⟩ otimesₜ ⟨b⟩
参数：a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma Algebra.TensorProduct.uliftEquiv_tmul (a : A) (b : B) :
    uliftEquiv R S A B ⟨a ⊗ₜ b⟩ = ⟨a⟩ ⊗ₜ ⟨b⟩ :=
  rfl

attribute [local instance] ULift.algebra' in
@[simp]
/-
**Algebra.TensorProduct.down_uliftEquiv_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.down_uliftEquiv_symm_tmul (a : ULift A) (b : ULift B
) : ((uliftEquiv R S A B).symm (a otimesₜ b)).down = a.down otimesₜ b.down
参数：a : ULift A；b : ULift B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma Algebra.TensorProduct.down_uliftEquiv_symm_tmul (a : ULift A) (b : ULift B) :
    ((uliftEquiv R S A B).symm (a ⊗ₜ b)).down = a.down ⊗ₜ b.down :=
  rfl

attribute [local instance] ULift.algebra' in
/-
**Algebra.TensorProduct.uliftEquiv_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.TensorProduct.uliftEquiv_symm_tmul (a : ULift A) (b : ULift B) : (
uliftEquiv R S A B).symm (a otimesₜ b) = ⟨a.down otimesₜ b.down⟩
参数：a : ULift A；b : ULift B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma Algebra.TensorProduct.uliftEquiv_symm_tmul (a : ULift A) (b : ULift B) :
    (uliftEquiv R S A B).symm (a ⊗ₜ b) = ⟨a.down ⊗ₜ b.down⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ULift.algebra' in
/-
**Algebra.TensorProduct.lmul'_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.TensorPro
duct`。
形式化陈述：∀ (R : Type u_4) (S : Type u_5) [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S],   Algebra.TensorProduct.lmul' (ULift.{u₁, u_4} R
) =     (AlgHom.ulift.{u_8, u₁, u₂, u_4, u_5, u_5} (Algebra.TensorProduct.lmul' 
R)).comp       ↑(Algebra.TensorProduct.uliftEquiv R (ULift.{u₁, u_4} R) S S).sym
m
参数：R : Type u_4；S : Type u_5；ULift.{u₁, u_4} R；AlgHom.ulift.{u_8, u₁, u₂, u_4, u
_5, u_5} (Algebra.TensorProduct.lmul' R)；Algebra.TensorProduct.uliftEquiv R (ULi
ft.{u₁, u_4} R) S S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.lmul'_comp_includeLeft`：∀ {R : Type uR} {S : Type 
uS} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   
(Algebra.TensorProduct.lmul' R).co…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma Algebra.TensorProduct.lmul'_ulift :
    TensorProduct.lmul' (S := ULift.{u₂} S) (ULift.{u₁} R) =
      (TensorProduct.lmul' (S := S) R).ulift.comp
        (uliftEquiv _ _ _ _).symm.toAlgHom := by
  ext <;> simp

end

