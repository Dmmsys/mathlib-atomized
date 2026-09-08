/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Pi

/-!

# Tensor product and products

In this file we examine the behaviour of the tensor product with arbitrary and finite products.

Let `S` be an `R`-algebra, `N` an `S`-module, `ι` an index type and `Mᵢ` a family of `R`-modules.
We then have a natural map

`TensorProduct.piRightHom`: `N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i`

In general, this is not an isomorphism, but if `ι` is finite, then it is
and it is packaged as `TensorProduct.piRight`. Also a special case for when `Mᵢ = R` is given.

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Prod.lean` for binary products.

-/

@[expose] public section

variable (R : Type*) [CommSemiring R]
variable (S : Type*) [CommSemiring S] [Algebra R S]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

open LinearMap

namespace TensorProduct

section

variable {ι} (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- (Implementation): Bilinear map for defining `TensorProduct.piRightHom`. -/
/-
**TensorProduct.piRightHomBil** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piRightHomBil : N ->ₗ[S] (forall i, M i) ->ₗ[R] forall i, N otimes[R] M i 
where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Bilinear map for defining `TensorProduct.piRightHom`.
-/
def piRightHomBil : N →ₗ[S] (∀ i, M i) →ₗ[R] ∀ i, N ⊗[R] M i where
  toFun n := LinearMap.pi (fun i ↦ mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := rfl

/-- For any `R`-module `N`, index type `ι` and family of `R`-modules `Mᵢ`, there is a natural
linear map `N ⊗[R] (∀ i, M i) →ₗ ∀ i, N ⊗[R] M i`. This map is an isomorphism if `ι` is finite. -/
/-
**TensorProduct.piRightHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piRightHom : N otimes[R] (forall i, M i) ->ₗ[S] forall i, N otimes[R] M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-module `N`, index type `ι` and family of `R`-modules `Mᵢ`, there is 
a natural
linear map `N ⊗[R] (∀ i, M i) →ₗ ∀ i, N ⊗[R] M i`. This map is an isomorphism if
 `ι` is finite.
-/
def piRightHom : N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i :=
  AlgebraTensorModule.lift <| piRightHomBil R S N M

@[simp]
/-
**TensorProduct.piRightHom_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piRightHom_tmul (x : N) (f : forall i, M i) : piRightHom R S N M (x otimes
ₜ f) = (fun j => x otimesₜ f j)
参数：x : N；f : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piRightHom_tmul (x : N) (f : ∀ i, M i) :
    piRightHom R S N M (x ⊗ₜ f) = (fun j ↦ x ⊗ₜ f j) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- (Implementation): Inverse for `TensorProduct.piRight`. -/
/-
**TensorProduct.piRightInv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piRightInv : (forall i, N otimes[R] M i) ->ₗ[S] N otimes[R] forall i, M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Inverse for `TensorProduct.piRight`.
-/
def piRightInv : (∀ i, N ⊗[R] M i) →ₗ[S] N ⊗[R] ∀ i, M i :=
  LinearMap.lsum S (fun i ↦ N ⊗[R] M i) S <| fun i ↦
    AlgebraTensorModule.map LinearMap.id (single R M i)

@[simp]
/-
**TensorProduct.piRightInv_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma piRightInv_apply (x : N) (m : ∀ i, M i) :
    piRightInv R S N M (fun i ↦ x ⊗ₜ m i) = x ⊗ₜ m := by
  simp only [piRightInv, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_single]
  rw [← tmul_sum]
  congr
  ext j
  simp

@[simp]
/-
**TensorProduct.piRightInv_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma piRightInv_single (x : N) (i : ι) (m : M i) :
    piRightInv R S N M (Pi.single i (x ⊗ₜ m)) = x ⊗ₜ Pi.single i m := by
  have : Pi.single i (x ⊗ₜ m) = fun j ↦ x ⊗ₜ[R] (Pi.single i m j) := by
    ext j
    rw [← tmul_single]
  rw [this]
  simp

/-- Tensor product commutes with finite products on the right. -/
/-
**TensorProduct.piRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piRight : N otimes[R] (forall i, M i) ≃ₗ[S] forall i, N otimes[R] M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product commutes with finite products on the right.
-/
def piRight : N ⊗[R] (∀ i, M i) ≃ₗ[S] ∀ i, N ⊗[R] M i :=
  LinearEquiv.ofLinearMap
    (piRightHom R S N M)
    (piRightInv R S N M)
    (by ext i x m j; simp [tmul_single])
    (by ext x j m; simp)

@[simp]
/-
**TensorProduct.piRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piRight_apply (x : N otimes[R] (forall i, M i)) : piRight R S N M x = piRi
ghtHom R S N M x
参数：x : N otimes[R] (forall i, M i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piRight_apply (x : N ⊗[R] (∀ i, M i)) :
    piRight R S N M x = piRightHom R S N M x := by
  rfl

@[simp]
/-
**TensorProduct.piRight_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piRight_symm_apply (x : N) (m : forall i, M i) : (piRight R S N M).symm (f
un i => x otimesₜ m i) = x otimesₜ m
参数：x : N；m : forall i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.TensorProduct.Pi.0.TensorProduct.piRightI
nv_apply`：∀ (R : Type u_1) [inst : CommSemiring R] (S : Type u_2) [inst_1 : Comm
Semiring S] [inst_2 : Algebra R S] (N : Type u_3)   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piRight_symm_apply (x : N) (m : ∀ i, M i) :
    (piRight R S N M).symm (fun i ↦ x ⊗ₜ m i) = x ⊗ₜ m := by
  simp [piRight]

@[simp]
/-
**TensorProduct.piRight_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piRight_symm_single (x : N) (i : ι) (m : M i) : (piRight R S N M).symm (Pi
.single i (x otimesₜ m)) = x otimesₜ Pi.single i m
参数：x : N；i : ι；m : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.TensorProduct.Pi.0.TensorProduct.piRightI
nv_single`：∀ (R : Type u_1) [inst : CommSemiring R] (S : Type u_2) [inst_1 : Com
mSemiring S] [inst_2 : Algebra R S] (N : Type u_3)   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piRight_symm_single (x : N) (i : ι) (m : M i) :
    (piRight R S N M).symm (Pi.single i (x ⊗ₜ m)) = x ⊗ₜ Pi.single i m := by
  simp [piRight]

/-- Tensor product commutes with finite products on the left.
TODO: generalize to `S`-linear. -/
/-
**TensorProduct.piLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (N : Type u_3) →       [i
nst_1 : AddCommMonoid N] →         [inst_2 : _root_.Module R N] →           {ι :
 Type u_4} →             (M : ι → Type u_5) →               [inst_3 : (i : ι) → 
AddCommMonoid (M i)] →                 [inst_4 : (i : ι) → _root_.Module R (M i)
] →                   [Fintype ι] →                     [DecidableEq ι] → Tensor
Product R ((i : ι) → M i) N ≃ₗ[R] (i : ι) → TensorProduct R (M i) N
参数：i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product commutes with finite products on the left.
TODO: generalize to `S`-linear.
-/
@[simp] def piLeft : (∀ i, M i) ⊗[R] N ≃ₗ[R] ∀ i, M i ⊗[R] N :=
  TensorProduct.comm .. ≪≫ₗ piRight .. ≪≫ₗ .piCongrRight fun _ ↦ TensorProduct.comm ..

end

set_option backward.defeqAttrib.useBackward true in
/-- Internal implementation detail: we should make this `private`. -/
/-
**TensorProduct.piScalarRightHomBil** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRightHomBil : N ->ₗ[S] (ι -> R) ->ₗ[R] (ι -> N) where toFun n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Internal implementation detail: we should make this `private`.
-/
def piScalarRightHomBil : N →ₗ[S] (ι → R) →ₗ[R] (ι → N) where
  toFun n := LinearMap.compLeft (toSpanSingleton R N n) ι
  map_add' x y := by
    ext i j
    simp
  map_smul' s x := by
    ext i j
    dsimp only [coe_comp, coe_single, Function.comp_apply, compLeft_apply, toSpanSingleton_apply,
      RingHom.id_apply, smul_apply, Pi.smul_apply]
    rw [← IsScalarTower.smul_assoc, _root_.Algebra.smul_def, mul_comm, mul_smul]
    simp

/-- For any `R`-module `N` and index type `ι`, there is a natural
linear map `N ⊗[R] (ι → R) →ₗ (ι → N)`. This map is an isomorphism if `ι` is finite. -/
/-
**TensorProduct.piScalarRightHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRightHom : N otimes[R] (ι -> R) ->ₗ[S] (ι -> N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-module `N` and index type `ι`, there is a natural
linear map `N ⊗[R] (ι → R) →ₗ (ι → N)`. This map is an isomorphism if `ι` is fin
ite.
-/
def piScalarRightHom : N ⊗[R] (ι → R) →ₗ[S] (ι → N) :=
  AlgebraTensorModule.lift <| piScalarRightHomBil R S N ι

@[simp]
/-
**TensorProduct.piScalarRightHom_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRightHom_tmul (x : N) (f : ι -> R) : piScalarRightHom R S N ι (x o
timesₜ f) = (fun j => f j • x)
参数：x : N；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.compLeft_apply`：∀ {R : Type u} {M₂ : Type w} {M₃ : Type y} [in
st : Semiring R] [inst_1 : AddCommMonoid M₂] [inst_2 : _root_.Module R M₂]   [in
st_3 : AddComm…
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piScalarRightHom_tmul (x : N) (f : ι → R) :
    piScalarRightHom R S N ι (x ⊗ₜ f) = (fun j ↦ f j • x) := by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

variable [Fintype ι] [DecidableEq ι]

/-- (Implementation): Inverse for `TensorProduct.piScalarRight`. -/
/-
**TensorProduct.piScalarRightInv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRightInv : (ι -> N) ->ₗ[S] N otimes[R] (ι -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Inverse for `TensorProduct.piScalarRight`.
-/
def piScalarRightInv : (ι → N) →ₗ[S] N ⊗[R] (ι → R) :=
  LinearMap.lsum S (fun _ ↦ N) S <| fun i ↦ {
    toFun := fun n ↦ n ⊗ₜ Pi.single i 1
    map_add' := fun x y ↦ by simp [add_tmul]
    map_smul' := fun _ _ ↦ rfl
  }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TensorProduct.piScalarRightInv_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma piScalarRightInv_single (x : N) (i : ι) :
    piScalarRightInv R S N ι (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]

/-- For any `R`-module `N` and finite index type `ι`, `N ⊗[R] (ι → R)` is canonically
isomorphic to `ι → N`. -/
/-
**TensorProduct.piScalarRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRight : N otimes[R] (ι -> R) ≃ₗ[S] (ι -> N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-module `N` and finite index type `ι`, `N ⊗[R] (ι → R)` is canonicall
y
isomorphic to `ι → N`.
-/
def piScalarRight : N ⊗[R] (ι → R) ≃ₗ[S] (ι → N) :=
  LinearEquiv.ofLinearMap
    (piScalarRightHom R S N ι)
    (piScalarRightInv R S N ι)
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp [Pi.single_apply_smul])

@[simp]
/-
**TensorProduct.piScalarRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：piScalarRight_apply (x : N otimes[R] (ι -> R)) : piScalarRight R S N ι x =
 piScalarRightHom R S N ι x
参数：x : N otimes[R] (ι -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma piScalarRight_apply (x : N ⊗[R] (ι → R)) :
    piScalarRight R S N ι x = piScalarRightHom R S N ι x := by
  rfl

@[simp]
/-
**TensorProduct.piScalarRight_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProdu
ct`。
形式化陈述：piScalarRight_symm_single (x : N) (i : ι) : (piScalarRight R S N ι).symm (
Pi.single i x) = x otimesₜ Pi.single i 1
参数：x : N；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.TensorProduct.Pi.0.TensorProduct.piScalar
RightInv_single`：∀ (R : Type u_1) [inst : CommSemiring R] (S : Type u_2) [inst_1
 : CommSemiring S] [inst_2 : Algebra R S] (N : Type u_3)   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma piScalarRight_symm_single (x : N) (i : ι) :
    (piScalarRight R S N ι).symm (Pi.single i x) = x ⊗ₜ Pi.single i 1 := by
  simp [piScalarRight]

-- See also `TensorProduct.piScalarRight_symm_algebraMap` in
-- `Mathlib/RingTheory/TensorProduct/Pi.lean`.

end TensorProduct

