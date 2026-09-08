/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.DirectSum.Module
/-!
# Tensor products of direct sums

This file shows that taking `TensorProduct`s commutes with taking `DirectSum`s in both arguments.

## Main results

* `TensorProduct.directSum`
* `TensorProduct.directSumLeft`
* `TensorProduct.directSumRight`
-/

@[expose] public section

universe u v₁ v₂ w₁ w₁' w₂ w₂'

section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type u) [CommSemiring R] (S) [Semiring S] [Algebra R S]
variable {ι₁ : Type v₁} {ι₂ : Type v₂}
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (M₁ : ι₁ → Type w₁) (M₁' : Type w₁') (M₂ : ι₂ → Type w₂) (M₂' : Type w₂')
variable [∀ i₁, AddCommMonoid (M₁ i₁)] [AddCommMonoid M₁']
variable [∀ i₂, AddCommMonoid (M₂ i₂)] [AddCommMonoid M₂']
variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']
variable [∀ i₁, Module S (M₁ i₁)] [∀ i₁, IsScalarTower R S (M₁ i₁)]
variable [Module S M₁'] [IsScalarTower R S M₁']

/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
/-
**TensorProduct.directSum** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u) →   [inst : CommSemiring R] →     (S : Type u_1) →       [ins
t_1 : Semiring S] →         [inst_2 : Algebra R S] →           {ι₁ : Type v₁} → 
            {ι₂ : Type v₂} →               [DecidableEq ι₁] →                 [D
ecidableEq ι₂] →                   (M₁ : ι₁ → Type w₁) →                     (M₂
 : ι₂ → Type w₂) →                       [inst_5 : (i₁ : ι₁) → AddCommMonoid (M₁
 i₁)] →                         [inst_6 : (i₂ : ι₂) → AddCommMonoid (M₂ i₂)] →  
                         [inst_7 : (i₁ : ι₁) → _root_.Module R (M₁ i₁)] →       
                      [inst_8 : (i₂ : ι₂) → _root_.Module R (M₂ i₂)] →          
                     [inst_9 : (i₁ : ι₁) → _root_.Module S (M₁ i₁)] →           
                      [inst_10 : ∀ (i₁ : ι₁), IsScalarTower R S (M₁ i₁)] →      
                             TensorProduct R (DirectSum ι₁ fun i₁ => M₁ i₁) (Dir
ectSum ι₂ fun i₂ => M₂ i₂) ≃ₗ[S]                                     DirectSum (
ι₁ × ι₂) fun i => TensorProduct R (M₁ i.1) (M₂ i.2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ 
i₂)`, i.e.
"tensor product distributes over direct sum".
-/
protected def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[S] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 := by
  refine LinearEquiv.ofLinearMap ?toFun ?invFun ?left ?right
  · exact AlgebraTensorModule.lift <|
      toModule S _ _ fun i₁ => flip <| toModule R _ _ fun i₂ => flip <| AlgebraTensorModule.curry <|
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]

/-- Tensor products distribute over a direct sum on the left . -/
/-
**TensorProduct.directSumLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：directSumLeft : (⨁ i₁, M₁ i₁) otimes[R] M₂' ≃ₗ[S] ⨁ i, M₁ i otimes[R] M₂'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor products distribute over a direct sum on the left .
-/
def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[S] ⨁ i, M₁ i ⊗[R] M₂' :=
  TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit ↦ M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

/-- Tensor products distribute over a direct sum on the right. -/
/-
**TensorProduct.directSumRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：directSumRight : (M₁' otimes[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' otimes[R] M₂ i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Tensor products distribute over a direct sum on the right.
-/
def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit ↦ M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

@[deprecated (since := "2026-03-04")] alias directSumRight' := directSumRight

variable {M₁ M₁' M₂ M₂'}

@[simp]
/-
**TensorProduct.directSum_lof_tmul_lof** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : Ten
sorProduct.directSum R S M₁ M₂ (DirectSum.lof S ι₁ M₁ i₁ m₁ otimesₜ DirectSum.lo
f R ι₂ M₂ i₂ m₂) = DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 otimes[R] M₂ i.2) 
(i₁, i₂) (m₁ otimesₜ m₂)
参数：i₁ : ι₁；m₁ : M₁ i₁；i₂ : ι₂；m₂ : M₂ i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `DirectSum.toModule_lof`：toModule_lof (i) (x : M i) : toModule R ι N φ (l
of R ι M i x) = φ i x
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    TensorProduct.directSum R S M₁ M₂ (DirectSum.lof S ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) := by
  simp [TensorProduct.directSum]

@[simp]
/-
**TensorProduct.directSum_symm_lof_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：directSum_symm_lof_tmul (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : (T
ensorProduct.directSum R S M₁ M₂).symm (DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i
.1 otimes[R] M₂ i.2) (i₁, i₂) (m₁ otimesₜ m₂)) = (DirectSum.lof S ι₁ M₁ i₁ m₁ ot
imesₜ DirectSum.lof R ι₂ M₂ i₂ m₂)
参数：i₁ : ι₁；m₁ : M₁ i₁；i₂ : ι₂；m₂ : M₂ i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `TensorProduct.directSum_lof_tmul_lof`：directSum_lof_tmul_lof (i₁ : ι₁) (
m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : TensorProduct.directSum R S M₁ M₂ (DirectSu
m.lof S ι₁ M₁ i₁ m₁ otimes…
-/
theorem directSum_symm_lof_tmul (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    (TensorProduct.directSum R S M₁ M₂).symm
      (DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂)) =
      (DirectSum.lof S ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) := by
  rw [LinearEquiv.symm_apply_eq, directSum_lof_tmul_lof]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TensorProduct.directSumLeft_tmul_lof** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') : directSumLeft R S M
₁ M₂' (DirectSum.lof S _ _ i x otimesₜ[R] y) = DirectSum.lof S _ _ i (x otimesₜ[
R] y)
参数：i : ι₁；x : M₁ i；y : M₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `DirectSum.lid_symm_apply`：∀ (R : Type u) [inst : Semiring R] {M : Type v
} {ι : Type u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Unique ι]…
· 使用定理 `TensorProduct.directSum_lof_tmul_lof`：directSum_lof_tmul_lof (i₁ : ι₁) (
m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : TensorProduct.directSum R S M₁ M₂ (DirectSu
m.lof S ι₁ M₁ i₁ m₁ otimes…
· 使用引理 `DirectSum.lequivCongrLeft_lof`：lequivCongrLeft_lof [DecidableEq ι] [Deci
dableEq κ] {e : ι ≃ κ} {i : ι} {k : κ} (hik : i = e.symm k) (x : M i) (y : M (e.
symm k)) (hxy : cas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x ⊗ₜ[R] y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumLeft] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
/-
**TensorProduct.directSumLeft_symm_lof_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') : (directSumLeft
 R S M₁ M₂').symm (DirectSum.lof S _ _ i (x otimesₜ[R] y)) = DirectSum.lof S _ _
 i x otimesₜ[R] y
参数：i : ι₁；x : M₁ i；y : M₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `TensorProduct.directSumLeft_tmul_lof`：directSumLeft_tmul_lof (i : ι₁) (x
 : M₁ i) (y : M₂') : directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x otimesₜ[R
] y) = DirectSum.lof S _ _…
-/
theorem directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft R S M₁ M₂').symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof S _ _ i x ⊗ₜ[R] y := by
  rw [LinearEquiv.symm_apply_eq, directSumLeft_tmul_lof]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TensorProduct.directSumLeft_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：directSumLeft_tmul (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁) : directSumLeft R S 
M₁ M₂' (m otimesₜ[R] n) i = (m i) otimesₜ[R] n
参数：m : ⨁ i, M₁ i；n : M₂'；i : ι₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
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
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `TensorProduct.AlgebraTensorModule.mk_apply`：∀ (R : Type uR) [inst : Comm
Semiring R] (A : Type u_1) (M : Type u_2) (N : Type u_3) [inst_1 : Semiring A]  
 [inst_2 : AddCommMonoid M] [ins…
· 使用定理 `TensorProduct.directSumLeft_tmul_lof`：directSumLeft_tmul_lof (i : ι₁) (x
 : M₁ i) (y : M₂') : directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x otimesₜ[R
] y) = DirectSum.lof S _ _…
· 使用定理 `DirectSum.component.lof_self`：∀ (R : Type u) [inst : Semiring R] {ι : Ty
pe v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i :
 ι) → _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DirectSum.component.of`：∀ (R : Type u) [inst : Semiring R] {ι : Type v} 
{M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → 
_root_.Modul…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
lemma directSumLeft_tmul (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁) :
    directSumLeft R S M₁ M₂' (m ⊗ₜ[R] n) i = (m i) ⊗ₜ[R] n := by
  suffices (DirectSum.component S ι₁ _ i) ∘ₗ (directSumLeft R S M₁ M₂').toLinearMap ∘ₗ
      ((AlgebraTensorModule.mk R S (⨁ i, M₁ i) M₂').flip n) =
        ((AlgebraTensorModule.mk R S (M₁ i) M₂').flip n) ∘ₗ (DirectSum.component S ι₁ M₁ i) by
    simpa using! LinearMap.congr_fun this m
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]
/-
**TensorProduct.directSumLeft_symm_of** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：directSumLeft_symm_of {i : ι₁} (x : (M₁ i) otimes[R] M₂') : (directSumLeft
 R S M₁ M₂').symm ((of (fun i => M₁ i otimes[R] M₂') i) x) = rTensor M₂' (lof R 
ι₁ M₁ i) x
参数：x : (M₁ i) otimes[R] M₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instSMulCommClass`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.lof_eq_of`：lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M 
i b
· 使用定理 `TensorProduct.directSumLeft_symm_lof_tmul`：directSumLeft_symm_lof_tmul (
i : ι₁) (x : M₁ i) (y : M₂') : (directSumLeft R S M₁ M₂').symm (DirectSum.lof S 
_ _ i (x otimesₜ[R] y)) = Direc…
· 使用定理 `LinearMap.rTensor_tmul`：rTensor_tmul (m : M) (n : N) : f.rTensor M (n ot
imesₜ m) = f n otimesₜ m
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma directSumLeft_symm_of {i : ι₁} (x : (M₁ i) ⊗[R] M₂') :
    (directSumLeft R S M₁ M₂').symm ((of (fun i ↦ M₁ i ⊗[R] M₂') i) x) =
      rTensor M₂' (lof R ι₁ M₁ i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [← lof_eq_of S, directSumLeft_symm_lof_tmul, rTensor_tmul, lof_eq_of, lof_eq_of]
  | add x y h₁ h₂ => simp [h₁, h₂]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TensorProduct.directSumRight_tmul_lof** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) : directSumRight R S
 M₁' M₂ (x otimesₜ[R] DirectSum.lof R _ _ i y) = DirectSum.lof S _ _ i (x otimes
ₜ[R] y)
参数：x : M₁'；i : ι₂；y : M₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `DirectSum.lid_symm_apply`：∀ (R : Type u) [inst : Semiring R] {M : Type v
} {ι : Type u_1} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Unique ι]…
· 使用定理 `TensorProduct.directSum_lof_tmul_lof`：directSum_lof_tmul_lof (i₁ : ι₁) (
m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) : TensorProduct.directSum R S M₁ M₂ (DirectSu
m.lof S ι₁ M₁ i₁ m₁ otimes…
· 使用引理 `DirectSum.lequivCongrLeft_lof`：lequivCongrLeft_lof [DecidableEq ι] [Deci
dableEq κ] {e : ι ≃ κ} {i : ι} {k : κ} (hik : i = e.symm k) (x : M i) (y : M (e.
symm k)) (hxy : cas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight R S M₁' M₂ (x ⊗ₜ[R] DirectSum.lof R _ _ i y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumRight] using! lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
/-
**TensorProduct.directSumRight_symm_lof_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) : (directSumRig
ht R S M₁' M₂).symm (DirectSum.lof S _ _ i (x otimesₜ[R] y)) = x otimesₜ[R] Dire
ctSum.lof R _ _ i y
参数：x : M₁'；i : ι₂；y : M₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `TensorProduct.directSumRight_tmul_lof`：directSumRight_tmul_lof (x : M₁')
 (i : ι₂) (y : M₂ i) : directSumRight R S M₁' M₂ (x otimesₜ[R] DirectSum.lof R _
 _ i y) = DirectSum.lof S _…
-/
theorem directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight R S M₁' M₂).symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y := by
  rw [LinearEquiv.symm_apply_eq, directSumRight_tmul_lof]
/-
**TensorProduct.directSumRight_comp_rTensor** 是 Mathlib 中的一个引理，位于命名空间 `TensorPro
duct`。
形式化陈述：directSumRight_comp_rTensor (f : M₁' ->ₗ[R] M₂') : (directSumRight R R M₂'
 M₁).toLinearMap ∘ₗ f.rTensor _ = (lmap fun _ => f.rTensor _) ∘ₗ directSumRight 
R R M₁' M₁
参数：f : M₁' ->ₗ[R] M₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `TensorProduct.directSumRight_tmul_lof`：directSumRight_tmul_lof (x : M₁')
 (i : ι₂) (y : M₂ i) : directSumRight R S M₁' M₂ (x otimesₜ[R] DirectSum.lof R _
 _ i y) = DirectSum.lof S _…
· 使用定理 `DirectSum.lmap_lof`：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M :
 ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _roo
t_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma directSumRight_comp_rTensor (f : M₁' →ₗ[R] M₂') :
    (directSumRight R R M₂' M₁).toLinearMap ∘ₗ f.rTensor _ =
      (lmap fun _ ↦ f.rTensor _) ∘ₗ directSumRight R R M₁' M₁ := by
  ext; simp

@[simp]
/-
**TensorProduct.directSumRight_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：directSumRight_tmul (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂) : directSumRight R 
S M₁' M₂ (m otimesₜ[R] n) i = m otimesₜ[R] (n i)
参数：m : M₁'；n : ⨁ i, M₂ i；i : ι₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.directSumRight_tmul_lof`：directSumRight_tmul_lof (x : M₁')
 (i : ι₂) (y : M₂ i) : directSumRight R S M₁' M₂ (x otimesₜ[R] DirectSum.lof R _
 _ i y) = DirectSum.lof S _…
· 使用定理 `DirectSum.component.lof_self`：∀ (R : Type u) [inst : Semiring R] {ι : Ty
pe v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i :
 ι) → _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DirectSum.component.of`：∀ (R : Type u) [inst : Semiring R] {ι : Type v} 
{M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → 
_root_.Modul…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
lemma directSumRight_tmul (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂) :
    directSumRight R S M₁' M₂ (m ⊗ₜ[R] n) i = m ⊗ₜ[R] (n i) := by
  suffices (DirectSum.component S ι₂ _ i).restrictScalars R ∘ₗ
      (directSumRight R S M₁' M₂).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk R M₁' (⨁ i, M₂ i) m) =
          (TensorProduct.mk R M₁' (M₂ i) m) ∘ₗ (DirectSum.component R ι₂ M₂ i) by
    simpa using! LinearMap.congr_fun this n
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

variable (S₀ : Type*) [CommSemiring S₀] [Algebra R S₀] [Algebra S₀ S]
  [Module S₀ M₁'] [IsScalarTower R S₀ M₁'] [IsScalarTower S₀ S M₁']

set_option backward.isDefEq.respectTransparency false in
/-
**TensorProduct.restrictScalar_directSumRight** 是 Mathlib 中的一个引理，位于命名空间 `TensorP
roduct`。
形式化陈述：restrictScalar_directSumRight : (directSumRight R S M₁' M₂).restrictScalar
s S₀ = directSumRight R S₀ M₁' M₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.restrictScalars_injective`：restrictScalars_injective : Funct
ion.Injective (restrictScalars R : (M ≃ₗ[S] M₂) -> M ≃ₗ[R] M₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.restrictScalars.congr_simp`：∀ (R : Type u_1) {S : Type u_5} {M
 : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_
2 : AddCommMonoid M] [inst…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `TensorProduct.directSumRight_tmul`：directSumRight_tmul (m : M₁') (n : ⨁ 
i, M₂ i) (i : ι₂) : directSumRight R S M₁' M₂ (m otimesₜ[R] n) i = m otimesₜ[R] 
(n i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrictScalar_directSumRight :
    (directSumRight R S M₁' M₂).restrictScalars S₀ = directSumRight R S₀ M₁' M₂ :=
  LinearEquiv.restrictScalars_injective R <| LinearEquiv.toLinearMap_injective <| by ext; simp [lof]

@[deprecated (since := "2026-03-04")]
alias directSumRight'_restrict := restrictScalar_directSumRight
/-
**TensorProduct.coe_directSumRight** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：coe_directSumRight : ⇑(directSumRight R S M₁' M₂) = directSumRight R R M₁'
 M₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `DirectSum.instIsScalarTower`：∀ {R : Type u} [inst : Semiring R] {ι : Typ
e v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : 
ι) → _root_.Modul…
· 使用引理 `TensorProduct.restrictScalar_directSumRight`：restrictScalar_directSumRig
ht : (directSumRight R S M₁' M₂).restrictScalars S₀ = directSumRight R S₀ M₁' M₂
-/
lemma coe_directSumRight :
    ⇑(directSumRight R S M₁' M₂) = directSumRight R R M₁' M₂ :=
  congr($(restrictScalar_directSumRight ..))

@[deprecated (since := "2026-03-04")] alias coe_directSumRight' := coe_directSumRight

end TensorProduct

end Ring

