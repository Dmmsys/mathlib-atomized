/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Linear equivalences of tensor products as isometries

These results are separate from the definition of `QuadraticForm.tmul` as that file is very slow.

## Main definitions

* `QuadraticForm.Isometry.tmul`: `TensorProduct.map` as a `QuadraticForm.Isometry`
* `QuadraticForm.tensorComm`: `TensorProduct.comm` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorAssoc`: `TensorProduct.assoc` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorRId`: `TensorProduct.rid` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorLId`: `TensorProduct.lid` as a `QuadraticForm.IsometryEquiv`
-/

@[expose] public section

universe uR uM₁ uM₂ uM₃ uM₄
variable {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} {M₄ : Type uM₄}

open scoped TensorProduct

open QuadraticMap

namespace QuadraticForm

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Invertible (2 : R)]

@[simp]
/-
**QuadraticForm.tmul_comp_tensorMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_comp_tensorMap {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q
₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄} (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ 
Q₄) : (Q₂.tmul Q₄).comp (TensorProduct.map f.toLinearMap g.toLinearMap) = Q₁.tmu
l Q₃
参数：f : Q₁ ->qᵢ Q₂；g : Q₃ ->qᵢ Q₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.Isometry.map_app`：map_app (f : Q₁ ->qᵢ Q₂) (m : M₁) : Q₂ (f
 m) = Q₁ m
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_rightInverse`：associated_rightInverse : Function
.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ -> QuadraticMap R M
 N)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
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
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `QuadraticForm.tmul.congr_simp`：∀ {R : Type uR} {A : Type uA} {M₁ : Type 
uM₁} {M₂ : Type uM₂} [inst : CommRing R] [inst_1 : CommRing A]   [inst_2 : AddCo
mmGroup M₁] [inst_3…
· 使用定理 `LinearMap.BilinForm.tmul.congr_simp`：∀ {R : Type uR} {A : Type uA} {M₁ :
 Type uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [
inst_2 : AddCommMonoid M₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tmul_comp_tensorMap
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) :
    (Q₂.tmul Q₄).comp (TensorProduct.map f.toLinearMap g.toLinearMap) = Q₁.tmul Q₃ := by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [h₁, h₃, associated_tmul]

@[simp]
/-
**QuadraticForm.tmul_tensorMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_tensorMap_apply {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {
Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄} (f : Q₁ ->qᵢ Q₂) (g : Q₃ ->qᵢ
 Q₄) (x : M₁ otimes[R] M₃) : Q₂.tmul Q₄ (TensorProduct.map f.toLinearMap g.toLin
earMap x) = Q₁.tmul Q₃ x
参数：f : Q₁ ->qᵢ Q₂；g : Q₃ ->qᵢ Q₄；x : M₁ otimes[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `QuadraticForm.tmul_comp_tensorMap`：tmul_comp_tensorMap {Q₁ : QuadraticFo
rm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm
 R M₄} (f : Q₁ ->qᵢ Q₂)…
-/
theorem tmul_tensorMap_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) (x : M₁ ⊗[R] M₃) :
    Q₂.tmul Q₄ (TensorProduct.map f.toLinearMap g.toLinearMap x) = Q₁.tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorMap f g) x

namespace Isometry

/-- `TensorProduct.map` for `QuadraticForm.Isometry`s -/
/-
**QuadraticForm.Isometry._root_.QuadraticMap.Isometry.tmul** 是 Mathlib 中的一个定义，位于
命名空间 `QuadraticForm.Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TensorProduct.map` for `QuadraticForm.Isometry`s
-/
def _root_.QuadraticMap.Isometry.tmul
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) : (Q₁.tmul Q₃) →qᵢ (Q₂.tmul Q₄) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

@[simp]
/-
**QuadraticForm.Isometry._root_.QuadraticMap.Isometry.tmul_apply** 是 Mathlib 中的一
个定理，位于命名空间 `QuadraticForm.Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuadraticMap.Isometry.tmul_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) (x : M₁ ⊗[R] M₃) :
    f.tmul g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

end Isometry

section tensorComm

@[simp]
/-
**QuadraticForm.tmul_comp_tensorComm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
 (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_rightInverse`：associated_rightInverse : Function
.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ -> QuadraticMap R M
 N)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]
/-
**QuadraticForm.tmul_tensorComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_tensorComm_apply (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) 
(x : M₁ otimes[R] M₂) : Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；x : M₁ otimes[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `QuadraticForm.tmul_comp_tensorComm`：tmul_comp_tensorComm (Q₁ : Quadratic
Form R M₁) (Q₂ : QuadraticForm R M₂) : (Q₂.tmul Q₁).comp (TensorProduct.comm R M
₁ M₂) = Q₁.tmul Q₂
-/
theorem tmul_tensorComm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ ⊗[R] M₂) :
    Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x :=
  DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

/-- `TensorProduct.comm` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/-
**QuadraticForm.tensorComm** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul 
Q₂).IsometryEquiv (Q₂.tmul Q₁) where toLinearEquiv
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticForm.tmul_tensorComm_apply`：tmul_tensorComm_apply (Q₁ : Quadrat
icForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ otimes[R] M₂) : Q₂.tmul Q₁ (Tenso
rProduct.comm R M₁ M₂ x) …

--- 原说明 ---
`TensorProduct.comm` preserves tensor products of quadratic forms.
-/
def tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).IsometryEquiv (Q₂.tmul Q₁) where
  toLinearEquiv := TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂
/-
**QuadraticForm.tensorComm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} [inst : CommRing R] [inst_
1 : AddCommGroup M₁]   [inst_2 : AddCommGroup M₂] [inst_3 : _root_.Module R M₁] 
[inst_4 : _root_.Module R M₂] [inst_5 : Invertible 2]   (Q₁ : QuadraticForm R M₁
) (Q₂ : QuadraticForm R M₂) (x : TensorProduct R M₁ M₂),   (Q₁.tensorComm Q₂) x 
= (TensorProduct.comm R M₁ M₂) x
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；x : TensorProduct R M₁ M₂；Q₁.
tensorComm Q₂；TensorProduct.comm R M₁ M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma tensorComm_apply (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (x : M₁ ⊗[R] M₂) :
    tensorComm Q₁ Q₂ x = TensorProduct.comm R M₁ M₂ x :=
  rfl
/-
**QuadraticForm.tensorComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} [inst : CommRing R] [inst_
1 : AddCommGroup M₁]   [inst_2 : AddCommGroup M₂] [inst_3 : _root_.Module R M₁] 
[inst_4 : _root_.Module R M₂] [inst_5 : Invertible 2]   (Q₁ : QuadraticForm R M₁
) (Q₂ : QuadraticForm R M₂), (Q₁.tensorComm Q₂).symm = Q₂.tensorComm Q₁
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₁.tensorComm Q₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma tensorComm_symm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (tensorComm Q₁ Q₂).symm = tensorComm Q₂ Q₁ :=
  rfl

end tensorComm

section tensorAssoc

@[simp]
/-
**QuadraticForm.tmul_comp_tensorAssoc** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_comp_tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) 
(Q₃ : QuadraticForm R M₃) : (Q₁.tmul (Q₂.tmul Q₃)).comp (TensorProduct.assoc R M
₁ M₂ M₃) = (Q₁.tmul Q₂).tmul Q₃
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₃ : QuadraticForm R M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_rightInverse`：associated_rightInverse : Function
.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ -> QuadraticMap R M
 N)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用定理 `LinearMap.BilinForm.tmul.congr_simp`：∀ {R : Type uR} {A : Type uA} {M₁ :
 Type uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [
inst_2 : AddCommMonoid M₁…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem tmul_comp_tensorAssoc
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    (Q₁.tmul (Q₂.tmul Q₃)).comp (TensorProduct.assoc R M₁ M₂ M₃) = (Q₁.tmul Q₂).tmul Q₃ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]
/-
**QuadraticForm.tmul_tensorAssoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`
。
形式化陈述：tmul_tensorAssoc_apply (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
 (Q₃ : QuadraticForm R M₃) (x : (M₁ otimes[R] M₂) otimes[R] M₃) : Q₁.tmul (Q₂.tm
ul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₃ : QuadraticForm R M₃；x : (
M₁ otimes[R] M₂) otimes[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `QuadraticForm.tmul_comp_tensorAssoc`：tmul_comp_tensorAssoc (Q₁ : Quadrat
icForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) : (Q₁.tmul (Q₂.
tmul Q₃)).comp (TensorPro…
-/
theorem tmul_tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    Q₁.tmul (Q₂.tmul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

/-- `TensorProduct.assoc` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/-
**QuadraticForm.tensorAssoc** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : Quad
raticForm R M₃) : ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) wh
ere toLinearEquiv
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₃ : QuadraticForm R M₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticForm.tmul_tensorAssoc_apply`：tmul_tensorAssoc_apply (Q₁ : Quadr
aticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) (x : (M₁ otim
es[R] M₂) otimes[R] M₃) : …

--- 原说明 ---
`TensorProduct.assoc` preserves tensor products of quadratic forms.
-/
def tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) where
  toLinearEquiv := TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃
/-
**QuadraticForm.tensorAssoc_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} [inst : Co
mmRing R] [inst_1 : AddCommGroup M₁]   [inst_2 : AddCommGroup M₂] [inst_3 : AddC
ommGroup M₃] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]   [inst
_6 : _root_.Module R M₃] [inst_7 : Invertible 2] (Q₁ : QuadraticForm R M₁) (Q₂ :
 QuadraticForm R M₂)   (Q₃ : QuadraticForm R M₃) (x : TensorProduct R (TensorPro
duct R M₁ M₂) M₃),   (Q₁.tensorAssoc Q₂ Q₃) x = (TensorProduct.assoc R M₁ M₂ M₃)
 x
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₃ : QuadraticForm R M₃；x : T
ensorProduct R (TensorProduct R M₁ M₂) M₃；Q₁.tensorAssoc Q₂ Q₃；TensorProduct.ass
oc R M₁ M₂ M₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    tensorAssoc Q₁ Q₂ Q₃ x = TensorProduct.assoc R M₁ M₂ M₃ x :=
  rfl
/-
**QuadraticForm.tensorAssoc_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`
。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} [inst : Co
mmRing R] [inst_1 : AddCommGroup M₁]   [inst_2 : AddCommGroup M₂] [inst_3 : AddC
ommGroup M₃] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]   [inst
_6 : _root_.Module R M₃] [inst_7 : Invertible 2] (Q₁ : QuadraticForm R M₁) (Q₂ :
 QuadraticForm R M₂)   (Q₃ : QuadraticForm R M₃) (x : TensorProduct R M₁ (Tensor
Product R M₂ M₃)),   (Q₁.tensorAssoc Q₂ Q₃).symm x = (TensorProduct.assoc R M₁ M
₂ M₃).symm x
参数：Q₁ : QuadraticForm R M₁；Q₂ : QuadraticForm R M₂；Q₃ : QuadraticForm R M₃；x : T
ensorProduct R M₁ (TensorProduct R M₂ M₃)；Q₁.tensorAssoc Q₂ Q₃；TensorProduct.ass
oc R M₁ M₂ M₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] lemma tensorAssoc_symm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (tensorAssoc Q₁ Q₂ Q₃).symm x = (TensorProduct.assoc R M₁ M₂ M₃).symm x :=
  rfl

end tensorAssoc

section tensorRId

/-
**QuadraticForm.comp_tensorRId_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：comp_tensorRId_eq (Q₁ : QuadraticForm R M₁) : Q₁.comp (TensorProduct.rid R
 M₁) = Q₁.tmul (sq (R
参数：Q₁ : QuadraticForm R M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_rightInverse`：associated_rightInverse : Function
.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ -> QuadraticMap R M
 N)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
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
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `QuadraticForm.associated_tmul`：associated_tmul [Invertible (2 : A)] (Q₁ 
: QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) : (Q₁.tmul Q₂).associated = Bili
nForm.tmul Q₁.assoc…
· 使用定理 `LinearMap.BilinForm.tmul.congr_simp`：∀ {R : Type uR} {A : Type uA} {M₁ :
 Type uM₁} {M₂ : Type uM₂} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [
inst_2 : AddCommMonoid M₁…
· 使用引理 `QuadraticMap.associated_sq`：associated_sq [Invertible (2 : R)] : associa
ted (R
· 使用定理 `LinearMap.mul_apply_apply`：∀ (R : Type u_1) (A : Type u_2) [inst : CommS
emiring R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A]
 [inst_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_tensorRId_eq (Q₁ : QuadraticForm R M₁) :
    Q₁.comp (TensorProduct.rid R M₁) = Q₁.tmul (sq (R := R)) := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  simp [associated_tmul, QuadraticMap.associated_comp, one_mul]

@[simp]
/-
**QuadraticForm.tmul_tensorRId_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_tensorRId_apply (Q₁ : QuadraticForm R M₁) (x : M₁ otimes[R] R) : Q₁ (
TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R
参数：Q₁ : QuadraticForm R M₁；x : M₁ otimes[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `QuadraticForm.comp_tensorRId_eq`：comp_tensorRId_eq (Q₁ : QuadraticForm R
 M₁) : Q₁.comp (TensorProduct.rid R M₁) = Q₁.tmul (sq (R
-/
theorem tmul_tensorRId_apply
    (Q₁ : QuadraticForm R M₁) (x : M₁ ⊗[R] R) :
    Q₁ (TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R := R)) x :=
  DFunLike.congr_fun (comp_tensorRId_eq Q₁) x

/-- `TensorProduct.rid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/-
**QuadraticForm.tensorRId** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：tensorRId (Q₁ : QuadraticForm R M₁) : (Q₁.tmul (sq (R
参数：Q₁ : QuadraticForm R M₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticForm.tmul_tensorRId_apply`：tmul_tensorRId_apply (Q₁ : Quadratic
Form R M₁) (x : M₁ otimes[R] R) : Q₁ (TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R

--- 原说明 ---
`TensorProduct.rid` preserves tensor products of quadratic forms.
-/
def tensorRId (Q₁ : QuadraticForm R M₁) :
    (Q₁.tmul (sq (R := R))).IsometryEquiv Q₁ where
  toLinearEquiv := TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁
/-
**QuadraticForm.tensorRId_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} [inst : CommRing R] [inst_1 : AddCommGroup
 M₁] [inst_2 : _root_.Module R M₁]   [inst_3 : Invertible 2] (Q₁ : QuadraticForm
 R M₁) (x : TensorProduct R M₁ R),   Q₁.tensorRId x = (TensorProduct.rid R M₁) x
参数：Q₁ : QuadraticForm R M₁；x : TensorProduct R M₁ R；TensorProduct.rid R M₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma tensorRId_apply (Q₁ : QuadraticForm R M₁) (x : M₁ ⊗[R] R) :
    tensorRId Q₁ x = TensorProduct.rid R M₁ x :=
  rfl
/-
**QuadraticForm.tensorRId_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₁ : Type uM₁} [inst : CommRing R] [inst_1 : AddCommGroup
 M₁] [inst_2 : _root_.Module R M₁]   [inst_3 : Invertible 2] (Q₁ : QuadraticForm
 R M₁) (x : M₁), Q₁.tensorRId.symm x = (TensorProduct.rid R M₁).symm x
参数：Q₁ : QuadraticForm R M₁；x : M₁；TensorProduct.rid R M₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma tensorRId_symm_apply (Q₁ : QuadraticForm R M₁) (x : M₁) :
    (tensorRId Q₁).symm x = (TensorProduct.rid R M₁).symm x :=
  rfl

end tensorRId

section tensorLId

/-
**QuadraticForm.comp_tensorLId_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：comp_tensorLId_eq (Q₂ : QuadraticForm R M₂) : Q₂.comp (TensorProduct.lid R
 M₂) = QuadraticForm.tmul (sq (R
参数：Q₂ : QuadraticForm R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `baseChange_ext`：baseChange_ext ⦃Q₁ Q₂ : QuadraticMap A (A otimes[R] M₂) 
N₁⦄ (h : forall m, Q₁ (1 otimesₜ m) = Q₂ (1 otimesₜ m)) : Q₁ = Q₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `QuadraticMap.instSMulCommClass`：∀ {S : Type u_1} {T : Type u_2} {R : Typ
e u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R]   [inst_1 : AddComm
Monoid M] [inst_2 : …
· 使用定理 `QuadraticForm.tensorDistrib_tmul`：tensorDistrib_tmul (Q₁ : QuadraticForm
 A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) : tensorDistrib R A (Q₁ oti
mesₜ Q₂) (m₁ otimesₜ m…
· 使用定理 `QuadraticMap.sq_apply`：∀ {R : Type u_3} {A : Type u_7} [inst : CommSemir
ing R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [in
st_3 : SMul…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_tensorLId_eq (Q₂ : QuadraticForm R M₂) :
    Q₂.comp (TensorProduct.lid R M₂) = QuadraticForm.tmul (sq (R := R)) Q₂ := by
  ext
  simp

@[simp]
/-
**QuadraticForm.tmul_tensorLId_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：tmul_tensorLId_apply (Q₂ : QuadraticForm R M₂) (x : R otimes[R] M₂) : Q₂ (
TensorProduct.lid R M₂ x) = QuadraticForm.tmul (sq (R
参数：Q₂ : QuadraticForm R M₂；x : R otimes[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `QuadraticForm.comp_tensorLId_eq`：comp_tensorLId_eq (Q₂ : QuadraticForm R
 M₂) : Q₂.comp (TensorProduct.lid R M₂) = QuadraticForm.tmul (sq (R
-/
theorem tmul_tensorLId_apply
    (Q₂ : QuadraticForm R M₂) (x : R ⊗[R] M₂) :
    Q₂ (TensorProduct.lid R M₂ x) = QuadraticForm.tmul (sq (R := R)) Q₂ x :=
  DFunLike.congr_fun (comp_tensorLId_eq Q₂) x

/-- `TensorProduct.lid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
/-
**QuadraticForm.tensorLId** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：tensorLId (Q₂ : QuadraticForm R M₂) : (QuadraticForm.tmul (sq (R
参数：Q₂ : QuadraticForm R M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticForm.tmul_tensorLId_apply`：tmul_tensorLId_apply (Q₂ : Quadratic
Form R M₂) (x : R otimes[R] M₂) : Q₂ (TensorProduct.lid R M₂ x) = QuadraticForm.
tmul (sq (R

--- 原说明 ---
`TensorProduct.lid` preserves tensor products of quadratic forms.
-/
def tensorLId (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.tmul (sq (R := R)) Q₂).IsometryEquiv Q₂ where
  toLinearEquiv := TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂
/-
**QuadraticForm.tensorLId_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₂ : Type uM₂} [inst : CommRing R] [inst_1 : AddCommGroup
 M₂] [inst_2 : _root_.Module R M₂]   [inst_3 : Invertible 2] (Q₂ : QuadraticForm
 R M₂) (x : TensorProduct R R M₂),   Q₂.tensorLId x = (TensorProduct.lid R M₂) x
参数：Q₂ : QuadraticForm R M₂；x : TensorProduct R R M₂；TensorProduct.lid R M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma tensorLId_apply (Q₂ : QuadraticForm R M₂) (x : R ⊗[R] M₂) :
    tensorLId Q₂ x = TensorProduct.lid R M₂ x :=
  rfl
/-
**QuadraticForm.tensorLId_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type uR} {M₂ : Type uM₂} [inst : CommRing R] [inst_1 : AddCommGroup
 M₂] [inst_2 : _root_.Module R M₂]   [inst_3 : Invertible 2] (Q₂ : QuadraticForm
 R M₂) (x : M₂), Q₂.tensorLId.symm x = (TensorProduct.lid R M₂).symm x
参数：Q₂ : QuadraticForm R M₂；x : M₂；TensorProduct.lid R M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
@[simp] lemma tensorLId_symm_apply (Q₂ : QuadraticForm R M₂) (x : M₂) :
    (tensorLId Q₂).symm x = (TensorProduct.lid R M₂).symm x :=
  rfl

end tensorLId

end QuadraticForm

