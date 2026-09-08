/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definition

- `Module.Invertible R M` says that the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism.
  To show that `M` is invertible, it suffices to provide an arbitrary `R`-module `N`
  and an isomorphism `N ⊗[R] M ≃ₗ[R] R`, see `Module.Invertible.right`.

- `ClassGroup.equivPic`: the class group of a domain is isomorphic to the Picard group.

## Main results

- An invertible module is finite and projective (provided as instances).

- `Module.Invertible.free_iff_linearEquiv`: an invertible module is free iff it is isomorphic to
  the ring, i.e. its class is trivial in the Picard group.

- `Submodule.ker_unitsToPic`, `Submodule.range_unitsToPic`: exactness of the sequence
  `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at the last two spots.
  See Theorem 2.4 in [RobertsSingh1993] or Exercise I.3.7(iv) and Proposition I.3.5 in [Weibel2013].

## References

- https://qchu.wordpress.com/2014/10/19/the-picard-groups/
- https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
- https://mathoverflow.net/questions/375725/picard-group-vs-class-group
- [Weibel2013], https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf
- [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

Show:
- Invertible modules over a commutative ring have the same cardinality as the ring.

- Establish other characterizations of invertible modules, e.g. they are modules that
  become free of rank one when localized at every prime ideal.
  See [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX).
- Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
  constant finite rank to locally free sheaves on `Spec R`.
- Exhibit isomorphism with sheaf cohomology `H¹(Spec R, 𝓞ˣ)`.
-/

@[expose] public section

open TensorProduct

universe u v

variable (R : Type u) (M : Type v) (N P Q A : Type*) [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace Module

/-- An `R`-module `M` is invertible if the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism,
where `Mᵛ` is the `R`-dual of `M`. -/
/-
**Module.Invertible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → (M : Type v) → [inst : CommSemiring R] → [inst_1 : AddCommM
onoid M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` is invertible if the canonical map `Mᵛ ⊗[R] M → R` is an isomo
rphism,
where `Mᵛ` is the `R`-dual of `M`.
-/
protected class Invertible : Prop where
  bijective : Function.Bijective (contractLeft R M)

namespace Invertible

/-- Promote the canonical map `Mᵛ ⊗[R] M → R` to a linear equivalence for invertible `M`. -/
/-
**Module.Invertible.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Invertible`。
形式化陈述：linearEquiv [Module.Invertible R M] : Module.Dual R M otimes[R] M ≃ₗ[R] R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.bijective`：∀ {R : Type u} {M : Type v} {inst : CommSem
iring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Modul
e.Invertible R M]…

--- 原说明 ---
Promote the canonical map `Mᵛ ⊗[R] M → R` to a linear equivalence for invertible
 `M`.
-/
noncomputable def linearEquiv [Module.Invertible R M] : Module.Dual R M ⊗[R] M ≃ₗ[R] R :=
  .ofBijective _ Invertible.bijective

variable {R M N}

section LinearEquiv

variable (e : M ⊗[R] N ≃ₗ[R] R)

/-- The canonical isomorphism between a module and the result of tensoring it
from the left by two mutually dual invertible modules. -/
/-
**Module.Invertible.leftCancelEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.Invertib
le`。
形式化陈述：leftCancelEquiv : M otimes[R] (N otimes[R] P) ≃ₗ[R] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between a module and the result of tensoring it
from the left by two mutually dual invertible modules.
-/
noncomputable abbrev leftCancelEquiv : M ⊗[R] (N ⊗[R] P) ≃ₗ[R] P :=
  (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

/-- The canonical isomorphism between a module and the result of tensoring it
from the right by two mutually dual invertible modules. -/
/-
**Module.Invertible.rightCancelEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.Inverti
ble`。
形式化陈述：rightCancelEquiv : (P otimes[R] M) otimes[R] N ≃ₗ[R] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between a module and the result of tensoring it
from the right by two mutually dual invertible modules.
-/
noncomputable abbrev rightCancelEquiv : (P ⊗[R] M) ⊗[R] N ≃ₗ[R] P :=
  TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

variable {P Q} in
/-
**Module.Invertible.leftCancelEquiv_comp_lTensor_comp_symm** 是 Mathlib 中的一个定理，位于
命名空间 `Module.Invertible`。
形式化陈述：leftCancelEquiv_comp_lTensor_comp_symm (f : P ->ₗ[R] Q) : leftCancelEquiv 
Q e ∘ₗ (f.lTensor N).lTensor M ∘ₗ (leftCancelEquiv P e).symm = f
参数：f : P ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftCancelEquiv_comp_lTensor_comp_symm (f : P →ₗ[R] Q) :
    leftCancelEquiv Q e ∘ₗ (f.lTensor N).lTensor M ∘ₗ (leftCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

variable {P Q} in
/-
**Module.Invertible.rightCancelEquiv_comp_rTensor_comp_symm** 是 Mathlib 中的一个定理，位
于命名空间 `Module.Invertible`。
形式化陈述：rightCancelEquiv_comp_rTensor_comp_symm (f : P ->ₗ[R] Q) : rightCancelEqui
v Q e ∘ₗ (f.rTensor M).rTensor N ∘ₗ (rightCancelEquiv P e).symm = f
参数：f : P ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightCancelEquiv_comp_rTensor_comp_symm (f : P →ₗ[R] Q) :
    rightCancelEquiv Q e ∘ₗ (f.rTensor M).rTensor N ∘ₗ (rightCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

/-- If M is invertible, `rTensorHom M` admits an inverse. -/
/-
**Module.Invertible.rTensorInv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Invertible`。
形式化陈述：rTensorInv : (P otimes[R] M ->ₗ[R] Q otimes[R] M) ->ₗ[R] (P ->ₗ[R] Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If M is invertible, `rTensorHom M` admits an inverse.
-/
noncomputable def rTensorInv : (P ⊗[R] M →ₗ[R] Q ⊗[R] M) →ₗ[R] (P →ₗ[R] Q) :=
  ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.Invertible.rTensorInv_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inv
ertible`。
形式化陈述：rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensor
Hom M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M) :=
  fun _ ↦ by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
/-
**Module.Invertible.rTensorInv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inver
tible`。
形式化陈述：rTensorInv_injective : Function.Injective (rTensorInv P Q e)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Module.Invertible.rTensorInv_leftInverse`：rTensorInv_leftInverse : Funct
ion.LeftInverse (rTensorInv P Q e) (.rTensorHom M)
-/
theorem rTensorInv_injective : Function.Injective (rTensorInv P Q e) := by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

/-- If `M` is an invertible `R`-module, `(· ⊗[R] M)` is an auto-equivalence of the category
of `R`-modules. -/
/-
**Module.Invertible.rTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Invertible`。
形式化陈述：{R : Type u} →   {M : Type v} →     {N : Type u_1} →       (P : Type u_2) 
→         (Q : Type u_3) →           [inst : CommSemiring R] →             [inst
_1 : AddCommMonoid M] →               [inst_2 : AddCommMonoid N] →              
   [inst_3 : AddCommMonoid P] →                   [inst_4 : AddCommMonoid Q] →  
                   [inst_5 : _root_.Module R M] →                       [inst_6 
: _root_.Module R N] →                         [inst_7 : _root_.Module R P] →   
                        [inst_8 : _root_.Module R Q] →                          
   (TensorProduct R M N ≃ₗ[R] R) →                               (P →ₗ[R] Q) ≃ₗ[
R] TensorProduct R P M →ₗ[R] TensorProduct R Q M
参数：P : Type u_2；Q : Type u_3；TensorProduct R M N ≃ₗ[R] R；P →ₗ[R] Q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.rTensorInv_leftInverse`：rTensorInv_leftInverse : Funct
ion.LeftInverse (rTensorInv P Q e) (.rTensorHom M)

--- 原说明 ---
If `M` is an invertible `R`-module, `(· ⊗[R] M)` is an auto-equivalence of the c
ategory
of `R`-modules.
-/
@[simps!] noncomputable def rTensorEquiv : (P →ₗ[R] Q) ≃ₗ[R] (P ⊗[R] M →ₗ[R] Q ⊗[R] M) where
  __ := LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e (by rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse])

set_option backward.isDefEq.respectTransparency.types false in
open LinearMap in
/-- If there is an `R`-isomorphism between `M ⊗[R] N` and `R`,
the induced map `M → Nᵛ` is an isomorphism. -/
/-
**Module.Invertible.bijective_curry** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible
`。
形式化陈述：bijective_curry : Function.Bijective (curry e.toLinearMap)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If there is an `R`-isomorphism between `M ⊗[R] N` and `R`,
the induced map `M → Nᵛ` is an isomorphism.
-/
theorem bijective_curry : Function.Bijective (curry e.toLinearMap) := by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
  simpa [this] using! (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

/-- Given `M ⊗[R] N ≃ₗ[R] R`, this is the induced isomorphism `M ≃ₗ[R] Nᵛ`. -/
/-
**Module.Invertible.linearEquivDual** 是 Mathlib 中的一个定义，位于命名空间 `Module.Invertible
`。
形式化陈述：linearEquivDual : M ≃ₗ[R] Dual R N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.bijective_curry`：bijective_curry : Function.Bijective 
(curry e.toLinearMap)

--- 原说明 ---
Given `M ⊗[R] N ≃ₗ[R] R`, this is the induced isomorphism `M ≃ₗ[R] Nᵛ`.
-/
noncomputable def linearEquivDual : M ≃ₗ[R] Dual R N := .ofBijective _ (bijective_curry e)

include e
/-
**Module.Invertible.right** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] (e : TensorProduct R M N ≃ₗ[R] R), Module.Invertible 
R N
参数：e : TensorProduct R M N ≃ₗ[R] R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_symm`：eq_comp_toLinearMap_symm (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁
₂.toLinearMap = g
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
protected theorem right : Module.Invertible R N where
  bijective := by
    rw [show contractLeft R N = ((linearEquivDual e).rTensor N).symm ≪≫ₗ e by
      rw [LinearEquiv.coe_trans, LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl]
    apply LinearEquiv.bijective
/-
**Module.Invertible.left** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] (e : TensorProduct R M N ≃ₗ[R] R), Module.Invertible 
R M
参数：e : TensorProduct R M N ≃ₗ[R] R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.right`：∀ {R : Type u} {M : Type v} {N : Type u_1} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [ins
t_3 : _root_.…
-/
protected theorem left : Module.Invertible R M := .right (TensorProduct.comm R N M ≪≫ₗ e)
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Invertible R R := .left (TensorProduct.lid R R)

end LinearEquiv

variable [Module.Invertible R M]

/-
**Module.Invertible.congr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] [Module.Invertible R M] (e : M ≃ₗ[R] N),   Module.Inv
ertible R N
参数：e : M ≃ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.right`：∀ {R : Type u} {M : Type v} {N : Type u_1} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [ins
t_3 : _root_.…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
protected theorem congr (e : M ≃ₗ[R] N) : Module.Invertible R N :=
  .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)

variable (R M N)
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Invertible R (Dual R M) := .left (linearEquiv R M)
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Invertible R N] : Module.Invertible R (M ⊗[R] N) :=
  .right (M := Dual R M ⊗[R] Dual R N) <| tensorTensorTensorComm .. ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R
/-
**Module.Invertible.finite_projective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertib
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem finite_projective : Module.Finite R M ∧ Projective R M := by
  let N := Dual R M
  let e : M ⊗[R] N ≃ₗ[R] R := TensorProduct.comm .. ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S →₀ N) →ₗ[R] R := Finsupp.lsum R fun i ↦ e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Ideal.eq_top_iff_one]
    use Finsupp.equivFunOnFinite.symm fun i ↦ i.1.2
    simp_rw [f, Finsupp.coe_lsum]
    rw [Finsupp.sum_fintype _ _ fun _ ↦ map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R _ M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S →₀ R) →ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M →ₗ[R] S →₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
  refine ⟨.of_surjective f' this, .of_split g' f' <| LinearMap.ext fun m ↦ ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R M := (finite_projective R M).1
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Projective R M := (finite_projective R M).2
/-
**Module.Invertible.** 是 Mathlib 中的一个示例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsReflexive R M := inferInstance

section inj_surj_bij

variable {R N P}

/-
**Module.Invertible.lTensor_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inve
rtible`。
形式化陈述：lTensor_injective_iff {f : N ->ₗ[R] P} : Function.Injective (f.lTensor M) 
↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Invertible.leftCancelEquiv_comp_lTensor_comp_symm`：leftCancelEqui
v_comp_lTensor_comp_symm (f : P ->ₗ[R] Q) : leftCancelEquiv Q e ∘ₗ (f.lTensor N)
.lTensor M ∘ₗ (leftCancelEquiv P e).symm = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `Module.Invertible.instProjective`：∀ (R : Type u) (M : Type v) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.
Invertible R M], Modul…
-/
theorem lTensor_injective_iff {f : N →ₗ[R] P} :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  refine ⟨fun h ↦ ?_, Flat.lTensor_preserves_injective_linearMap _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using Flat.lTensor_preserves_injective_linearMap _ h
/-
**Module.Invertible.rTensor_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inve
rtible`。
形式化陈述：rTensor_injective_iff {f : N ->ₗ[R] P} : Function.Injective (f.rTensor M) 
↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_inj_iff_rTensor_inj`：lTensor_inj_iff_rTensor_inj : Fun
ction.Injective (lTensor M f) ↔ Function.Injective (rTensor M f)
· 使用定理 `Module.Invertible.lTensor_injective_iff`：lTensor_injective_iff {f : N ->
ₗ[R] P} : Function.Injective (f.lTensor M) ↔ Function.Injective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rTensor_injective_iff {f : N →ₗ[R] P} :
    Function.Injective (f.rTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_injective_iff]
/-
**Module.Invertible.lTensor_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inv
ertible`。
形式化陈述：lTensor_surjective_iff {f : N ->ₗ[R] P} : Function.Surjective (f.lTensor M
) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Invertible.leftCancelEquiv_comp_lTensor_comp_symm`：leftCancelEqui
v_comp_lTensor_comp_symm (f : P ->ₗ[R] Q) : leftCancelEquiv Q e ∘ₗ (f.lTensor N)
.lTensor M ∘ₗ (leftCancelEquiv P e).symm = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
-/
theorem lTensor_surjective_iff {f : N →ₗ[R] P} :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, LinearMap.lTensor_surjective _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using LinearMap.lTensor_surjective _ h
/-
**Module.Invertible.rTensor_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inv
ertible`。
形式化陈述：rTensor_surjective_iff {f : N ->ₗ[R] P} : Function.Surjective (f.rTensor M
) ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_surj_iff_rTensor_surj`：lTensor_surj_iff_rTensor_surj :
 Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f)
· 使用定理 `Module.Invertible.lTensor_surjective_iff`：lTensor_surjective_iff {f : N 
->ₗ[R] P} : Function.Surjective (f.lTensor M) ↔ Function.Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rTensor_surjective_iff {f : N →ₗ[R] P} :
    Function.Surjective (f.rTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj, lTensor_surjective_iff]
/-
**Module.Invertible.lTensor_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inve
rtible`。
形式化陈述：lTensor_bijective_iff {f : N ->ₗ[R] P} : Function.Bijective (f.lTensor M) 
↔ Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lTensor_bijective_iff {f : N →ₗ[R] P} :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff]
/-
**Module.Invertible.rTensor_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inve
rtible`。
形式化陈述：rTensor_bijective_iff {f : N ->ₗ[R] P} : Function.Bijective (f.rTensor M) 
↔ Function.Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rTensor_bijective_iff {f : N →ₗ[R] P} :
    Function.Bijective (f.rTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff]

end inj_surj_bij

open Finsupp in
variable {R M} in
/-- An invertible module is free iff it is isomorphic to the ring, i.e. its class is trivial in
the Picard group. -/
/-
**Module.Invertible.free_iff_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inver
tible`。
形式化陈述：free_iff_linearEquiv : Free R M ↔ Nonempty (M ≃ₗ[R] R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `card_eq_of_linearEquiv`：card_eq_of_linearEquiv {α β : Type*} [Fintype α]
 [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R) : Fintype.card α = Fintype.card β
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_nontrivial_of_commSemiring`：∀ {R : Type u_4} [inst : Co
mmSemiring R] [Nontrivial R], RankCondition R
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_eq_one_iff_nonempty_unique`：card_eq_one_iff_nonempty_unique
 : card α = 1 ↔ Nonempty (Unique α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…

--- 原说明 ---
An invertible module is free iff it is isomorphic to the ring, i.e. its class is
 trivial in
the Picard group.
-/
theorem free_iff_linearEquiv : Free R M ↔ Nonempty (M ≃ₗ[R] R) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ .of_equiv e.symm⟩
  nontriviality R
  have e := (Free.chooseBasis R M).repr
  have := card_eq_of_linearEquiv R <|
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ e.dualMap)
      e.symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨e ≪≫ₗ uniqueLinearEquiv R R default⟩
/-
**Module.Invertible.finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`
。
形式化陈述：∀ (R : Type u) (M : Type v) [inst : CommSemiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Module.Invertible R M] [Module.Free R M], M
odule.finrank R M = 1
参数：R : Type u；M : Type v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Invertible.free_iff_linearEquiv`：free_iff_linearEquiv : Free R M 
↔ Nonempty (M ≃ₗ[R] R)
· 使用定理 `CommSemiring.finrank_self`：CommSemiring.finrank_self (R) [CommSemiring R
] : Module.finrank R R = 1
-/
protected theorem finrank_eq_one [Free R M] : finrank R M = 1 := by
  rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq, CommSemiring.finrank_self]
/-
**Module.Invertible.rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`。
形式化陈述：rank_eq_one [Free R M] : Module.rank R M = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.rank_eq_one_iff_finrank_eq_one`：rank_eq_one_iff_finrank_eq_one : 
Module.rank R M = 1 ↔ finrank R M = 1
· 使用定理 `Module.Invertible.finrank_eq_one`：∀ (R : Type u) (M : Type v) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.
Invertible R M] [Modul…
-/
theorem rank_eq_one [Free R M] : Module.rank R M = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr (Invertible.finrank_eq_one R M)

open TensorProduct (comm lid) in
/-
**Module.Invertible.toModuleEnd_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inve
rtible`。
形式化陈述：toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `Module.toModuleEnd_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type u_4)
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [
inst_3 : Semir…
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用定理 `RingEquiv.moduleEndSelf_apply`：∀ (R : Type u_1) [inst : Semiring R] (s :
 Rᵐᵒᵖ), (RingEquiv.moduleEndSelf R) s = DistribSMul.toLinearMap R R s
· 使用定理 `Module.Invertible.rTensorEquiv_apply_apply`：∀ {R : Type u} {M : Type v} 
{N : Type u_1} (P : Type u_2) (Q : Type u_3) [inst : CommSemiring R]   [inst_1 :
 AddCommMonoid M] [inst_2 : AddC…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LinearMap.toAddMonoidHom'_apply`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {M : 
Type u_8} {M₂ : Type u_10} [inst : Semiring R₁] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
theorem toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S := R) M) := by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul R M where
  eq_of_smul_eq_smul {_ _} h := (toModuleEnd_bijective R M).injective <| LinearMap.ext h

variable {R M N} in
/-
**Module.Invertible.bijective_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bijective_self_of_surjective (f : R →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Bijective f where
  left {r₁ r₂} eq := smul_left_injective' (α := M) <| funext fun m ↦ by
    obtain ⟨r, rfl⟩ := hf m
    simp_rw [← map_smul, smul_eq_mul, mul_comm _ r, ← smul_eq_mul, map_smul, eq]
  right := hf

variable {R M N} in
/- Not true if `surjective` is replaced by `injective`: any nonzero element in an invertible
module over a domain generates a submodule isomorphic to the domain, which is not the whole
module unless the module is free. -/
/-
**Module.Invertible.bijective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module.In
vertible`。
形式化陈述：bijective_of_surjective [Module.Invertible R N] {f : M ->ₗ[R] N} (hf : Fun
ction.Surjective f) : Function.Bijective f
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Invertible.instDual`：∀ (R : Type u) (M : Type v) [inst : CommSemi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Invert
ible R M], Modul…
· 使用定理 `_private.Mathlib.RingTheory.PicardGroup.0.Module.Invertible.bijective_se
lf_of_surjective`：∀ {R : Type u} {M : Type v} [inst : CommSemiring R] [inst_1 : 
AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Invertible R M] (f : R…
· 使用定理 `Module.Invertible.instTensorProduct`：∀ (R : Type u) (M : Type v) (N : Ty
pe u_1) [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMono
id N]   [inst_3 : _root_.…

--- 原说明 ---
Not true if `surjective` is replaced by `injective`: any nonzero element in an i
nvertible
module over a domain generates a submodule isomorphic to the domain, which is no
t the whole
module unless the module is free.
-/
theorem bijective_of_surjective [Module.Invertible R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : Function.Bijective f := by
  simpa [lTensor_bijective_iff] using bijective_self_of_surjective
    (f.lTensor _ ∘ₗ (linearEquiv R M).symm.toLinearMap) (by simpa [lTensor_surjective_iff] using hf)

section LinearEquiv
variable {R M N} [Module.Invertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M}

/-
**Module.Invertible.rightInverse_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e.Invertible`。
形式化陈述：rightInverse_of_leftInverse (hfg : Function.LeftInverse f g) : Function.Ri
ghtInverse f g
参数：hfg : Function.LeftInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.rightInverse_of_injective_of_leftInverse`：∀ {α : Sort u_1} {β :
 Sort u_2} {f : α → β} {g : β → α},   Function.Injective f → Function.LeftInvers
e f g → Function.RightInverse f g
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Module.Invertible.bijective_of_surjective`：bijective_of_surjective [Modu
le.Invertible R N] {f : M ->ₗ[R] N} (hf : Function.Surjective f) : Function.Bije
ctive f
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
-/
theorem rightInverse_of_leftInverse (hfg : Function.LeftInverse f g) :
    Function.RightInverse f g :=
  Function.rightInverse_of_injective_of_leftInverse
    (bijective_of_surjective hfg.surjective).injective hfg
/-
**Module.Invertible.leftInverse_of_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e.Invertible`。
形式化陈述：leftInverse_of_rightInverse (hfg : Function.RightInverse f g) : Function.L
eftInverse f g
参数：hfg : Function.RightInverse f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.rightInverse_of_leftInverse`：rightInverse_of_leftInver
se (hfg : Function.LeftInverse f g) : Function.RightInverse f g
-/
theorem leftInverse_of_rightInverse (hfg : Function.RightInverse f g) :
    Function.LeftInverse f g :=
  rightInverse_of_leftInverse hfg

variable (f g) in
/-
**Module.Invertible.leftInverse_iff_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.Invertible`。
形式化陈述：leftInverse_iff_rightInverse : Function.LeftInverse f g ↔ Function.RightIn
verse f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.rightInverse_of_leftInverse`：rightInverse_of_leftInver
se (hfg : Function.LeftInverse f g) : Function.RightInverse f g
· 使用定理 `Module.Invertible.leftInverse_of_rightInverse`：leftInverse_of_rightInver
se (hfg : Function.RightInverse f g) : Function.LeftInverse f g
-/
theorem leftInverse_iff_rightInverse :
    Function.LeftInverse f g ↔ Function.RightInverse f g :=
  ⟨rightInverse_of_leftInverse, leftInverse_of_rightInverse⟩

/-- If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modules, and `f` is
a left inverse of `g`, then in fact `f` is also the right inverse of `g`, and we promote this to
an `R`-module isomorphism. -/
/-
**Module.Invertible.linearEquivOfLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Module.I
nvertible`。
形式化陈述：linearEquivOfLeftInverse (hfg : Function.LeftInverse f g) : M ≃ₗ[R] N
参数：hfg : Function.LeftInverse f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modu
les, and `f` is
a left inverse of `g`, then in fact `f` is also the right inverse of `g`, and we
 promote this to
an `R`-module isomorphism.
-/
def linearEquivOfLeftInverse (hfg : Function.LeftInverse f g) : M ≃ₗ[R] N :=
  .ofLinearMap f g (LinearMap.ext hfg) (LinearMap.ext <| rightInverse_of_leftInverse hfg)
/-
**Module.Invertible.linearEquivOfLeftInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] [inst_5 : Module.Invertible R M]   [inst_6 : Module.I
nvertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M} (hfg : Function.LeftInverse ⇑f ⇑g
) (x : M),   (Module.Invertible.linearEquivOfLeftInverse hfg) x = f x
参数：hfg : Function.LeftInverse ⇑f ⇑g；x : M；Module.Invertible.linearEquivOfLeftInv
erse hfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearEquivOfLeftInverse_apply (hfg : Function.LeftInverse f g) (x : M) :
    linearEquivOfLeftInverse hfg x = f x := rfl
/-
**Module.Invertible.linearEquivOfLeftInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] [inst_5 : Module.Invertible R M]   [inst_6 : Module.I
nvertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M} (hfg : Function.LeftInverse ⇑f ⇑g
) (x : N),   (Module.Invertible.linearEquivOfLeftInverse hfg).symm x = g x
参数：hfg : Function.LeftInverse ⇑f ⇑g；x : N；Module.Invertible.linearEquivOfLeftInv
erse hfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearEquivOfLeftInverse_symm_apply (hfg : Function.LeftInverse f g) (x : N) :
    (linearEquivOfLeftInverse hfg).symm x = g x := rfl

/-- If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modules, and `f` is
a right inverse of `g`, then in fact `f` is also the left inverse of `g`, and we promote this to
an `R`-module isomorphism. -/
/-
**Module.Invertible.linearEquivOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Module.
Invertible`。
形式化陈述：linearEquivOfRightInverse (hfg : Function.RightInverse f g) : M ≃ₗ[R] N
参数：hfg : Function.RightInverse f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modu
les, and `f` is
a right inverse of `g`, then in fact `f` is also the left inverse of `g`, and we
 promote this to
an `R`-module isomorphism.
-/
def linearEquivOfRightInverse (hfg : Function.RightInverse f g) : M ≃ₗ[R] N :=
  .ofLinearMap f g (LinearMap.ext <| leftInverse_of_rightInverse hfg) (LinearMap.ext hfg)
/-
**Module.Invertible.linearEquivOfRightInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] [inst_5 : Module.Invertible R M]   [inst_6 : Module.I
nvertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M} (hfg : Function.RightInverse ⇑f ⇑
g) (x : M),   (Module.Invertible.linearEquivOfRightInverse hfg) x = f x
参数：hfg : Function.RightInverse ⇑f ⇑g；x : M；Module.Invertible.linearEquivOfRightI
nverse hfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearEquivOfRightInverse_apply (hfg : Function.RightInverse f g) (x : M) :
    linearEquivOfRightInverse hfg x = f x := rfl
/-
**Module.Invertible.linearEquivOfRightInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名
空间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} {N : Type u_1} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst_3 : _root_.Module R M] [i
nst_4 : _root_.Module R N] [inst_5 : Module.Invertible R M]   [inst_6 : Module.I
nvertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M} (hfg : Function.RightInverse ⇑f ⇑
g) (x : N),   (Module.Invertible.linearEquivOfRightInverse hfg).symm x = g x
参数：hfg : Function.RightInverse ⇑f ⇑g；x : N；Module.Invertible.linearEquivOfRightI
nverse hfg。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearEquivOfRightInverse_symm_apply (hfg : Function.RightInverse f g) (x : N) :
    (linearEquivOfRightInverse hfg).symm x = g x := rfl

end LinearEquiv

section Algebra

section algEquivOfRing

variable [Semiring A] [Algebra R A] [Module.Invertible R A]

/-- If an `R`-algebra `A` is also an invertible `R`-module, then it is in fact isomorphic to the
base ring `R`. The algebra structure gives us a map `A ⊗ A → A`, which after tensoring by `Aᵛ`
becomes a map `A → R`, which is the inverse map we seek. -/
/-
**Module.Invertible.algEquivOfRing** 是 Mathlib 中的一个定义，位于命名空间 `Module.Invertible`
。
形式化陈述：algEquivOfRing : R ≃ₐ[R] A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R

--- 原说明 ---
If an `R`-algebra `A` is also an invertible `R`-module, then it is in fact isomo
rphic to the
base ring `R`. The algebra structure gives us a map `A ⊗ A → A`, which after ten
soring by `Aᵛ`
becomes a map `A → R`, which is the inverse map we seek.
-/
noncomputable def algEquivOfRing : R ≃ₐ[R] A :=
  let inv : A →ₗ[R] R :=
    linearEquiv R A ∘ₗ
      (LinearMap.mul' R A).lTensor (Dual R A) ∘ₗ
      (leftCancelEquiv A (linearEquiv R A)).symm
  have right : inv ∘ₗ Algebra.linearMap R A = LinearMap.id :=
    let ⟨s, hs⟩ := exists_finset ((linearEquiv R A).symm 1)
    LinearMap.ext_ring <| by simp [inv, hs, sum_tmul, map_sum, ← (LinearEquiv.symm_apply_eq _).1 hs]
  { linearEquivOfRightInverse (f := Algebra.linearMap R A) (g := inv) (LinearMap.ext_iff.1 right),
    Algebra.ofId R A with }

variable {A} in
/-
**Module.Invertible.algEquivOfRing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Inver
tible`。
形式化陈述：∀ (R : Type u) {A : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A]   [inst_3 : Module.Invertible R A] (x : R), (Module.Inv
ertible.algEquivOfRing R A) x = (algebraMap R A) x
参数：R : Type u；x : R；Module.Invertible.algEquivOfRing R A；algebraMap R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algEquivOfRing_apply (x : R) : algEquivOfRing R A x = algebraMap R A x := rfl

end algEquivOfRing

section CommSemiring

variable [CommSemiring A] [Algebra R A]

/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Invertible A (A ⊗[R] M) :=
  .right (M := A ⊗[R] Dual R M) <| (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

variable {R M N A} in
/-
**Module.Invertible.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertib
le`。
形式化陈述：of_isLocalization (S : Submonoid R) [IsLocalization S A] (f : M ->ₗ[R] N) 
[IsLocalizedModule S f] [Module A N] [IsScalarTower R A N] : Module.Invertible A
 N
参数：S : Submonoid R；f : M ->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.congr`：∀ {R : Type u} {M : Type v} {N : Type u_1} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [ins
t_3 : _root_.…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Invertible.instTensorProduct_1`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
-/
theorem of_isLocalization (S : Submonoid R) [IsLocalization S A]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] [Module A N] [IsScalarTower R A N] :
    Module.Invertible A N :=
  .congr (IsLocalizedModule.isBaseChange S A f).equiv
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Submonoid R) : Module.Invertible (Localization S) (LocalizedModule S M) :=
  of_isLocalization S (LocalizedModule.mkLinearMap S M)
/-
**Module.Invertible.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Invertible`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L) [AddCommMonoid L] [Module R L] [Module A L] [IsScalarTower R A L]
    [Module.Invertible A L] : Module.Invertible A (L ⊗[R] M) :=
  .congr (AlgebraTensorModule.cancelBaseChange R A A L M)

/-- An invertible module over a commutative semiring is Zariski-locally free of rank 1.
Theorem 10.7 in [BorgerJun2024].

More precisely, there is a finite set of elements of `R` that generate the unit ideal,
and localizing `M` at any one of them yields a free module.

Finite projective modules over a local commutative semiring may not be free,
see Remark 7.10, Example 9.6 and 9.8. -/
/-
**Module.Invertible.exists_finset_free_localization** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Invertible`。
形式化陈述：exists_finset_free_localization : exists s : Finset R, Ideal.span (s : Set
 R) = ⊤ ∧ forall r in s, Free (Localization.Away r) (LocalizedModule.Away r M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.exists_finset`：exists_finset (x : M otimes[R] N) : exists 
S : Finset (M × N), x = S.sum fun i => i.1 otimesₜ[R] i.2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Module.Invertible.bijective`：∀ {R : Type u} {M : Type v} {inst : CommSem
iring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Modul
e.Invertible R M]…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
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
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Module.Invertible.bijective_of_surjective`：bijective_of_surjective [Modu
le.Invertible R N] {f : M ->ₗ[R] N} (hf : Function.Surjective f) : Function.Bije
ctive f
· 使用定理 `Module.Invertible.instLocalizationLocalizedModule`：∀ (R : Type u) (M : T
ype v) [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   [Module.Invertible R M] (S : S…
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R

--- 原说明 ---
An invertible module over a commutative semiring is Zariski-locally free of rank
 1.
Theorem 10.7 in [BorgerJun2024].

More precisely, there is a finite set of elements of `R` that generate the unit 
ideal,
and localizing `M` at any one of them yields a free module.

Finite projective modules over a local commutative semiring may not be free,
see Remark 7.10, Example 9.6 and 9.8.
-/
theorem exists_finset_free_localization :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r ∈ s, Free (Localization.Away r) (LocalizedModule.Away r M) := by
  classical
  -- write 1 = ∑ᵢ fᵢ(mᵢ) with `mᵢ : M` and `fᵢ : Dual R M`
  obtain ⟨S, hS⟩ := ((linearEquiv R M).symm 1).exists_finset
  refine ⟨S.image fun i ↦ i.1 i.2, ?_, fun r hr ↦ ?_⟩
  -- Part 1: The evaluations fᵢ(mᵢ) generate the unit ideal
  · simpa [Ideal.eq_top_iff_one, (LinearEquiv.symm_apply_eq _).mp hS, linearEquiv]
      using Ideal.sum_mem _ fun i hi ↦ Ideal.subset_span (Finset.mem_image_of_mem _ hi)
  -- Part 2: After localizing at any f(m), the module becomes free
  obtain ⟨⟨f, m⟩, _, rfl⟩ := Finset.mem_image.mp hr
  -- Extend f to a R_{f(m)}-linear functional f' on the localized module
  let f' : Dual (Localization.Away (f m)) (LocalizedModule.Away (f m) M) :=
    .extendScalarsOfIsLocalization (.powers (f m)) _ <| IsLocalizedModule.map
      (.powers (f m)) (LocalizedModule.mkLinearMap _ M) (Algebra.linearMap R _) f
  -- f'(m/1) = f(m)/1 is a unit in R_{f(m)}, so f' is surjective and therefore bijective
  have surj : Function.Surjective f' := LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem
    _ ⟨_, IsLocalizedModule.map_apply ..⟩ (IsLocalization.Away.algebraMap_isUnit (f m))
  exact .of_equiv <| .symm <| .ofBijective f' (bijective_of_surjective surj)

end CommSemiring

end Algebra

end Invertible

end Module

section PicardGroup

open CategoryTheory Module

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquivₛ
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type u) [CommRing R] (M : (Skeleton <| ModuleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquiv
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{u} (Skeleton <| SemimoduleCat.{u} R)ˣ :=
  let sf := Σ n, ModuleCon R (Fin n → R)
  have {c₁ c₂ : sf} : c₁ = c₂ → c₁.2.Quotient ≃ₗ[R] c₂.2.Quotient := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerReprₛ R M⟩
  small_of_injective (f := f) fun M N eq ↦ Units.ext <| Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquivₛ R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquivₛ R N).toModuleIsoₛ⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type u) [CommRing R] : Small.{u} (Skeleton <| ModuleCat.{u} R)ˣ :=
  small_map (Units.mapEquiv <| Skeleton.mulEquiv ModuleCat.equivalenceSemimoduleCat).toEquiv

/-- The Picard group of a commutative semiring R consists of the invertible R-modules,
up to isomorphism. -/
/-
**CommRing.Pic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommRing.Pic (R : Type u) [CommSemiring R] : Type u
参数：R : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ

--- 原说明 ---
The Picard group of a commutative semiring R consists of the invertible R-module
s,
up to isomorphism.
-/
def CommRing.Pic (R : Type u) [CommSemiring R] : Type u :=
  Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ

open CommRing (Pic)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CommGroup (Pic R) := fast_instance% (equivShrink _).symm.commGroup

variable [Module.Invertible R M] [Module.Invertible R N]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Invertible R (Finite.reprₛ R M) := .congr (Finite.reprEquivₛ R M).symm

namespace CommRing.Pic

variable {R} in
/-- A representative of an element in the Picard group. -/
/-
**CommRing.Pic.AsModule** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommRing.Pic`。
形式化陈述：AsModule (M : Pic R) : Type u
参数：M : Pic R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A representative of an element in the Picard group.
-/
abbrev AsModule (M : Pic R) : Type u := ((equivShrink _).symm M).val
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CoeSort (Pic R) (Type u) := ⟨AsModule⟩
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (R) [CommRing R] (M : Pic R) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.privateInPublic true in
/-
**CommRing.Pic.equivShrinkLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def equivShrinkLinearEquiv (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) :
    (id <| equivShrink _ M : Pic R) ≃ₗ[R] M :=
  have {M N : Skeleton (SemimoduleCat.{u} R)} : M = N → M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)

/-- The class of an invertible module in the Picard group. -/
/-
**CommRing.Pic.mk** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic`。
形式化陈述：(R : Type u) →   (M : Type v) →     [inst : CommSemiring R] →       [inst_
1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [Module.Invertible R M] → 
CommRing.Pic R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…

--- 原说明 ---
The class of an invertible module in the Picard group.
-/
protected noncomputable def mk : Pic R := equivShrink _ <|
  letI M' := Finite.reprₛ R M
  .mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ <| by
    rw [← toSkeleton, ← toSkeleton, mul_comm, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIsoₛ⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `mk R M` is indeed the class of `M`. -/
/-
**CommRing.Pic.mk.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic.mk`。
形式化陈述：(R : Type u) →   (M : Type v) →     [inst : CommSemiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → [inst_3 : Module.I
nvertible R M] → (CommRing.Pic.mk R M).AsModule ≃ₗ[R] M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`mk R M` is indeed the class of `M`.
-/
noncomputable def mk.linearEquiv : Pic.mk R M ≃ₗ[R] M :=
  equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (SemimoduleCat.of R (Finite.reprₛ R M))).some.toLinearEquivₛ ≪≫ₗ Finite.reprEquivₛ R M

variable {R M N}
/-
**CommRing.Pic.mk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk_eq_iff_out`：Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y
 : Quotient s} : ⟦x⟧ = y ↔ x ≈ Quotient.out y
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
-/
theorem mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where
  mp := (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
  mpr := fun ⟨e⟩ ↦ ((equivShrink _).eq_symm_apply).mp <|
    Units.ext <| Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquivₛ R M ≪≫ₗ e).toModuleIsoₛ⟩
/-
**CommRing.Pic.mk_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_self {M : Pic R} : Pic.mk R M = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `CommRing.Pic.mk_eq_iff`：mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempt
y (M ≃ₗ[R] N) where mp
-/
theorem mk_eq_self {M : Pic R} : Pic.mk R M = M := mk_eq_iff.mpr ⟨.refl ..⟩
/-
**CommRing.Pic.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：ext_iff {M N : Pic R} : M = N ↔ Nonempty (M ≃ₗ[R] N)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CommRing.Pic.mk_eq_iff`：mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempt
y (M ≃ₗ[R] N) where mp
· 使用定理 `CommRing.Pic.mk_eq_self`：mk_eq_self {M : Pic R} : Pic.mk R M = M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ext_iff {M N : Pic R} : M = N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← mk_eq_iff, mk_eq_self]
/-
**CommRing.Pic.mk_eq_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CommRing.Pic.mk_eq_iff`：mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempt
y (M ≃ₗ[R] N) where mp
-/
theorem mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN.symm⟩⟩
/-
**CommRing.Pic.mk_self** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_self : Pic.mk R R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
-/
theorem mk_self : Pic.mk R R = 1 :=
  congr_arg (equivShrink _) <| Units.ext <| Quotient.sound ⟨(Finite.reprEquivₛ R R).toModuleIsoₛ⟩
/-
**CommRing.Pic.mk_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CommRing.Pic.mk_self`：mk_self : Pic.mk R R = 1
· 使用定理 `CommRing.Pic.mk_eq_mk_iff`：mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ None
mpty (M ≃ₗ[R] N)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) := by
  rw [← mk_self, mk_eq_mk_iff]
/-
**CommRing.Pic.mk_eq_one_iff_free** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_one_iff_free : Pic.mk R M = 1 ↔ Free R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CommRing.Pic.mk_eq_one_iff`：mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M
 ≃ₗ[R] R)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Module.Invertible.free_iff_linearEquiv`：free_iff_linearEquiv : Free R M 
↔ Nonempty (M ≃ₗ[R] R)
-/
theorem mk_eq_one_iff_free : Pic.mk R M = 1 ↔ Free R M :=
  mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

variable (R M) in
/-
**CommRing.Pic.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_eq_one [Free R M] : Pic.mk R M = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CommRing.Pic.mk_eq_one_iff_free`：mk_eq_one_iff_free : Pic.mk R M = 1 ↔ F
ree R M
-/
theorem mk_eq_one [Free R M] : Pic.mk R M = 1 := mk_eq_one_iff_free.mpr ‹_›
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Free R (1 : Pic R) := mk_eq_one_iff_free.mp mk_eq_self
/-
**CommRing.Pic.mk_tensor** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_tensor : Pic.mk R (M otimes[R] N) = Pic.mk R M * Pic.mk R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `CategoryTheory.Skeleton.toSkeleton_tensorObj`：toSkeleton_tensorObj (X Y 
: C) : toSkeleton (X otimes Y) = toSkeleton X * toSkeleton Y
-/
theorem mk_tensor : Pic.mk R (M ⊗[R] N) = Pic.mk R M * Pic.mk R N :=
  congr_arg (equivShrink _) <| Units.ext <| by
    simp_rw [Pic.mk, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquivₛ R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquivₛ R M).symm (Finite.reprEquivₛ R N).symm).toModuleIsoₛ⟩
/-
**CommRing.Pic.mk_dual** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Invertible.instFinite`：∀ (R : Type u) (M : Type v) [inst : CommSe
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Inve
rtible R M], Modul…
· 使用定理 `Module.Invertible.instDual`：∀ (R : Type u) (M : Type v) [inst : CommSemi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Invert
ible R M], Modul…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mk.eq_1`：∀ (R : Type u) (M : Type v) [inst : CommSemiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.Inv
ertible R …
· 使用定理 `Equiv.toFun_as_coe`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.toFun = ⇑
e
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
-/
theorem mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹ :=
  congr_arg (equivShrink _) <| Units.ext <| by
    rw [Pic.mk, Equiv.toFun_as_coe, Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquivₛ R _ ≪≫ₗ (Finite.reprEquivₛ R _).dualMap).toModuleIsoₛ⟩
/-
**CommRing.Pic.inv_eq_dual** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：inv_eq_dual (M : Pic R) : M⁻¹ = Pic.mk R (Dual R M)
参数：M : Pic R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Invertible.instDual`：∀ (R : Type u) (M : Type v) [inst : CommSemi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Invert
ible R M], Modul…
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mk_dual`：mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹
· 使用定理 `CommRing.Pic.mk_eq_self`：mk_eq_self {M : Pic R} : Pic.mk R M = M
-/
theorem inv_eq_dual (M : Pic R) : M⁻¹ = Pic.mk R (Dual R M) := by
  rw [mk_dual, mk_eq_self]
/-
**CommRing.Pic.mul_eq_tensor** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mul_eq_tensor (M N : Pic R) : M * N = Pic.mk R (M otimes[R] N)
参数：M N : Pic R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mk_tensor`：mk_tensor : Pic.mk R (M otimes[R] N) = Pic.mk R 
M * Pic.mk R N
· 使用定理 `CommRing.Pic.mk_eq_self`：mk_eq_self {M : Pic R} : Pic.mk R M = M
-/
theorem mul_eq_tensor (M N : Pic R) : M * N = Pic.mk R (M ⊗[R] N) := by
  rw [mk_tensor, mk_eq_self, mk_eq_self]
/-
**CommRing.Pic.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：subsingleton_iff {R : Type u} [CommRing R] : Subsingleton (Pic R) ↔ forall
 (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M -> Free R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CommRing.Pic.subsingleton_iffₛ`：subsingleton_iffₛ : Subsingleton (Pic R)
 ↔ forall (M : Type u) [AddCommMonoid M] [Module R M], Module.Invertible R M -> 
Free R M
-/
theorem subsingleton_iffₛ : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommMonoid M] [Module R M], Module.Invertible R M → Free R M :=
  .trans ⟨fun _ M _ _ _ ↦ Subsingleton.elim ..,
      fun h ↦ ⟨fun M N ↦ by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩ <|
    forall₄_congr fun _ _ _ _ ↦ mk_eq_one_iff_free
/-
**CommRing.Pic.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：subsingleton_iff {R : Type u} [CommRing R] : Subsingleton (Pic R) ↔ forall
 (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M -> Free R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `CommRing.Pic.subsingleton_iffₛ`：subsingleton_iffₛ : Subsingleton (Pic R)
 ↔ forall (M : Type u) [AddCommMonoid M] [Module R M], Module.Invertible R M -> 
Free R M
-/
theorem subsingleton_iff {R : Type u} [CommRing R] : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M → Free R M :=
  subsingleton_iffₛ.trans
    ⟨fun h M ↦ h M, fun h M ↦ let _ := @Module.addCommMonoidToAddCommGroup R; h M⟩
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton (Pic R)] : Free R M :=
  have := subsingleton_iffₛ.mp ‹_› (Finite.reprₛ R M) inferInstance
  .of_equiv (Finite.reprEquivₛ R M)

/-- The Picard group of a local semiring is trivial. -/
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Picard group of a local semiring is trivial.
-/
instance [IsLocalRing R] : Subsingleton (Pic R) := subsingleton_iffₛ.mpr fun M _ _ _ ↦ by
  obtain ⟨S, hS⟩ := ((Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Invertible.linearEquiv] using hS
  obtain ⟨⟨f, m⟩, mem, hfm⟩ := IsLocalRing.exists_of_isUnit_sum (hS ▸ isUnit_one)
  exact .of_equiv <| .symm <| .ofBijective f (Invertible.bijective_of_surjective <|
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨m, rfl⟩ hfm)

/-- The Picard group of a semilocal ring is trivial. -/
/-
**CommRing.Pic.** 是 Mathlib 中的一个实例，位于命名空间 `CommRing.Pic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Picard group of a semilocal ring is trivial.
-/
instance (R) [CommRing R] [Finite (MaximalSpectrum R)] : Subsingleton (Pic R) :=
  subsingleton_iff.mpr fun _ _ _ _ ↦ free_of_flat_of_finrank_eq _ _ 1
    fun _ ↦ let _ := @Ideal.Quotient.field; Invertible.finrank_eq_one ..

variable (R) (A B : Type*) [CommSemiring A] [CommSemiring B] [Algebra R A]

open AlgebraTensorModule in
/-- Every `R`-algebra `A` gives rise to a homomorphism between Picard groups of `R` and `A`. -/
/-
**CommRing.Pic.mapAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic`。
形式化陈述：(R : Type u) →   [inst : CommSemiring R] →     (A : Type u_5) → [inst_1 : 
CommSemiring A] → [Algebra R A] → CommRing.Pic R →* CommRing.Pic A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Every `R`-algebra `A` gives rise to a homomorphism between Picard groups of `R` 
and `A`.
-/
@[simps] noncomputable def mapAlgebra : Pic R →* Pic A where
  toFun M := .mk A (A ⊗[R] M)
  map_one' := mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp inferInstance)
  map_mul' _ _ := by
    rw [← mk_tensor, mk_eq_mk_iff]
    refine ⟨congr (.refl ..) (.symm (mk_eq_iff.mp ?_).some) ≪≫ₗ distribBaseChange R A ..⟩
    simp_rw [mk_tensor, mk_eq_self]

variable {R A B} [Algebra R B] [Algebra A B] [IsScalarTower R A B]
/-
**CommRing.Pic.mapAlgebra_mapAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapAlgebra_mapAlgebra {M : Pic R} : mapAlgebra A B (mapAlgebra R A M) = ma
pAlgebra R B M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `CommRing.Pic.mk_eq_mk_iff`：mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ None
mpty (M ≃ₗ[R] N)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem mapAlgebra_mapAlgebra {M : Pic R} : mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M :=
  mk_eq_mk_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (mk.linearEquiv ..) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange ..⟩
/-
**CommRing.Pic.mapAlgebra_comp_mapAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pi
c`。
形式化陈述：mapAlgebra_comp_mapAlgebra : (mapAlgebra A B).comp (mapAlgebra R A) = mapA
lgebra R B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `CommRing.Pic.mapAlgebra_mapAlgebra`：mapAlgebra_mapAlgebra {M : Pic R} : 
mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M
-/
theorem mapAlgebra_comp_mapAlgebra : (mapAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B := by
  ext; rw [MonoidHom.comp_apply, mapAlgebra_mapAlgebra]
/-
**CommRing.Pic.mapAlgebra_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapAlgebra_self_apply {M : Pic R} : mapAlgebra R R M = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `CommRing.Pic.mk_eq_iff`：mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempt
y (M ≃ₗ[R] N) where mp
-/
theorem mapAlgebra_self_apply {M : Pic R} : mapAlgebra R R M = M :=
  mk_eq_iff.mpr ⟨TensorProduct.lid ..⟩
/-
**CommRing.Pic.mapAlgebra_self** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapAlgebra_self : mapAlgebra R R = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `CommRing.Pic.mapAlgebra_self_apply`：mapAlgebra_self_apply {M : Pic R} : 
mapAlgebra R R M = M
-/
theorem mapAlgebra_self : mapAlgebra R R = .id _ := by ext; exact mapAlgebra_self_apply

variable {S T : Type*} [CommSemiring S] [CommSemiring T] (f : R →+* S) (g : S →+* T)

/-- Every ring homomorphism between commutative semirings induces a homomorphism between
Picard groups. -/
/-
**CommRing.Pic.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic`。
形式化陈述：mapRingHom : Pic R ->* Pic S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every ring homomorphism between commutative semirings induces a homomorphism bet
ween
Picard groups.
-/
noncomputable def mapRingHom : Pic R →* Pic S :=
  let := f.toAlgebra; mapAlgebra R S
/-
**CommRing.Pic.mapRingHom_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapRingHom_algebraMap : mapRingHom (algebraMap R A) = mapAlgebra R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mapRingHom.eq_1`：∀ {R : Type u} [inst : CommSemiring R] {S 
: Type u_7} [inst_1 : CommSemiring S] (f : R →+* S),   CommRing.Pic.mapRingHom f
 = CommRing.Pic.ma…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
-/
theorem mapRingHom_algebraMap : mapRingHom (algebraMap R A) = mapAlgebra R A := by
  rw [mapRingHom, toAlgebra_algebraMap]

variable {f g}
/-
**CommRing.Pic.mapRingHom_comp_mapRingHom** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pi
c`。
形式化陈述：mapRingHom_comp_mapRingHom : (mapRingHom g).comp (mapRingHom f) = mapRingH
om (g.comp f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mapAlgebra_comp_mapAlgebra`：mapAlgebra_comp_mapAlgebra : (m
apAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRingHom_comp_mapRingHom :
    (mapRingHom g).comp (mapRingHom f) = mapRingHom (g.comp f) := by
  algebraize [f, g, g.comp f]
  simp_rw [mapRingHom, mapAlgebra_comp_mapAlgebra]
/-
**CommRing.Pic.mapRingHom_mapRingHom** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapRingHom_mapRingHom {M : Pic R} : mapRingHom g (mapRingHom f M) = mapRin
gHom (g.comp f) M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mapRingHom_comp_mapRingHom`：mapRingHom_comp_mapRingHom : (m
apRingHom g).comp (mapRingHom f) = mapRingHom (g.comp f)
-/
theorem mapRingHom_mapRingHom {M : Pic R} :
    mapRingHom g (mapRingHom f M) = mapRingHom (g.comp f) M :=
  congr($mapRingHom_comp_mapRingHom M)
/-
**CommRing.Pic.mapRingHom_id** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapRingHom_id : mapRingHom (.id R) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mapRingHom.eq_1`：∀ {R : Type u} [inst : CommSemiring R] {S 
: Type u_7} [inst_1 : CommSemiring S] (f : R →+* S),   CommRing.Pic.mapRingHom f
 = CommRing.Pic.ma…
· 使用定理 `CommRing.Pic.mapAlgebra_self`：mapAlgebra_self : mapAlgebra R R = .id _
-/
theorem mapRingHom_id : mapRingHom (.id R) = .id _ := by
  rw [mapRingHom, mapAlgebra_self]
/-
**CommRing.Pic.mapRingHom_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：mapRingHom_id_apply {M : Pic R} : mapRingHom (.id R) M = M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mapRingHom_id`：mapRingHom_id : mapRingHom (.id R) = .id _
-/
theorem mapRingHom_id_apply {M : Pic R} : mapRingHom (.id R) M = M :=
  congr($mapRingHom_id M)

/-- Picard group as a functor from the category of commutative semirings to
the category of abelian groups. -/
/-
**CommRing.Pic.functor** 是 Mathlib 中的一个定义，位于命名空间 `CommRing.Pic`。
形式化陈述：functor : CommSemiRingCat.{u} ⥤ CommGrpCat.{u} where obj R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Picard group as a functor from the category of commutative semirings to
the category of abelian groups.
-/
noncomputable def functor : CommSemiRingCat.{u} ⥤ CommGrpCat.{u} where
  obj R := .of (Pic R)
  map f := CommGrpCat.ofHom (mapRingHom f.hom)
  map_id _ := CommGrpCat.Hom.ext mapRingHom_id
  map_comp _ _ := CommGrpCat.Hom.ext mapRingHom_comp_mapRingHom.symm

end Pic

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The relative Picard group of an `R`-algebra `A`, denoted `Pic(A/R)`,
defined to be the kernel of `Pic.mapAlgebra R A`. -/
/-
**CommRing.relPic** 是 Mathlib 中的一个定义，位于命名空间 `CommRing`。
形式化陈述：(R : Type u) →   [inst : CommSemiring R] → (A : Type u_5) → [inst_1 : Comm
Semiring A] → [Algebra R A] → Subgroup (CommRing.Pic R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative Picard group of an `R`-algebra `A`, denoted `Pic(A/R)`,
defined to be the kernel of `Pic.mapAlgebra R A`.
-/
noncomputable def relPic : Subgroup (Pic R) := (Pic.mapAlgebra R A).ker
/-
**CommRing.relPic_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `CommRing`。
形式化陈述：∀ (R : Type u) [inst : CommSemiring R] (A : Type u_5) [inst_1 : CommSemiri
ng A] [inst_2 : Algebra R A]   [Subsingleton (CommRing.Pic A)], CommRing.relPic 
R A = ⊤
参数：R : Type u；A : Type u_5；CommRing.Pic A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem relPic_eq_top [Subsingleton (Pic A)] : relPic R A = ⊤ :=
  top_unique fun _ _ ↦ Subsingleton.elim ..

end CommRing

end PicardGroup

namespace Module.Invertible

variable [Module.Invertible R M]

/-
**Module.Invertible.tensorProductComm_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Invertible`。
形式化陈述：∀ (R : Type u) (M : Type v) [inst : CommSemiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Module.Invertible R M], TensorProduct.comm 
R M M = LinearEquiv.refl R (TensorProduct R M M)
参数：R : Type u；M : Type v；TensorProduct R M M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.eq_of_localization_maximal`：LinearMap.eq_of_localization_maxim
al (g g' : M ->ₗ[R] M₁) (h : forall (P : Ideal R) [P.IsMaximal], IsLocalizedModu
le.map P.primeCompl (f P) …
· 使用定理 `IsLocalization.instIsLocalizedModuleTensorProductMap`：∀ {R : Type u_1} [
inst : CommSemiring R] (S : Submonoid R) {M : Type u_3} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module R M] {M' : Ty…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalizedModule.linearMap_ext`：linearMap_ext {N N'} [AddCommMonoid N] 
[Module R N] [AddCommMonoid N'] [Module R N'] (f' : N ->ₗ[R] N') [IsLocalizedMod
ule S f'] ⦃g g' : M' …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Invertible.free_iff_linearEquiv`：free_iff_linearEquiv : Free R M 
↔ Nonempty (M ≃ₗ[R] R)
· 使用定理 `Module.Invertible.instLocalizationLocalizedModule`：∀ (R : Type u) (M : T
ype v) [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modul
e R M]   [Module.Invertible R M] (S : S…
· 使用定理 `CommRing.Pic.instFreeOfSubsingleton`：∀ {R : Type u} {M : Type v} [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Modu
le.Invertible R M] [Subsi…
· 使用定理 `CommRing.Pic.instSubsingletonOfIsLocalRing`：∀ {R : Type u} [inst : CommS
emiring R] [IsLocalRing R], Subsingleton (CommRing.Pic R)
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsLocalization.instCompatibleSMulLocalizationOfIsScalarTower_1`：∀ {R : T
ype u_1} [inst : CommSemiring R] (S : Submonoid R) (M₁ : Type u_5) (M₂ : Type u_
6) [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 34 条，此处仅展示前 30 条）
-/
theorem tensorProductComm_eq_refl : TensorProduct.comm R M M = .refl .. := by
  let f (P : Ideal R) [P.IsMaximal] := LocalizedModule.mkLinearMap P.primeCompl M
  let ff (P : Ideal R) [P.IsMaximal] := TensorProduct.map (f P) (f P)
  refine LinearEquiv.toLinearMap_injective <| LinearMap.eq_of_localization_maximal _ ff _ ff _ _
    fun P _ ↦ .trans (b := (TensorProduct.comm ..).toLinearMap) ?_ ?_
  · apply IsLocalizedModule.linearMap_ext P.primeCompl (ff P) (ff P)
    ext; exact IsLocalizedModule.map_apply _ (ff P) ..
  let Rp := Localization P.primeCompl
  have ⟨e⟩ := free_iff_linearEquiv.mp (inferInstance : Free Rp (LocalizedModule P.primeCompl M))
  have e := e.restrictScalars R
  ext x y
  refine (congr e e ≪≫ₗ equivOfCompatibleSMul Rp ..).injective ?_
  suffices e y ⊗ₜ[Rp] e x = e x ⊗ₜ e y by simpa [equivOfCompatibleSMul]
  conv_lhs => rw [← mul_one (e y), ← smul_eq_mul, smul_tmul, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← smul_tmul, smul_eq_mul, mul_one]

variable {R M} in
/-
**Module.Invertible.tmul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Invertible`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : CommSemiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Module.Invertible R M] {m₁ m₂ : M}, m₁ ⊗ₜ[R
] m₂ = m₂ ⊗ₜ[R] m₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Module.Invertible.tensorProductComm_eq_refl`：∀ (R : Type u) (M : Type v)
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [Module.Invertible R M], Tenso…
-/
theorem tmul_comm {m₁ m₂ : M} : m₁ ⊗ₜ[R] m₂ = m₂ ⊗ₜ m₁ :=
  DFunLike.congr_fun (tensorProductComm_eq_refl ..) (m₂ ⊗ₜ m₁)

end Module.Invertible

namespace Submodule

open Module Invertible

variable {R M A}

section Semiring

variable [Semiring A] [Algebra R A] [FaithfulSMul R A]

open LinearMap in
set_option backward.privateInPublic true in
/-
**Submodule.projective_units_and_mul'_comp_lTensor_bijective** 是 Mathlib 中的一个定理，
位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem projective_units_and_mul'_comp_lTensor_bijective (I : (Submodule R A)ˣ) :
    Projective R I ∧ Function.Bijective (mul' R A ∘ₗ I.1.subtype.lTensor A) := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul, ← Finset.coe_image₂, mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S ↦ Finset.mem_image₂.mp i.2
  let f : I →ₗ[R] S → R := .pi fun i ↦ (LinearEquiv.ofInjective
      (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx ↦ by
      rw [← one_eq_range, ← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  have hf (x : I.1) (i : S) : algebraMap R A (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
  let g : (S → R) →ₗ[R] I := .lsum _ _ ℕ fun i ↦ .toSpanSingleton _ _ ⟨b i, hT' <| hb i⟩
  have hgf : g ∘ₗ f = .id := LinearMap.ext fun x ↦ Subtype.ext <| by
    simp only [g, lsum_apply, comp_apply, LinearMap.sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [coe_sum, coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply]
  set m := mul' R A ∘ₗ I.1.subtype.lTensor A
  have eq : (piScalarRight R R A S).toLinearMap ∘ₗ f.lTensor A =
      (.pi fun i : S ↦ mulRight R (r i • a i)) ∘ₗ m := by
    ext; simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
  have := (piScalarRight R R A S).injective.comp <| injective_of_comp_eq_id
    (f.lTensor A) (g.lTensor A) <| by rw [← lTensor_comp, hgf, lTensor_id]
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp, eq, coe_comp] at this
  refine ⟨.of_split f g hgf, .of_comp this, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl, range_comp,
    LinearEquiv.range, map_top, mulMap_range, top_mul_eq_top_of_mul_eq_one I.inv_mul]

open LinearMap in
/-
**Submodule.projective_units** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {A : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A] [FaithfulSMul R A]   (I : (Submodule R A)ˣ), Module.Pro
jective R ↥↑I
参数：I : (Submodule R A)ˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `_private.Mathlib.RingTheory.PicardGroup.0.Submodule.projective_units_and
_mul'_comp_lTensor_bijective`：∀ {R : Type u} {A : Type u_4} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]   (I : (Subm
odule R A)…
-/
instance projective_units (I : (Submodule R A)ˣ) : Projective R I :=
  (projective_units_and_mul'_comp_lTensor_bijective I).1
/-
**Submodule.projective_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {A : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A] [FaithfulSMul R A]   {I : Submodule R A}, IsUnit I → Mo
dule.Projective R ↥I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.projective_units`：∀ {R : Type u} {A : Type u_4} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]   (I :
 (Submodule R A)…
-/
theorem projective_of_isUnit {I : Submodule R A} (hI : IsUnit I) : Projective R I :=
  projective_units hI.unit

variable (I J : (Submodule R A)ˣ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two invertible `R`-submodules in an `R`-algebra `A`, the `R`-linear map from
`I ⊗[R] J` to `I * J` induced by multiplication is an isomorphism. -/
/-
**Submodule.tensorEquivMul** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {A : Type u_4} →     [inst : CommSemiring R] →       [ins
t_1 : Semiring A] →         [inst_2 : Algebra R A] → [FaithfulSMul R A] → (I J :
 (Submodule R A)ˣ) → TensorProduct R ↥↑I ↥↑J ≃ₗ[R] ↥↑(I * J)
参数：I J : (Submodule R A)ˣ；I * J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two invertible `R`-submodules in an `R`-algebra `A`, the `R`-linear map fr
om
`I ⊗[R] J` to `I * J` induced by multiplication is an isomorphism.
-/
noncomputable def tensorEquivMul : I ⊗[R] J ≃ₗ[R] I * J := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, mulMap'_surjective _ _⟩
  convert!
    (projective_units_and_mul'_comp_lTensor_bijective J).2.1.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.1.subtype_injective)
  simp_rw [← LinearMap.coe_comp]
  congr 1; ext; rfl

/-- Given an invertible `R`-submodule `I` in an `R`-algebra `A`, the `R`-linear map
from `I ⊗[R] I⁻¹` to `R` induced by multiplication is an isomorphism. -/
/-
**Submodule.tensorInvEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {A : Type u_4} →     [inst : CommSemiring R] →       [ins
t_1 : Semiring A] →         [inst_2 : Algebra R A] → [FaithfulSMul R A] → (I : (
Submodule R A)ˣ) → TensorProduct R ↥↑I ↥↑I⁻¹ ≃ₗ[R] R
参数：I : (Submodule R A)ˣ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)

--- 原说明 ---
Given an invertible `R`-submodule `I` in an `R`-algebra `A`, the `R`-linear map
from `I ⊗[R] I⁻¹` to `R` induced by multiplication is an isomorphism.
-/
noncomputable def tensorInvEquiv : I ⊗[R] ↑I⁻¹ ≃ₗ[R] R :=
  tensorEquivMul I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Invertible R I := .left (tensorInvEquiv I)

open CommRing Pic

variable (R A) in
/-- The group homomorphism from the invertible submodules in a faithful algebra over `R` to
the Picard group of `R`. See Lemma 2.2 in [RobertsSingh1993]. -/
/-
**Submodule.unitsToPic** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：(R : Type u) →   (A : Type u_4) →     [inst : CommSemiring R] →       [ins
t_1 : Semiring A] → [inst_2 : Algebra R A] → [FaithfulSMul R A] → (Submodule R A
)ˣ →* CommRing.Pic R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instInvertibleSubtypeMemVal`：∀ {R : Type u} {A : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul 
R A]   (I : (Submodule R A)…

--- 原说明 ---
The group homomorphism from the invertible submodules in a faithful algebra over
 `R` to
the Picard group of `R`. See Lemma 2.2 in [RobertsSingh1993].
-/
@[simps] noncomputable def unitsToPic : (Submodule R A)ˣ →* Pic R where
  toFun I := Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul I J).symm⟩

/-- The image of an invertible `R`-submodule `I ⊆ A` under `unitsToPic` is isomorphic to `I`. -/
/-
**Submodule.unitsToPicEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {A : Type u_4} →     [inst : CommSemiring R] →       [ins
t_1 : Semiring A] →         [inst_2 : Algebra R A] →           [inst_3 : Faithfu
lSMul R A] → (I : (Submodule R A)ˣ) → ((Submodule.unitsToPic R A) I).AsModule ≃ₗ
[R] ↥↑I
参数：I : (Submodule R A)ˣ；(Submodule.unitsToPic R A) I。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.instInvertibleSubtypeMemVal`：∀ {R : Type u} {A : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul 
R A]   (I : (Submodule R A)…
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The image of an invertible `R`-submodule `I ⊆ A` under `unitsToPic` is isomorphi
c to `I`.
-/
noncomputable def unitsToPicEquiv (I : (Submodule R A)ˣ) : unitsToPic R A I ≃ₗ[R] I :=
  (mk_eq_iff.mp rfl).some.symm

variable (R A)
/-
**Submodule.ker_unitsToPic** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ (R : Type u) (A : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A]   [inst_3 : FaithfulSMul R A], (Submodule.unitsToPic R 
A).ker = (Units.map ↑(Submodule.spanSingleton R)).range
参数：R : Type u；A : Type u_4；Submodule.unitsToPic R A；Units.map ↑(Submodule.spanSi
ngleton R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.instInvertibleSubtypeMemVal`：∀ {R : Type u} {A : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul 
R A]   (I : (Submodule R A)…
· 使用定理 `CommRing.Pic.mk_eq_one_iff`：mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M
 ≃ₗ[R] R)
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Submodule.eq_span_singleton_of_surjective`：eq_span_singleton_of_surjecti
ve {s : Submodule R M} {f : R ->ₗ[R] s} (hf : Surjective f) : s = span R {(f 1 :
 M)}
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_and_exists`：isUnit_iff_exists_and_exists [Monoid M] {a
 : M} : IsUnit a ↔ (exists b, a * b = 1) ∧ (exists c, c * a = 1)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_singleton_eq_one_iff`：span_singleton_eq_one_iff {x : A} :
 span R {x} = 1 ↔ exists r : Rˣ, x = algebraMap R A r where mp h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
（共 40 条，此处仅展示前 30 条）
-/
theorem ker_unitsToPic :
    (unitsToPic R A).ker = (Units.map (spanSingleton R).toMonoidHom).range := by
  ext I; constructor <;> intro h
  · have e := (mk_eq_one_iff.mp h).some.symm
    have e' := (mk_eq_one_iff.mp (inv_mem h)).some.symm
    have h := eq_span_singleton_of_surjective e.surjective
    have h' := eq_span_singleton_of_surjective e'.surjective
    refine ⟨(isUnit_iff_exists_and_exists.mpr ⟨?_, ?_⟩).unit, Units.ext h.symm⟩
    · have : span R {(e 1).1 * e' 1} = 1 := by simpa [span_mul_span] using congr($h * $h').symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨e' 1 * algebraMap R A r.inv, by simp [← mul_assoc, hr, ← map_mul]⟩
    · have : span R {(e' 1).1 * e 1} = 1 := by simpa [span_mul_span] using congr($h' * $h).symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨algebraMap R A r.inv * e' 1, by simp [mul_assoc, hr, ← map_mul]⟩
  · obtain ⟨x, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨.symm <| (.ofInjective (LinearMap.toSpanSingleton R A x) fun _ _ eq ↦
      (faithfulSMul_iff_injective_smul_one R A).mp ‹_› <| by simpa using congr($eq * x.inv)) ≪≫ₗ
      .ofEq _ _ (by ext; simp [mem_span_singleton])⟩

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A`
at `(Submodule R A)ˣ`. -/
/-
**Submodule.mulExact_unitsMap_spanSingleton_unitsToPic** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
形式化陈述：∀ (R : Type u) (A : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A
] [inst_2 : Algebra R A]   [inst_3 : FaithfulSMul R A], Function.MulExact ⇑(Unit
s.map ↑(Submodule.spanSingleton R)) ⇑(Submodule.unitsToPic R A)
参数：R : Type u；A : Type u_4；Units.map ↑(Submodule.spanSingleton R)；Submodule.unit
sToPic R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MonoidHom.mulExact_iff`：mulExact_iff : MulExact f g ↔ ker g = range f
· 使用定理 `Submodule.ker_unitsToPic`：∀ (R : Type u) (A : Type u_4) [inst : CommSemi
ring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : FaithfulSMul R 
A], (Submodule…

--- 原说明 ---
Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A`
at `(Submodule R A)ˣ`.
-/
theorem mulExact_unitsMap_spanSingleton_unitsToPic :
    Function.MulExact (Units.map (spanSingleton R).toMonoidHom) (unitsToPic R A) :=
  MonoidHom.mulExact_iff.mpr (ker_unitsToPic R A)

end Semiring

end Submodule

namespace Module.Flat

variable {R M A} [Semiring A] [Algebra R A] (e : A ⊗[R] M ≃ₗ[A] A)

/-- If a flat `R`-module becomes free of rank 1 after base-changing to a faithful `R`-algebra `A`,
then it embeds into `A`. -/
/-
**Module.Flat.toAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Module.Flat`。
形式化陈述：{R : Type u} →   {M : Type v} →     {A : Type u_4} →       [inst : CommSem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring A] → [inst_4 : Algebra R A] → (TensorPro
duct R A M ≃ₗ[A] A) → M →ₗ[R] A
参数：TensorProduct R A M ≃ₗ[A] A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
If a flat `R`-module becomes free of rank 1 after base-changing to a faithful `R
`-algebra `A`,
then it embeds into `A`.
-/
noncomputable def toAlgebra : M →ₗ[R] A :=
  e.restrictScalars R ∘ₗ (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

variable [Flat R M] [FaithfulSMul R A]
/-
**Module.Flat.toAlgebra_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：∀ {R : Type u} {M : Type v} {A : Type u_4} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Semiring A] [inst_4
 : Algebra R A] (e : TensorProduct R A M ≃ₗ[A] A)   [Module.Flat R M] [FaithfulS
Mul R A], Function.Injective ⇑(Module.Flat.toAlgebra e)
参数：e : TensorProduct R A M ≃ₗ[A] A；Module.Flat.toAlgebra e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem toAlgebra_injective : Function.Injective (toAlgebra e) := by
  simpa [toAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

/-- A flat `R`-module as a `R`-submodule of a faithful `R`-algebra. -/
/-
**Module.Flat.submoduleAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Module.Flat`。
形式化陈述：{R : Type u} →   {M : Type v} →     {A : Type u_4} →       [inst : CommSem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring A] → [inst_4 : Algebra R A] → (TensorPro
duct R A M ≃ₗ[A] A) → Submodule R A
参数：TensorProduct R A M ≃ₗ[A] A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
A flat `R`-module as a `R`-submodule of a faithful `R`-algebra.
-/
noncomputable abbrev submoduleAlgebra : Submodule R A := LinearMap.range (toAlgebra e)

/-- An isomorphism between a flat `R`-module and its realization as a submodule in
a faithful `R`-algebra. -/
/-
**Module.Flat.submoduleAlgebraEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Flat`。
形式化陈述：{R : Type u} →   {M : Type v} →     {A : Type u_4} →       [inst : CommSem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring A] →               [inst_4 : Algebra R A
] →                 (e : TensorProduct R A M ≃ₗ[A] A) →                   [Modul
e.Flat R M] → [FaithfulSMul R A] → ↥(Module.Flat.submoduleAlgebra e) ≃ₗ[R] M
参数：e : TensorProduct R A M ≃ₗ[A] A；Module.Flat.submoduleAlgebra e。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Flat.toAlgebra_injective`：∀ {R : Type u} {M : Type v} {A : Type u
_4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : Semir…

--- 原说明 ---
An isomorphism between a flat `R`-module and its realization as a submodule in
a faithful `R`-algebra.
-/
noncomputable def submoduleAlgebraEquiv : submoduleAlgebra e ≃ₗ[R] M :=
  .symm <| .ofInjective _ (toAlgebra_injective e)
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Flat R (submoduleAlgebra e) := .of_linearEquiv (submoduleAlgebraEquiv e)
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Invertible R M] : Module.Invertible R (submoduleAlgebra e) :=
  .congr (submoduleAlgebraEquiv e).symm

set_option backward.defeqAttrib.useBackward true in
/-- When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra `A`,
the multiplication map induces an isomorphism `A ⊗[R] M ≃ₗ[A] A`. -/
/-
**Module.Flat.tensorSubmoduleAlgebraEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Flat
`。
形式化陈述：{R : Type u} →   {M : Type v} →     {A : Type u_4} →       [inst : CommSem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring A] →               [inst_4 : Algebra R A
] →                 (e : TensorProduct R A M ≃ₗ[A] A) →                   [Modul
e.Flat R M] → [FaithfulSMul R A] → TensorProduct R A ↥(Module.Flat.submoduleAlge
bra e) ≃ₗ[A] A
参数：e : TensorProduct R A M ≃ₗ[A] A；Module.Flat.submoduleAlgebra e。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra 
`A`,
the multiplication map induces an isomorphism `A ⊗[R] M ≃ₗ[A] A`.
-/
noncomputable def tensorSubmoduleAlgebraEquiv : A ⊗[R] submoduleAlgebra e ≃ₗ[A] A :=
  .ofBijective (.mul'' R A ∘ₗ AlgebraTensorModule.lTensor A A (Submodule.subtype _)) <| by
    convert! (AlgebraTensorModule.congr (.refl ..) (submoduleAlgebraEquiv e) ≪≫ₗ e).bijective
    ext x
    refine x.induction_on (by simp) ?_ (by simp +contextual)
    intro a x
    obtain ⟨m, rfl⟩ := (submoduleAlgebraEquiv e).symm.surjective x
    suffices a * toAlgebra e m = e (a ⊗ₜ[R] m) by simpa using! this
    dsimp [toAlgebra]
    rw [map_one, ← smul_eq_mul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]
/-
**Module.Flat.top_mul_submoduleAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：∀ {R : Type u} {M : Type v} {A : Type u_4} [inst : CommSemiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : Semiring A] [inst_4
 : Algebra R A] (e : TensorProduct R A M ≃ₗ[A] A)   [Module.Flat R M] [FaithfulS
Mul R A], ⊤ * Module.Flat.submoduleAlgebra e = ⊤
参数：e : TensorProduct R A M ≃ₗ[A] A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mulMap_range`：mulMap_range : LinearMap.range (mulMap M N) = M 
* N
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
theorem top_mul_submoduleAlgebra : ⊤ * submoduleAlgebra e = ⊤ := by
  rw [← Submodule.mulMap_range]
  convert!
    (Submodule.topEquiv.rTensor _ ≪≫ₗ (tensorSubmoduleAlgebraEquiv e).restrictScalars R).range
  ext; rfl

/-- When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra `A`,
we have `I ⊗[R] M ≃ₗ[R] I * M` for any `R`-submodule `I` of `A`. -/
/-
**Module.Flat.tensorSubmoduleAlgebraEquivMul** 是 Mathlib 中的一个定义，位于命名空间 `Module.F
lat`。
形式化陈述：{R : Type u} →   {M : Type v} →     {A : Type u_4} →       [inst : CommSem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring A] →               [inst_4 : Algebra R A
] →                 (e : TensorProduct R A M ≃ₗ[A] A) →                   [Modul
e.Flat R M] →                     [FaithfulSMul R A] →                       (I 
: Submodule R A) →                         TensorProduct R ↥I ↥(Module.Flat.subm
oduleAlgebra e) ≃ₗ[R] ↥(I * Module.Flat.submoduleAlgebra e)
参数：e : TensorProduct R A M ≃ₗ[A] A；I : Submodule R A；Module.Flat.submoduleAlgebr
a e；I * Module.Flat.submoduleAlgebra e。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra 
`A`,
we have `I ⊗[R] M ≃ₗ[R] I * M` for any `R`-submodule `I` of `A`.
-/
noncomputable def tensorSubmoduleAlgebraEquivMul (I : Submodule R A) :
    I ⊗[R] submoduleAlgebra e ≃ₗ[R] I * submoduleAlgebra e := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, Submodule.mulMap'_surjective _ _⟩
  convert!
    ((tensorSubmoduleAlgebraEquiv e).restrictScalars R).injective.comp
      (Flat.rTensor_preserves_injective_linearMap _ I.subtype_injective)
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr 1; ext; rfl

end Module.Flat

section PicardGroup

variable [CommSemiring A] [Algebra R A] [FaithfulSMul R A]

open CommRing Pic LinearMap Module.Flat

/-
**Submodule.range_unitsToPic** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：Submodule.range_unitsToPic : (unitsToPic R A).range = relPic R A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSmallUnitsSkeletonSemimoduleCat`：∀ (R : Type u) [inst : CommSemiring
 R], Small.{u, u + 1} (CategoryTheory.Skeleton (SemimoduleCat R))ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `instInvertibleCarrierOutSemimoduleCatValSkeleton`：∀ (R : Type u) [inst :
 CommSemiring R] (M : (CategoryTheory.Skeleton (SemimoduleCat R))ˣ),   Module.In
vertible R ↑(Quotient.out ↑M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `CommRing.Pic.mk_eq_one_iff`：mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M
 ≃ₗ[R] R)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.RingTheory.PicardGroup.0.Submodule.projective_units_and
_mul'_comp_lTensor_bijective`：∀ {R : Type u} {A : Type u_4} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]   (I : (Subm
odule R A)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Module.Invertible.instProjective`：∀ (R : Type u) (M : Type v) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.
Invertible R M], Modul…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommRing.Pic.mk_tensor`：mk_tensor : Pic.mk R (M otimes[R] N) = Pic.mk R 
M * Pic.mk R N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CommRing.Pic.mk_eq_self`：mk_eq_self {M : Pic R} : Pic.mk R M = M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 41 条，此处仅展示前 30 条）
-/
theorem Submodule.range_unitsToPic : (unitsToPic R A).range = relPic R A := by
  ext M; constructor <;> intro h
  · obtain ⟨I, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (unitsToPicEquiv I) ≪≫ₗ
      .ofBijective ((Algebra.TensorProduct.lmul'' R).toLinearMap ∘ₗ AlgebraTensorModule.lTensor A A
        I.1.subtype) (projective_units_and_mul'_comp_lTensor_bijective I).2⟩
  have e := (mk_eq_one_iff.mp h).some
  have f := (mk_eq_one_iff.mp (inv_mem h)).some
  refine ⟨(isUnit_of_mul_isUnit_left (x := submoduleAlgebra e) (y := submoduleAlgebra f) ?_).unit,
    mk_eq_iff.mpr ⟨submoduleAlgebraEquiv e⟩⟩
  have := eq_span_singleton_of_surjective <| LinearEquiv.surjective <|
    (congr (submoduleAlgebraEquiv e) (submoduleAlgebraEquiv f) ≪≫ₗ
    (mk_eq_one_iff.mp <| by simp_rw [mk_tensor, mk_eq_self, mul_inv_cancel]).some).symm ≪≫ₗ
    tensorSubmoduleAlgebraEquivMul f (submoduleAlgebra e)
  rw [this]
  apply_fun (⊤ * ·) at this
  simp_rw [← mul_assoc, top_mul_submoduleAlgebra] at this
  obtain ⟨a, -, eq⟩ := mem_mul_span_singleton.mp (this ▸ mem_top (x := 1))
  exact .map (spanSingleton R).toMonoidHom (.of_mul_eq_one_right _ eq)

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at `Pic R`. -/
/-
**Submodule.mulExact_unitsToPic_mapAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.P
ic`。
形式化陈述：Submodule.mulExact_unitsToPic_mapAlgebra : Function.MulExact (unitsToPic R
 A) (mapAlgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MonoidHom.mulExact_iff`：mulExact_iff : MulExact f g ↔ ker g = range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_unitsToPic`：Submodule.range_unitsToPic : (unitsToPic R A
).range = relPic R A

--- 原说明 ---
Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at `P
ic R`.
-/
theorem Submodule.mulExact_unitsToPic_mapAlgebra :
    Function.MulExact (unitsToPic R A) (mapAlgebra R A) :=
  MonoidHom.mulExact_iff.mpr (range_unitsToPic R A).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
open QuotientGroup in
/-- If `A` is a faithful `R`-algebra, the relative Picard group Pic(A/R) is isomorphic to
the group of the invertible `R`-submodules in `A` modulo the principal submodules. -/
/-
**Submodule.unitsQuotEquivRelPic** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：(R : Type u) →   (A : Type u_4) →     [inst : CommSemiring R] →       [ins
t_1 : CommSemiring A] →         [inst_2 : Algebra R A] →           [FaithfulSMul
 R A] →             (Submodule R A)ˣ ⧸ (Units.map ↑(Submodule.spanSingleton R)).
range ≃* ↥(CommRing.relPic R A)
参数：Submodule.spanSingleton R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.range_unitsToPic`：Submodule.range_unitsToPic : (unitsToPic R A
).range = relPic R A

--- 原说明 ---
If `A` is a faithful `R`-algebra, the relative Picard group Pic(A/R) is isomorph
ic to
the group of the invertible `R`-submodules in `A` modulo the principal submodule
s.
-/
@[simps!] noncomputable def Submodule.unitsQuotEquivRelPic :
    (Submodule R A)ˣ ⧸ (Units.map (spanSingleton R).toMonoidHom).range ≃* relPic R A :=
  (QuotientGroup.congr _ _ (.refl _) ((Subgroup.map_id _).trans (ker_unitsToPic R A).symm)).trans <|
  (quotientKerEquivRange _).trans <| .subgroupCongr (range_unitsToPic R A)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The class group of a domain is isomorphic to the Picard group. -/
/-
**ClassGroup.equivPic** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：(R : Type u_5) → [inst : CommRing R] → [inst_1 : IsDomain R] → ClassGroup 
R ≃* CommRing.Pic R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class group of a domain is isomorphic to the Picard group.
-/
@[simps!] noncomputable def ClassGroup.equivPic (R) [CommRing R] [IsDomain R] :
    ClassGroup R ≃* Pic R :=
  (mulEquivUnitsSubmoduleQuotRange R).trans <| .trans (Submodule.unitsQuotEquivRelPic R _) <|
    .trans (.subgroupCongr <| relPic_eq_top R _) Subgroup.topEquiv

/-- The Picard group of a domain with normalizable gcd is trivial.
This includes unique factorization domains. -/
@[stacks 0BCH]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Picard group of a domain with normalizable gcd is trivial.
This includes unique factorization domains.
-/
instance (R) [CommRing R] [IsDomain R] [IsGCDMonoid R] : Subsingleton (Pic R) :=
  Equiv.subsingleton (ClassGroup.equivPic R).toEquiv.symm

end PicardGroup

open CommRing Pic

section Ideal

variable (R M N : Type*) [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]
variable [AddCommGroup N] [Module R N] [Module.Invertible R N]

/-- If `FractionRing R` has trivial Picard group,
every invertible `R`-module is isomorphic to an ideal. -/
/-
**Module.Invertible.exists_linearEquiv_ideal** 是 Mathlib 中的一个定理，位于命名空间 `CommRing
.Pic`。
形式化陈述：Module.Invertible.exists_linearEquiv_ideal [Subsingleton (Pic (FractionRin
g R))] : exists I : Ideal R, Nonempty (M ≃ₗ[R] I)
参数：Pic (FractionRing R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.Invertible.instFaithfulSMul`：∀ (R : Type u) (M : Type v) [inst : 
CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Modul
e.Invertible R M], Faith…
· 使用定理 `Module.Invertible.inst`：∀ {R : Type u} [inst : CommSemiring R], Module.I
nvertible R R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_unitsToPic`：Submodule.range_unitsToPic : (unitsToPic R A
).range = relPic R A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.instInvertibleSubtypeMemVal`：∀ {R : Type u} {A : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul 
R A]   (I : (Submodule R A)…
· 使用定理 `CommRing.Pic.mk_eq_mk_iff`：mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ None
mpty (M ≃ₗ[R] N)
· 使用定理 `Units.submodule_isFractional`：∀ {R : Type u_1} [inst : CommRing R] {S : 
Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   [IsLo
calization S P] (I…

--- 原说明 ---
If `FractionRing R` has trivial Picard group,
every invertible `R`-module is isomorphic to an ideal.
-/
theorem Module.Invertible.exists_linearEquiv_ideal [Subsingleton (Pic (FractionRing R))] :
    ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  have : Pic.mk R M ∈ relPic R (FractionRing R) := Subsingleton.elim ..
  have ⟨I, eq⟩ := Submodule.range_unitsToPic R (FractionRing R) ▸ this
  have ⟨e⟩ := mk_eq_mk_iff.mp eq.symm
  ⟨_, ⟨e ≪≫ₗ FractionalIdeal.equivNumOfIsLocalization
    ⟨_, I.submodule_isFractional (S := nonZeroDivisors R)⟩⟩⟩

/-- Every invertible module over a domain is isomorphic to an ideal. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every invertible module over a domain is isomorphic to an ideal.
-/
example [IsDomain R] : ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

/-- Every invertible module over a Noetherian ring is isomorphic to an ideal.
See https://mathoverflow.net/a/499611. -/
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every invertible module over a Noetherian ring is isomorphic to an ideal.
See https://mathoverflow.net/a/499611.
-/
example [IsNoetherianRing R] : ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

variable {R} in
/-- In a total ring of fractions, if two ideals are inverse to each other in the Picard group,
the only possibility is that they are both the whole ring. -/
/-
**Ideal.eq_top_of_mk_tensor_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `CommRing.Pic`。
形式化陈述：Ideal.eq_top_of_mk_tensor_eq_one [IsFractionRing R R] (I J : Ideal R) [Mod
ule.Invertible R I] [Module.Invertible R J] (h : Pic.mk R (I otimes[R] J) = 1) :
 I = ⊤ ∧ J = ⊤
参数：I J : Ideal R；h : Pic.mk R (I otimes[R] J) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Invertible.instTensorProduct_2`：∀ (R : Type u) (M : Type v) (A : 
Type u_4) [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M] [Module.Inverti…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CommRing.Pic.mk_eq_one_iff`：mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M
 ≃ₗ[R] R)
· 使用定理 `Submodule.LinearDisjoint.of_left_le_one_of_flat`：of_left_le_one_of_flat 
(h : M <= 1) [Module.Flat R N] : M.LinearDisjoint N
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Module.Invertible.instProjective`：∀ (R : Type u) (M : Type v) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.
Invertible R M], Modul…
· 使用定理 `IsFractionRing.self_iff_nonZeroDivisors_le_isUnit`：self_iff_nonZeroDivis
ors_le_isUnit : IsFractionRing R R ↔ R⁰ <= IsUnit.submonoid R
· 使用引理 `IsRegular.mem_nonZeroDivisors`：IsRegular.mem_nonZeroDivisors (h : IsRegu
lar r) : r in M₀⁰
· 使用引理 `isRightRegular_iff_isRegular`：isRightRegular_iff_isRegular : IsRightRegu
lar a ↔ IsRegular a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightRegular.eq_1`：∀ {R : Type u_1} [inst : Mul R] (c : R), IsRightReg
ular c = Function.Injective fun x => x * c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Submodule.coe_smul`：coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (
x : M)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
In a total ring of fractions, if two ideals are inverse to each other in the Pic
ard group,
the only possibility is that they are both the whole ring.
-/
theorem Ideal.eq_top_of_mk_tensor_eq_one [IsFractionRing R R] (I J : Ideal R)
    [Module.Invertible R I] [Module.Invertible R J] (h : Pic.mk R (I ⊗[R] J) = 1) :
    I = ⊤ ∧ J = ⊤ := by
  have ⟨e⟩ := mk_eq_one_iff.mp h
  have e := e.symm ≪≫ₗ Submodule.LinearDisjoint.mulMap
    (.of_left_le_one_of_flat I J <| le_top.trans one_eq_top.ge)
  have : IsUnit (e 1 : R) := IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_› <|
      IsRegular.mem_nonZeroDivisors <| isRightRegular_iff_isRegular.mp <| by
    rw [IsRightRegular]
    convert! Subtype.val_injective.comp e.injective using 2
    rw [← smul_eq_mul, ← Submodule.coe_smul, ← map_smul, smul_eq_mul, mul_one, Function.comp_apply]
  constructor <;> refine eq_top_of_isUnit_mem _ ?_ this
  exacts [mul_le_left (e 1).2, mul_le_right (e 1).2]

end Ideal

