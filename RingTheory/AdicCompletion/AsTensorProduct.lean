/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Flat.Tensor

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show (in the `AdicCompletion` namespace):

- `ofTensorProduct_bijective_of_pi_of_fintype`: it is an isomorphism if `M = R^n`.
- `ofTensorProduct_surjective_of_finite`: it is surjective, if `M` is a finite `R`-module.
- `ofTensorProduct_bijective_of_finite_of_isNoetherian`: it is an isomorphism if `R` is Noetherian
  and `M` is a finite `R`-module.

As a corollary we obtain

- `flat_of_isNoetherian`: the adic completion of a Noetherian ring `R` is `R`-flat.

## TODO

- Show that `ofTensorProduct` is an isomorphism for any finite free `R`-module over an arbitrary
  ring. This is mostly composing with the isomorphism to `R^n` and checking that the diagram
  commutes.

-/

@[expose] public section

suppress_compilation

universe u v

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

/-- The natural `AdicCompletion I R`-linear map from `AdicCompletion I R ⊗[R] M` to
the adic completion of `M`. -/
/-
**AdicCompletion.ofTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProduct : AdicCompletion I R otimes[R] M ->ₗ[AdicCompletion I R] A
dicCompletion I M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …

--- 原说明 ---
The natural `AdicCompletion I R`-linear map from `AdicCompletion I R ⊗[R] M` to
the adic completion of `M`.
-/
def ofTensorProduct : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
      map_add' x y := by
        apply LinearMap.ext
        simp
      map_smul' r x := by
        apply LinearMap.ext
        simp [mul_smul] }

@[simp]
/-
**AdicCompletion.ofTensorProduct_tmul** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`
。
形式化陈述：ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) : ofTensorProduct I 
M (r otimesₜ x) = r • of I M x
参数：r : AdicCompletion I R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  rfl

variable {M} in
/-- `ofTensorProduct` is functorial in `M`. -/
/-
**AdicCompletion.ofTensorProduct_naturality** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompl
etion`。
形式化陈述：ofTensorProduct_naturality (f : M ->ₗ[R] N) : map I f ∘ₗ ofTensorProduct I
 M = ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `AdicCompletion.ofTensorProduct_tmul`：ofTensorProduct_tmul (r : AdicCompl
etion I R) (x : M) : ofTensorProduct I M (r otimesₜ x) = r • of I M x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`ofTensorProduct` is functorial in `M`.
-/
lemma ofTensorProduct_naturality (f : M →ₗ[R] N) :
    map I f ∘ₗ ofTensorProduct I M =
      ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp

section PiFintype

/-
In this section we show that `ofTensorProduct` is an isomorphism if `M = R^n`.
-/

variable (ι : Type*)

section DecidableEq

variable [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.piEquivOfFintype_comp_ofTensorProduct_eq** 是 Mathlib 中的一个引理，位于命
名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma piEquivOfFintype_comp_ofTensorProduct_eq :
    piEquivOfFintype I (fun _ : ι ↦ R) ∘ₗ ofTensorProduct I (ι → R) =
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul]
  split <;> simp

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.ofTensorProduct_eq** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [Decidab
leEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introdu
ces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCom
pletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
private lemma ofTensorProduct_eq :
    ofTensorProduct I (ι → R) = (piEquivOfFintype I (ι := ι) (fun _ : ι ↦ R)).symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι, ← LinearMap.comp_assoc]
  simp

/-- (Implementation): If `M = R^ι` and `ι` is finite, we may construct an inverse to
`ofTensorProduct I (ι → R)`. -/
/-
**AdicCompletion.ofTensorProductInvOfPiFintype** 是 Mathlib 中的一个定义，位于命名空间 `AdicCo
mpletion`。
形式化陈述：ofTensorProductInvOfPiFintype : AdicCompletion I (ι -> R) ≃ₗ[AdicCompletio
n I R] AdicCompletion I R otimes[R] (ι -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): If `M = R^ι` and `ι` is finite, we may construct an inverse to
`ofTensorProduct I (ι → R)`.
-/
def ofTensorProductInvOfPiFintype :
    AdicCompletion I (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (ι → R) :=
  letI f := piEquivOfFintype I (fun _ : ι ↦ R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.ofTensorProductInvOfPiFintype_comp_ofTensorProduct** 是 Mathlib 
中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProductInvOfPiFintype_comp_ofTensorProduct : ofTensorProductInvOfP
iFintype I ι ∘ₗ ofTensorProduct I (ι -> R) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.AsTensorProduct.0.AdicComplet
ion.piEquivOfFintype_comp_ofTensorProduct_eq`：∀ {R : Type u_1} [inst : CommRing 
R] (I : Ideal R) (ι : Type u_4) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι],  
 ↑(AdicCompletion.piEquivO…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [Decidab
leEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introdu
ces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCom
pletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct :
    ofTensorProductInvOfPiFintype I ι ∘ₗ ofTensorProduct I (ι → R) = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, LinearMap.comp_assoc, piEquivOfFintype_comp_ofTensorProduct_eq]
  simp

/-
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [DecidableEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introduces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCompletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.ofTensorProduct_comp_ofTensorProductInvOfPiFintype** 是 Mathlib 
中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProduct_comp_ofTensorProductInvOfPiFintype : ofTensorProduct I (ι 
-> R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.AsTensorProduct.0.AdicComplet
ion.ofTensorProduct_eq`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) (ι : 
Type u_4) [inst_1 : Fintype ι] [inst_2 : DecidableEq ι],   AdicCompletion.ofTens
orPr…
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
import Mathlib.RingTheory.AdicCompletion.Algebra

variable {R : Type*} [CommRing R] (I : Ideal R) (ι : Type*) [Fintype ι] [Decidab
leEq ι]

-- `AdicCompletion.module` has type `Module X Y → Module (F X) (F Y)` so introdu
ces
-- diamonds if `X = Y`.
example : AdicCompletion.module I = Semiring.toModule := by
  fail_if_success with_reducible_and_instances rfl
  rfl

example : ((AdicCompletion.module I).toSMul : SMul (AdicCompletion I R) (AdicCom
pletion I R)) =
    Semiring.toModule.toSMul := by
  fail_if_success with_reducible_and_instances rfl
  rfl
-/
lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype :
    ofTensorProduct I (ι → R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, ofTensorProduct_eq, LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

/-- `ofTensorProduct` as an equiv in the case of `M = R^ι` where `ι` is finite. -/
/-
**AdicCompletion.ofTensorProductEquivOfPiFintype** 是 Mathlib 中的一个定义，位于命名空间 `Adic
Completion`。
形式化陈述：ofTensorProductEquivOfPiFintype : AdicCompletion I R otimes[R] (ι -> R) ≃ₗ
[AdicCompletion I R] AdicCompletion I (ι -> R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.ofTensorProduct_comp_ofTensorProductInvOfPiFintype`：ofTen
sorProduct_comp_ofTensorProductInvOfPiFintype : ofTensorProduct I (ι -> R) ∘ₗ of
TensorProductInvOfPiFintype I ι = LinearMap.id
· 使用引理 `AdicCompletion.ofTensorProductInvOfPiFintype_comp_ofTensorProduct`：ofTen
sorProductInvOfPiFintype_comp_ofTensorProduct : ofTensorProductInvOfPiFintype I 
ι ∘ₗ ofTensorProduct I (ι -> R) = LinearMap.id

--- 原说明 ---
`ofTensorProduct` as an equiv in the case of `M = R^ι` where `ι` is finite.
-/
def ofTensorProductEquivOfPiFintype :
    AdicCompletion I R ⊗[R] (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (ι → R) :=
  LinearEquiv.ofLinearMap
    (ofTensorProduct I (ι → R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)

end DecidableEq

/-- If `M = R^ι`, `ofTensorProduct` is bijective. -/
/-
**AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype** 是 Mathlib 中的一个引理，位
于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProduct_bijective_of_pi_of_fintype [Finite ι] : Function.Bijective
 (ofTensorProduct I (ι -> R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e

--- 原说明 ---
If `M = R^ι`, `ofTensorProduct` is bijective.
-/
lemma ofTensorProduct_bijective_of_pi_of_fintype [Finite ι] :
    Function.Bijective (ofTensorProduct I (ι → R)) := by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)

end PiFintype

/-- If `M` is a finite `R`-module, then the canonical map
`AdicCompletion I R ⊗[R] M →ₗ AdicCompletion I M` is surjective. -/
/-
**AdicCompletion.ofTensorProduct_surjective_of_finite** 是 Mathlib 中的一个引理，位于命名空间 
`AdicCompletion`。
形式化陈述：ofTensorProduct_surjective_of_finite [Module.Finite R M] : Function.Surjec
tive (ofTensorProduct I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `AdicCompletion.ofTensorProduct_tmul`：ofTensorProduct_tmul (r : AdicCompl
etion I R) (x : M) : ofTensorProduct I M (r otimesₜ x) = r • of I M x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `AdicCompletion.map_surjective`：map_surjective (hf : Function.Surjective 
f) : Function.Surjective (map I f)
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用引理 `AdicCompletion.ofTensorProduct_bijective_of_pi_of_fintype`：ofTensorProdu
ct_bijective_of_pi_of_fintype [Finite ι] : Function.Bijective (ofTensorProduct I
 (ι -> R))
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f

--- 原说明 ---
If `M` is a finite `R`-module, then the canonical map
`AdicCompletion I R ⊗[R] M →ₗ AdicCompletion I M` is surjective.
-/
lemma ofTensorProduct_surjective_of_finite [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_comp, g]
    apply Function.Surjective.comp
    · exact AdicCompletion.map_surjective I hp
    · exact (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).surjective
  exact Function.Surjective.of_comp hf

section Noetherian

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-!

### Noetherian case

Suppose `R` is Noetherian. Then we show that the canonical map
`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M` is an isomorphism for every
finite `R`-module `M`.

The strategy is the following: Choose a surjection `f : (ι → R) →ₗ[R] M` and consider the following
commutative diagram:

```
 AdicCompletion I R ⊗[R] ker f -→ AdicCompletion I R ⊗[R] (ι → R) -→ AdicCompletion I R ⊗[R] M -→ 0
               |                             |                                 |                  |
               ↓                             ↓                                 ↓                  ↓
    AdicCompletion I (ker f) ------→ AdicCompletion I (ι → R) -------→ AdicCompletion I M ------→ 0
```

The vertical maps are given by `ofTensorProduct`. By the previous section we know that the second
vertical map is an isomorphism. Since `R` is Noetherian, `ker f` is finitely-generated, so again
by the previous section the first vertical map is surjective.

Moreover, both rows are exact by right-exactness of the tensor product and exactness of adic
completions over Noetherian rings. Hence we conclude by the 5-lemma.

-/

open CategoryTheory

section

variable {ι : Type} (f : (ι → R) →ₗ[R] M)

/-- The first horizontal arrow in the top row. -/
private
/-
**AdicCompletion.lTensorKerIncl** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：lTensorKerIncl : AdicCompletion I R otimes[R] LinearMap.ker f ->ₗ[AdicComp
letion I R] AdicCompletion I R otimes[R] (ι -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lTensorKerIncl : AdicCompletion I R ⊗[R] LinearMap.ker f →ₗ[AdicCompletion I R]
    AdicCompletion I R ⊗[R] (ι → R) :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype

/-- The second horizontal arrow in the top row. -/
/-
**AdicCompletion.lTensorf** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second horizontal arrow in the top row.
-/
private def lTensorf :
    AdicCompletion I R ⊗[R] (ι → R) →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] M :=
  AlgebraTensorModule.map LinearMap.id f

variable (hf : Function.Surjective f)

include hf
/-
**AdicCompletion.tens_exact** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tens_exact : Function.Exact (lTensorKerIncl I M f) (lTensorf I M f) :=
  lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf
/-
**AdicCompletion.tens_surj** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tens_surj : Function.Surjective (lTensorf I M f) :=
  LinearMap.lTensor_surjective (AdicCompletion I R) hf
/-
**AdicCompletion.adic_exact** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma adic_exact [IsNoetherianRing R] [Finite ι] :
    Function.Exact (map I (LinearMap.ker f).subtype) (map I f) :=
  map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf
/-
**AdicCompletion.adic_surj** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma adic_surj : Function.Surjective (map I f) :=
  map_surjective I hf

private
/-
**AdicCompletion.ofTensorProduct_bijective_of_map_from_fin** 是 Mathlib 中的一个引理，位于
命名空间 `AdicCompletion`。
形式化陈述：ofTensorProduct_bijective_of_map_from_fin [Finite ι] [IsNoetherianRing R] 
: Function.Bijective (ofTensorProduct I M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofTensorProduct_bijective_of_map_from_fin [Finite ι] [IsNoetherianRing R] :
    Function.Bijective (ofTensorProduct I M) :=
  LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (lTensorKerIncl I M f)
    (lTensorf I M f)
    (0 : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] Unit)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (map I <| (LinearMap.ker f).subtype)
    (map I f)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (0 : _ →ₗ[AdicCompletion I R] Unit)
    (ofTensorProduct I (LinearMap.ker f))
    (ofTensorProduct I (ι → R))
    (ofTensorProduct I M)
    0
    0
    (ofTensorProduct_naturality I <| (LinearMap.ker f).subtype)
    (ofTensorProduct_naturality I f)
    rfl
    rfl
    (tens_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| tens_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (adic_exact I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| adic_surj I M f hf)
    ((LinearMap.exact_zero_iff_surjective _ _).mpr <| Function.surjective_to_subsingleton _)
    (ofTensorProduct_surjective_of_finite I (LinearMap.ker f))
    (ofTensorProduct_bijective_of_pi_of_fintype I ι)
    (Function.bijective_of_subsingleton _)
    (Function.injective_of_subsingleton _)

end

variable [IsNoetherianRing R]

/-- If `R` is a Noetherian ring and `M` is a finite `R`-module, then the natural map
given by `AdicCompletion.ofTensorProduct` is an isomorphism. -/
/-
**AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian** 是 Mathlib
 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProduct_bijective_of_finite_of_isNoetherian [Module.Finite R M] : 
Function.Bijective (ofTensorProduct I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `_private.Mathlib.RingTheory.AdicCompletion.AsTensorProduct.0.AdicComplet
ion.ofTensorProduct_bijective_of_map_from_fin`：∀ {R : Type u} [inst : CommRing R
] (I : Ideal R) (M : Type u) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R
 M]   {ι : Type} (f : (ι → …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `R` is a Noetherian ring and `M` is a finite `R`-module, then the natural map
given by `AdicCompletion.ofTensorProduct` is an isomorphism.
-/
theorem ofTensorProduct_bijective_of_finite_of_isNoetherian
    [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

/-- `ofTensorProduct` packaged as linear equiv if `M` is a finite `R`-module and `R` is
Noetherian. -/
/-
**AdicCompletion.ofTensorProductEquivOfFiniteNoetherian** 是 Mathlib 中的一个定义，位于命名空
间 `AdicCompletion`。
形式化陈述：ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] : AdicCompletio
n I R otimes[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian`：ofTe
nsorProduct_bijective_of_finite_of_isNoetherian [Module.Finite R M] : Function.B
ijective (ofTensorProduct I M)

--- 原说明 ---
`ofTensorProduct` packaged as linear equiv if `M` is a finite `R`-module and `R`
 is
Noetherian.
-/
def ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)
/-
**AdicCompletion.coe_ofTensorProductEquivOfFiniteNoetherian** 是 Mathlib 中的一个引理，位
于命名空间 `AdicCompletion`。
形式化陈述：coe_ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] : ofTensorP
roductEquivOfFiniteNoetherian I M = ofTensorProduct I M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma coe_ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    ofTensorProductEquivOfFiniteNoetherian I M = ofTensorProduct I M :=
  rfl

@[simp]
/-
**AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply** 是 Mathlib 中的一个引理
，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProductEquivOfFiniteNoetherian_apply [Module.Finite R M] (x : Adic
Completion I R otimes[R] M) : ofTensorProductEquivOfFiniteNoetherian I M x = ofT
ensorProduct I M x
参数：x : AdicCompletion I R otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma ofTensorProductEquivOfFiniteNoetherian_apply [Module.Finite R M]
    (x : AdicCompletion I R ⊗[R] M) :
    ofTensorProductEquivOfFiniteNoetherian I M x = ofTensorProduct I M x :=
  rfl

@[simp]
/-
**AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of** 是 Mathlib 中的一个
引理，位于命名空间 `AdicCompletion`。
形式化陈述：ofTensorProductEquivOfFiniteNoetherian_symm_of [Module.Finite R M] (x : M)
 : (ofTensorProductEquivOfFiniteNoetherian I M).symm ((of I M) x) = 1 otimesₜ x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AdicCompletion.ofTensorProduct_tmul`：ofTensorProduct_tmul (r : AdicCompl
etion I R) (x : M) : ofTensorProduct I M (r otimesₜ x) = r • of I M x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
lemma ofTensorProductEquivOfFiniteNoetherian_symm_of
    [Module.Finite R M] (x : M) :
    (ofTensorProductEquivOfFiniteNoetherian I M).symm ((of I M) x) = 1 ⊗ₜ x := by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 ⊗ₜ x) := by
    simp
  rw [h, LinearEquiv.symm_apply_apply]

section

variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
variable [Module.Finite R M] [Module.Finite R N]

/-
**AdicCompletion.tensor_map_id_left_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `AdicComple
tion`。
形式化陈述：tensor_map_id_left_eq_map : (AlgebraTensorModule.map LinearMap.id f) = (of
TensorProductEquivOfFiniteNoetherian I N).symm.toLinearMap ∘ₗ map I f ∘ₗ (ofTens
orProductEquivOfFiniteNoetherian I M).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AdicCompletion.coe_ofTensorProductEquivOfFiniteNoetherian`：coe_ofTensorP
roductEquivOfFiniteNoetherian [Module.Finite R M] : ofTensorProductEquivOfFinite
Noetherian I M = ofTensorProduct I M
· 使用引理 `AdicCompletion.ofTensorProduct_naturality`：ofTensorProduct_naturality (f
 : M ->ₗ[R] N) : map I f ∘ₗ ofTensorProduct I M = ofTensorProduct I N ∘ₗ Algebra
TensorModule.map LinearMap.id f
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `AdicCompletion.instIsScalarTower_1`：∀ {R : Type u_1} [inst : CommRing R]
 (I : Ideal R) {M : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M], IsScalarTower R …
· 使用引理 `AdicCompletion.ofTensorProduct_tmul`：ofTensorProduct_tmul (r : AdicCompl
etion I R) (x : M) : ofTensorProduct I M (r otimesₜ x) = r • of I M x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of`：ofTensorP
roductEquivOfFiniteNoetherian_symm_of [Module.Finite R M] (x : M) : (ofTensorPro
ductEquivOfFiniteNoetherian I M).symm ((of I M) x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensor_map_id_left_eq_map :
    (AlgebraTensorModule.map LinearMap.id f) =
      (ofTensorProductEquivOfFiniteNoetherian I N).symm.toLinearMap ∘ₗ
      map I f ∘ₗ
      (ofTensorProductEquivOfFiniteNoetherian I M).toLinearMap := by
  rw [coe_ofTensorProductEquivOfFiniteNoetherian, ofTensorProduct_naturality I f]
  ext x
  simp

variable {f}
/-
**AdicCompletion.tensor_map_id_left_injective_of_injective** 是 Mathlib 中的一个引理，位于
命名空间 `AdicCompletion`。
形式化陈述：tensor_map_id_left_injective_of_injective (hf : Function.Injective f) : Fu
nction.Injective (AlgebraTensorModule.map LinearMap.id f : AdicCompletion I R ot
imes[R] M ->ₗ[AdicCompletion I R] AdicCompletion I R otimes[R] N)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AdicCompletion.tensor_map_id_left_eq_map`：tensor_map_id_left_eq_map : (A
lgebraTensorModule.map LinearMap.id f) = (ofTensorProductEquivOfFiniteNoetherian
 I N).symm.toLinearMap ∘ₗ map …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AdicCompletion.map_injective`：map_injective {f : M ->ₗ[R] N} (hf : Funct
ion.Injective f) : Function.Injective (map I f)
-/
lemma tensor_map_id_left_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map LinearMap.id f :
        AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] N) := by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf

end

/-- Adic completion of a Noetherian ring `R` is flat over `R`. -/
/-
**AdicCompletion.flat_of_isNoetherian** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`
。
形式化陈述：flat_of_isNoetherian : Module.Flat R (AdicCompletion I R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Flat.iff_lTensor_injective'`：iff_lTensor_injective' : Flat R M ↔ 
forall (I : Ideal R), Function.Injective (lTensor M I.subtype)
· 使用引理 `AdicCompletion.tensor_map_id_left_injective_of_injective`：tensor_map_id_
left_injective_of_injective (hf : Function.Injective f) : Function.Injective (Al
gebraTensorModule.map LinearMap.id f : AdicCom…
· 使用定理 `Module.instFiniteSubtypeMemIdealOfIsNoetherian`：∀ {R₁ : Type u_5} {S : T
ype u_6} [inst : CommSemiring R₁] [inst_1 : Semiring S] [inst_2 : Algebra R₁ S] 
  [IsNoetherian R₁ S] (I : Ideal S),…
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype

--- 原说明 ---
Adic completion of a Noetherian ring `R` is flat over `R`.
-/
instance flat_of_isNoetherian : Module.Flat R (AdicCompletion I R) :=
  Module.Flat.iff_lTensor_injective'.mpr fun J ↦
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)

end Noetherian

end AdicCompletion

