/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

@[expose] public section

variable {ι : Type*} (R M N P Q : Type*)

-- Enable extensionality of maps out of the tensor product.
-- High priority so it takes precedence over `LinearMap.ext`.
attribute [local ext high] TensorProduct.ext

section Contraction

open TensorProduct LinearMap Matrix Module

open TensorProduct

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable (b : Basis ι R M)

/-- The natural left-handed pairing between a module and its dual. -/
/-
**contractLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：contractLeft : Module.Dual R M otimes[R] M ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural left-handed pairing between a module and its dual.
-/
def contractLeft : Module.Dual R M ⊗[R] M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

/-- The natural right-handed pairing between a module and its dual. -/
/-
**contractRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：contractRight : M otimes[R] Module.Dual R M ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural right-handed pairing between a module and its dual.
-/
def contractRight : M ⊗[R] Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
/-
**dualTensorHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dualTensorHom : Module.Dual R M otimes[R] N ->ₗ[R] M ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map associating a linear map to the tensor product of two modules.
-/
def dualTensorHom : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry (.id R) M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

variable {R M N P Q}

@[simp]
/-
**contractLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f oti
mesₜ m) = f m
参数：f : Module.Dual R M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem contractLeft_apply (f : Module.Dual R M) (m : M) : contractLeft R M (f ⊗ₜ m) = f m :=
  rfl

@[simp]
/-
**contractRight_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contractRight_apply (f : Module.Dual R M) (m : M) : contractRight R M (m o
timesₜ f) = f m
参数：f : Module.Dual R M；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem contractRight_apply (f : Module.Dual R M) (m : M) : contractRight R M (m ⊗ₜ f) = f m :=
  rfl

@[simp]
/-
**dualTensorHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_apply (f : Module.Dual R M) (m : M) (n : N) : dualTensorHom 
R M N (f otimesₜ n) m = f m • n
参数：f : Module.Dual R M；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualTensorHom_apply (f : Module.Dual R M) (m : M) (n : N) :
    dualTensorHom R M N (f ⊗ₜ n) m = f m • n :=
  rfl
/-
**dualTensorHom_comp_lTensor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_comp_lTensor (f : N ->ₗ[R] P) : dualTensorHom R M P ∘ₗ f.lTe
nsor _ = f.compRight R ∘ₗ dualTensorHom R M N
参数：f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualTensorHom_comp_lTensor (f : N →ₗ[R] P) :
    dualTensorHom R M P ∘ₗ f.lTensor _ = f.compRight R ∘ₗ dualTensorHom R M N := by
  ext; simp
/-
**dualTensorHom_comp_rTensor_dualMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_comp_rTensor_dualMap (f : M ->ₗ[R] N) : dualTensorHom R M P 
∘ₗ f.dualMap.rTensor _ = f.lcomp R P ∘ₗ dualTensorHom R N P
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualTensorHom_comp_rTensor_dualMap (f : M →ₗ[R] N) :
    dualTensorHom R M P ∘ₗ f.dualMap.rTensor _ = f.lcomp R P ∘ₗ dualTensorHom R N P := by
  ext; simp

@[simp]
/-
**transpose_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：transpose_dualTensorHom (f : Module.Dual R M) (m : M) : Dual.transpose (R
参数：f : Module.Dual R M；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem transpose_dualTensorHom (f : Module.Dual R M) (m : M) :
    Dual.transpose (R := R) (dualTensorHom R M M (f ⊗ₜ m)) =
    dualTensorHom R _ _ (Dual.eval R M m ⊗ₜ f) := by
  ext f' m'
  simp only [Dual.transpose_apply, coe_comp, Function.comp_apply, dualTensorHom_apply,
    map_smulₛₗ, RingHom.id_apply, smul_eq_mul, Dual.eval_apply,
    LinearMap.smul_apply]
  exact mul_comm _ _

@[simp]
/-
**dualTensorHom_prodMap_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_prodMap_zero (f : Module.Dual R M) (p : P) : ((dualTensorHom
 R M P) (f otimesₜ[R] p)).prodMap (0 : N ->ₗ[R] Q) = dualTensorHom R (M × N) (P 
× Q) ((f ∘ₗ fst R M N) otimesₜ inl R P Q p)
参数：f : Module.Dual R M；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualTensorHom_prodMap_zero (f : Module.Dual R M) (p : P) :
    ((dualTensorHom R M P) (f ⊗ₜ[R] p)).prodMap (0 : N →ₗ[R] Q) =
      dualTensorHom R (M × N) (P × Q) ((f ∘ₗ fst R M N) ⊗ₜ inl R P Q p) := by
  ext <;>
    simp only [coe_comp, coe_inl, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      fst_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

@[simp]
/-
**zero_prodMap_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_prodMap_dualTensorHom (g : Module.Dual R N) (q : Q) : (0 : M ->ₗ[R] P
).prodMap ((dualTensorHom R N Q) (g otimesₜ[R] q)) = dualTensorHom R (M × N) (P 
× Q) ((g ∘ₗ snd R M N) otimesₜ inr R P Q q)
参数：g : Module.Dual R N；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_prodMap_dualTensorHom (g : Module.Dual R N) (q : Q) :
    (0 : M →ₗ[R] P).prodMap ((dualTensorHom R N Q) (g ⊗ₜ[R] q)) =
      dualTensorHom R (M × N) (P × Q) ((g ∘ₗ snd R M N) ⊗ₜ inr R P Q q) := by
  ext <;>
    simp only [coe_comp, coe_inr, Function.comp_apply, prodMap_apply, dualTensorHom_apply,
      snd_apply, Prod.smul_mk, LinearMap.zero_apply, smul_zero]

attribute [-ext] AlgebraTensorModule.curry_injective in
/-
**map_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q :
 Q) : TensorProduct.map (dualTensorHom R M P (f otimesₜ[R] p)) (dualTensorHom R 
N Q (g otimesₜ[R] q)) = dualTensorHom R (M otimes[R] N) (P otimes[R] Q) (dualDis
trib R M N (f otimesₜ g) otimesₜ[R] (p otimesₜ[R] q))
参数：f : Module.Dual R M；p : P；g : Module.Dual R N；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_dualTensorHom (f : Module.Dual R M) (p : P) (g : Module.Dual R N) (q : Q) :
    TensorProduct.map (dualTensorHom R M P (f ⊗ₜ[R] p)) (dualTensorHom R N Q (g ⊗ₜ[R] q)) =
      dualTensorHom R (M ⊗[R] N) (P ⊗[R] Q) (dualDistrib R M N (f ⊗ₜ g) ⊗ₜ[R] (p ⊗ₜ[R] q)) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, dualTensorHom_apply, dualDistrib_apply,
    ← smul_tmul_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**comp_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p 
: P) : dualTensorHom R N P (g otimesₜ[R] p) ∘ₗ dualTensorHom R M N (f otimesₜ[R]
 n) = g n • dualTensorHom R M P (f otimesₜ p)
参数：f : Module.Dual R M；n : N；g : Module.Dual R N；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem comp_dualTensorHom (f : Module.Dual R M) (n : N) (g : Module.Dual R N) (p : P) :
    dualTensorHom R N P (g ⊗ₜ[R] p) ∘ₗ dualTensorHom R M N (f ⊗ₜ[R] n) =
      g n • dualTensorHom R M P (f ⊗ₜ p) := by
  ext m
  simp only [coe_comp, Function.comp_apply, dualTensorHom_apply, map_smul, LinearMap.smul_apply]
  rw [smul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- As a matrix, `dualTensorHom` evaluated on a basis element of `M* ⊗ N` is a matrix with a
single one and zeros elsewhere -/
/-
**toMatrix_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Finite n] [Dec
idableEq m] [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n
) : toMatrix bM bN (dualTensorHom R M N (bM.coord j otimesₜ bN i)) = single i j 
1
参数：bM : Basis m R M；bN : Basis n R N；j : m；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Matrix.single.congr_simp`：∀ {m : Type u_2} {n : Type u_3} {α : Type u_7}
 {inst : DecidableEq m} [inst_1 : DecidableEq m] {inst_2 : DecidableEq n}   [ins
t_3 : Decidabl…
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `and_iff_not_or_not`：and_iff_not_or_not : a ∧ b ↔ ¬(¬a ∨ ¬b)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
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
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
As a matrix, `dualTensorHom` evaluated on a basis element of `M* ⊗ N` is a matri
x with a
single one and zeros elsewhere
-/
theorem toMatrix_dualTensorHom {m : Type*} {n : Type*} [Fintype m] [Finite n] [DecidableEq m]
    [DecidableEq n] (bM : Basis m R M) (bN : Basis n R N) (j : m) (i : n) :
    toMatrix bM bN (dualTensorHom R M N (bM.coord j ⊗ₜ bN i)) = single i j 1 := by
  ext i' j'
  by_cases hij : i = i' ∧ j = j'
  · simp [LinearMap.toMatrix_apply, hij]
  · rw [and_iff_not_or_not, Classical.not_not] at hij
    rcases hij with hij | hij <;> simp [LinearMap.toMatrix_apply, Finsupp.single_eq_pi_single, hij]

section

variable (h : 1 ∈ (dualTensorHom R M M).range)
include h

/-
**finite_projective_of_one_mem_range_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem finite_projective_of_one_mem_range_dualTensorHom :
    Module.Finite R M ∧ Projective R M := by
  have ⟨t, eq⟩ := h
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  let f : (s → R) →ₗ[R] M := Fintype.linearCombination R (·.1.2)
  have : f ∘ₗ pi (·.1.1) = 1 := by
    ext; simp [f, ← eq, Fintype.linearCombination_apply, ← s.sum_coe_sort]
  exact ⟨.of_surjective f (surjective_of_comp_eq_id _ _ this), .of_split _ f this⟩

/-- If the identity linear map lies in the range of the canonical map `M* ⊗[R] M → Hom_R(M, M)`,
then `M` is a finite projective `R`-module (finite part). -/
/-
**Module.Finite.of_one_mem_range_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.of_one_mem_range_dualTensorHom : Module.Finite R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.LinearAlgebra.Contraction.0.finite_projective_of_one_me
m_range_dualTensorHom`：∀ {R : Type u_2} {M : Type u_3} [inst : CommSemiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   1 ∈ (dualTensorHom R M
 M)…

--- 原说明 ---
If the identity linear map lies in the range of the canonical map `M* ⊗[R] M → H
om_R(M, M)`,
then `M` is a finite projective `R`-module (finite part).
-/
theorem Module.Finite.of_one_mem_range_dualTensorHom : Module.Finite R M :=
  (finite_projective_of_one_mem_range_dualTensorHom h).1

/-- If the identity linear map lies in the range of the canonical map `M* ⊗[R] M → Hom_R(M, M)`,
then `M` is a finite projective `R`-module (projective part). -/
/-
**Module.Projective.of_one_mem_range_dualTensorHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Projective.of_one_mem_range_dualTensorHom : Module.Projective R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.LinearAlgebra.Contraction.0.finite_projective_of_one_me
m_range_dualTensorHom`：∀ {R : Type u_2} {M : Type u_3} [inst : CommSemiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   1 ∈ (dualTensorHom R M
 M)…

--- 原说明 ---
If the identity linear map lies in the range of the canonical map `M* ⊗[R] M → H
om_R(M, M)`,
then `M` is a finite projective `R`-module (projective part).
-/
theorem Module.Projective.of_one_mem_range_dualTensorHom : Module.Projective R M :=
  (finite_projective_of_one_mem_range_dualTensorHom h).2

end

section Fintype

variable [DecidableEq ι] [Fintype ι]

attribute [-ext] AlgebraTensorModule.curry_injective in
/-- If `M` is free, the natural linear map $M^* ⊗ N → Hom(M, N)$ is an equivalence. This function
provides this equivalence in return for a basis of `M`. -/
-- We manually create simp-lemmas because `@[simps]` generates a malformed lemma
/-
**dualTensorHomEquivOfBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dualTensorHomEquivOfBasis : Module.Dual R M otimes[R] N ≃ₗ[R] M ->ₗ[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
noncomputable def dualTensorHomEquivOfBasis : Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  LinearEquiv.ofLinearMap (dualTensorHom R M N)
    (∑ i, TensorProduct.mk R _ N (b.dualBasis i) ∘ₗ (LinearMap.applyₗ (R := R) (b i)))
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, Basis.coord_apply, ←
        f.map_smul, _root_.map_sum (dualTensorHom R M N), ← _root_.map_sum f, b.sum_repr])
    (by
      ext f m
      simp only [applyₗ_apply_apply, coe_sum, dualTensorHom_apply, mk_apply, id_coe, _root_.id,
        Fintype.sum_apply, Function.comp_apply, Basis.coe_dualBasis, coe_comp, compr₂ₛₗ_apply,
        tmul_smul, smul_tmul', ← sum_tmul, Basis.sum_dual_apply_smul_coord])
/-
**coe_dualTensorHomEquivOfBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_dualTensorHomEquivOfBasis : ⇑(dualTensorHomEquivOfBasis (N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem coe_dualTensorHomEquivOfBasis :
    ⇑(dualTensorHomEquivOfBasis (N := N) b) = dualTensorHom R M N := rfl

@[simp]
/-
**dualTensorHomEquivOfBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHomEquivOfBasis_apply (x : Module.Dual R M otimes[R] N) : dualTe
nsorHomEquivOfBasis b x = dualTensorHom R M N x
参数：x : Module.Dual R M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualTensorHomEquivOfBasis_apply (x : Module.Dual R M ⊗[R] N) :
    dualTensorHomEquivOfBasis b x = dualTensorHom R M N x :=
  rfl

@[simp]
/-
**dualTensorHomEquivOfBasis_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHomEquivOfBasis_toLinearMap : (dualTensorHomEquivOfBasis b).toLi
nearMap = dualTensorHom R M N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem dualTensorHomEquivOfBasis_toLinearMap :
    (dualTensorHomEquivOfBasis b).toLinearMap = dualTensorHom R M N :=
  rfl

@[simp]
/-
**dualTensorHomEquivOfBasis_symm_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHomEquivOfBasis_symm_cancel_left (x : Module.Dual R M otimes[R] 
N) : (dualTensorHomEquivOfBasis b).symm (dualTensorHom R M N x) = x
参数：x : Module.Dual R M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dualTensorHomEquivOfBasis_apply`：dualTensorHomEquivOfBasis_apply (x : Mo
dule.Dual R M otimes[R] N) : dualTensorHomEquivOfBasis b x = dualTensorHom R M N
 x
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem dualTensorHomEquivOfBasis_symm_cancel_left (x : Module.Dual R M ⊗[R] N) :
    (dualTensorHomEquivOfBasis b).symm (dualTensorHom R M N x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b,
    LinearEquiv.symm_apply_apply <| dualTensorHomEquivOfBasis (N := N) b]

@[simp]
/-
**dualTensorHomEquivOfBasis_symm_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHomEquivOfBasis_symm_cancel_right (x : M ->ₗ[R] N) : dualTensorH
om R M N ((dualTensorHomEquivOfBasis b).symm x) = x
参数：x : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dualTensorHomEquivOfBasis_apply`：dualTensorHomEquivOfBasis_apply (x : Mo
dule.Dual R M otimes[R] N) : dualTensorHomEquivOfBasis b x = dualTensorHom R M N
 x
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem dualTensorHomEquivOfBasis_symm_cancel_right (x : M →ₗ[R] N) :
    dualTensorHom R M N ((dualTensorHomEquivOfBasis b).symm x) = x := by
  rw [← dualTensorHomEquivOfBasis_apply b, LinearEquiv.apply_symm_apply]

end Fintype

/-
**dualTensorHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_bijective [Module.Finite R M] [Projective R M] : Function.Bi
jective (dualTensorHom R M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.exists_comp_eq_id_of_projective`：exists_comp_eq_id_of_proj
ective [Module.Finite R M] [Projective R M] : exists (n : Nat) (f : (Fin n -> R)
 ->ₗ[R] M) (g : M ->ₗ[R] Fin n -> R…
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `dualTensorHom_comp_rTensor_dualMap`：dualTensorHom_comp_rTensor_dualMap (
f : M ->ₗ[R] N) : dualTensorHom R M P ∘ₗ f.dualMap.rTensor _ = f.lcomp R P ∘ₗ du
alTensorHom R N P
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `coe_dualTensorHomEquivOfBasis`：coe_dualTensorHomEquivOfBasis : ⇑(dualTen
sorHomEquivOfBasis (N
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.dualMap_id`：LinearMap.dualMap_id : (LinearMap.id : M₁ ->ₗ[R] M
₁).dualMap = LinearMap.id
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
theorem dualTensorHom_bijective [Module.Finite R M] [Projective R M] :
    Function.Bijective (dualTensorHom R M N) := by
  obtain ⟨n, f, g, -, -, eq⟩ := Finite.exists_comp_eq_id_of_projective R M
  constructor
  · refine .of_comp (f := f.lcomp R N) ?_
    rw [← coe_comp, ← dualTensorHom_comp_rTensor_dualMap, coe_comp,
      ← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (EquivLike.injective _).comp (injective_of_comp_eq_id _ (rTensor _ g.dualMap) ?_)
    simp [← rTensor_comp, dualMap_comp_dualMap g f, eq]
  · refine .of_comp (g := g.dualMap.rTensor N) ?_
    rw [← coe_comp, dualTensorHom_comp_rTensor_dualMap, coe_comp,
      ← coe_dualTensorHomEquivOfBasis (Pi.basisFun ..)]
    refine (surjective_of_comp_eq_id (f.lcomp R N) _ ?_).comp (EquivLike.surjective _)
    ext φ; exact congr(φ ($eq _))
/-
**dualTensorHom_self_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_self_right : dualTensorHom R M R = TensorProduct.rid R (Dual
 R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualTensorHom_self_right : dualTensorHom R M R = TensorProduct.rid R (Dual R M) := by
  ext; simp

/- Subsumed by `dualTensorHom_bijective_of_finite_projective_right`. -/
/-
**dualTensorHom_self_right_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subsumed by `dualTensorHom_bijective_of_finite_projective_right`.
-/
private theorem dualTensorHom_self_right_bijective : Function.Bijective (dualTensorHom R M R) := by
  simpa only [dualTensorHom_self_right] using! LinearEquiv.bijective _
/-
**dualTensorHom_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_finsupp [DecidableEq ι] : dualTensorHom R M (ι ->₀ N) = .fin
suppLinearMap R ∘ₗ Finsupp.mapRange.linearMap (dualTensorHom R M N) ∘ₗ (finsuppR
ight R R _ N ι).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用引理 `TensorProduct.finsuppRight_tmul_single`：finsuppRight_tmul_single (i : ι)
 (m : M) (n : N) : finsuppRight R S M N ι (m otimesₜ[R] Finsupp.single i n) = Fi
nsupp.single i (m otimesₜ[R]…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `LinearMap.finsuppLinearMap_apply_apply_apply`：∀ {R : Type u_1} {M : Type
 u_2} {N : Type u_3} {ι : Type u_4} (S : Type u_5) [inst : Semiring R]   [inst_1
 : AddCommMonoid M] [inst_2 : AddC…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem dualTensorHom_finsupp [DecidableEq ι] :
    dualTensorHom R M (ι →₀ N) = .finsuppLinearMap R ∘ₗ
      Finsupp.mapRange.linearMap (dualTensorHom R M N) ∘ₗ (finsuppRight R R _ N ι).toLinearMap := by
  ext; simp [Finsupp.single_apply]; aesop
/-
**dualTensorHom_finsupp_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_finsupp_bijective (fin : Finite ι ∨ Module.Finite R M) (h : 
Function.Bijective (dualTensorHom R M N)) : Function.Bijective (dualTensorHom R 
M (ι ->₀ N))
参数：fin : Finite ι ∨ Module.Finite R M；h : Function.Bijective (dualTensorHom R M 
N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dualTensorHom_finsupp`：dualTensorHom_finsupp [DecidableEq ι] : dualTenso
rHom R M (ι ->₀ N) = .finsuppLinearMap R ∘ₗ Finsupp.mapRange.linearMap (dualTens
orHom R M N…
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `LinearMap.finsuppLinearMap_bijective_of_finite`：finsuppLinearMap_bijecti
ve_of_finite [Finite ι] : Function.Bijective (finsuppLinearMap S : (ι ->₀ M ->ₗ[
R] N) -> M ->ₗ[R] ι ->₀ N) where lef…
· 使用定理 `LinearMap.finsuppLinearMap_bijective_of_moduleFinite`：finsuppLinearMap_b
ijective_of_moduleFinite [Module.Finite R M] : Function.Bijective (finsuppLinear
Map S : (ι ->₀ M ->ₗ[R] N) -> M ->ₗ[R] ι -…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Finsupp.mapRange_bijective`：mapRange_bijective (e : M -> N) (he₀ : e 0 =
 0) (he : Bijective e) : Bijective (Finsupp.mapRange (α
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem dualTensorHom_finsupp_bijective (fin : Finite ι ∨ Module.Finite R M)
    (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι →₀ N)) := by
  classical rw [dualTensorHom_finsupp, coe_comp]
  refine .comp ?_ ((Finsupp.mapRange_bijective _ (map_zero _) h).comp (LinearEquiv.bijective _))
  cases fin
  · apply finsuppLinearMap_bijective_of_finite
  · apply finsuppLinearMap_bijective_of_moduleFinite
/-
**dualTensorHom_bijective_of_comp_eq_id_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_bijective_of_comp_eq_id_right (f : N ->ₗ[R] P) (g : P ->ₗ[R]
 N) (comp_eq_id : g ∘ₗ f = .id) (h : Function.Bijective (dualTensorHom R M P)) :
 Function.Bijective (dualTensorHom R M N) where left
参数：f : N ->ₗ[R] P；g : P ->ₗ[R] N；comp_eq_id : g ∘ₗ f = .id；h : Function.Bijectiv
e (dualTensorHom R M P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `dualTensorHom_comp_lTensor`：dualTensorHom_comp_lTensor (f : N ->ₗ[R] P) 
: dualTensorHom R M P ∘ₗ f.lTensor _ = f.compRight R ∘ₗ dualTensorHom R M N
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dualTensorHom_bijective_of_comp_eq_id_right (f : N →ₗ[R] P) (g : P →ₗ[R] N)
    (comp_eq_id : g ∘ₗ f = .id) (h : Function.Bijective (dualTensorHom R M P)) :
    Function.Bijective (dualTensorHom R M N) where
  left := .of_comp (f := f.compRight R) <| by
    rw [← coe_comp, ← dualTensorHom_comp_lTensor]
    refine h.1.comp (injective_of_comp_eq_id _ (g.lTensor _) ?_)
    rw [← lTensor_comp, comp_eq_id, lTensor_id]
  right := .of_comp (g := g.lTensor _) <| by
    rw [← coe_comp, dualTensorHom_comp_lTensor, coe_comp]
    refine (surjective_of_comp_eq_id (f.compRight R) _ ?_).comp h.2
    ext; exact congr($comp_eq_id _)
/-
**dualTensorHom_fun_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHom_fun_bijective [Finite ι] (h : Function.Bijective (dualTensor
Hom R M N)) : Function.Bijective (dualTensorHom R M (ι -> N))
参数：h : Function.Bijective (dualTensorHom R M N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `dualTensorHom_bijective_of_comp_eq_id_right`：dualTensorHom_bijective_of_
comp_eq_id_right (f : N ->ₗ[R] P) (g : P ->ₗ[R] N) (comp_eq_id : g ∘ₗ f = .id) (
h : Function.Bijective (dualTenso…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dualTensorHom_finsupp_bijective`：dualTensorHom_finsupp_bijective (fin : 
Finite ι ∨ Module.Finite R M) (h : Function.Bijective (dualTensorHom R M N)) : F
unction.Bijective (du…
-/
theorem dualTensorHom_fun_bijective [Finite ι] (h : Function.Bijective (dualTensorHom R M N)) :
    Function.Bijective (dualTensorHom R M (ι → N)) :=
  dualTensorHom_bijective_of_comp_eq_id_right
    (Finsupp.linearEquivFunOnFinite R N ι).symm
    (Finsupp.linearEquivFunOnFinite ..).toLinearMap (by ext; simp)
    (dualTensorHom_finsupp_bijective (.inl ‹_›) h)
/-
**dualTensorHom_bijective_of_finite_projective_right** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：dualTensorHom_bijective_of_finite_projective_right [Module.Finite R N] [Pr
ojective R N] : Function.Bijective (dualTensorHom R M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.exists_comp_eq_id_of_projective`：exists_comp_eq_id_of_proj
ective [Module.Finite R M] [Projective R M] : exists (n : Nat) (f : (Fin n -> R)
 ->ₗ[R] M) (g : M ->ₗ[R] Fin n -> R…
· 使用定理 `dualTensorHom_bijective_of_comp_eq_id_right`：dualTensorHom_bijective_of_
comp_eq_id_right (f : N ->ₗ[R] P) (g : P ->ₗ[R] N) (comp_eq_id : g ∘ₗ f = .id) (
h : Function.Bijective (dualTenso…
· 使用定理 `dualTensorHom_fun_bijective`：dualTensorHom_fun_bijective [Finite ι] (h :
 Function.Bijective (dualTensorHom R M N)) : Function.Bijective (dualTensorHom R
 M (ι -> N))
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `_private.Mathlib.LinearAlgebra.Contraction.0.dualTensorHom_self_right_bi
jective`：∀ {R : Type u_2} {M : Type u_3} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M] [inst_2 : _root_.Module R M],   Function.Bijective ⇑(dual…
-/
theorem dualTensorHom_bijective_of_finite_projective_right [Module.Finite R N] [Projective R N] :
    Function.Bijective (dualTensorHom R M N) :=
  have ⟨_n, f, g, _, _, eq⟩ := Finite.exists_comp_eq_id_of_projective R N
  dualTensorHom_bijective_of_comp_eq_id_right g f eq <|
    dualTensorHom_fun_bijective dualTensorHom_self_right_bijective
/-
**dualTensorHom_bijective_of_finite_left_projective_right** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：dualTensorHom_bijective_of_finite_left_projective_right [Module.Finite R M
] [Projective R N] : Function.Bijective (dualTensorHom R M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.projective_def'`：projective_def' : Projective R P ↔ exists s : P 
->ₗ[R] P ->₀ R, Finsupp.linearCombination R id ∘ₗ s = .id
· 使用定理 `dualTensorHom_bijective_of_comp_eq_id_right`：dualTensorHom_bijective_of_
comp_eq_id_right (f : N ->ₗ[R] P) (g : P ->ₗ[R] N) (comp_eq_id : g ∘ₗ f = .id) (
h : Function.Bijective (dualTenso…
· 使用定理 `dualTensorHom_finsupp_bijective`：dualTensorHom_finsupp_bijective (fin : 
Finite ι ∨ Module.Finite R M) (h : Function.Bijective (dualTensorHom R M N)) : F
unction.Bijective (du…
· 使用定理 `_private.Mathlib.LinearAlgebra.Contraction.0.dualTensorHom_self_right_bi
jective`：∀ {R : Type u_2} {M : Type u_3} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M] [inst_2 : _root_.Module R M],   Function.Bijective ⇑(dual…
-/
theorem dualTensorHom_bijective_of_finite_left_projective_right [Module.Finite R M]
    [Projective R N] : Function.Bijective (dualTensorHom R M N) :=
  have ⟨f, eq⟩ := projective_def'.mp ‹Projective R N›
  dualTensorHom_bijective_of_comp_eq_id_right _ _ eq <|
    dualTensorHom_finsupp_bijective (.inr ‹_›) dualTensorHom_self_right_bijective

variable (R M N) in
/-- If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence. -/
@[simp]
/-
**dualTensorHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dualTensorHomEquiv [Module.Finite R M] [Projective R M] : Module.Dual R M 
otimes[R] N ≃ₗ[R] M ->ₗ[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)

--- 原说明 ---
If `M` is finite free, the natural map $M^* ⊗ N → Hom(M, N)$ is an
equivalence.
-/
noncomputable def dualTensorHomEquiv [Module.Finite R M] [Projective R M] :
    Module.Dual R M ⊗[R] N ≃ₗ[R] M →ₗ[R] N :=
  .ofBijective _ (dualTensorHom_bijective ..)
/-
**dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis (b : Basis ι R M) [Decidab
leEq ι] [Fintype ι] : have
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis
    (b : Basis ι R M) [DecidableEq ι] [Fintype ι] :
    have := Module.Finite.of_basis b; have := Module.Free.of_basis b
    dualTensorHomEquiv R M N = dualTensorHomEquivOfBasis b := by
  ext; rfl

end CommSemiring

end Contraction

section HomTensorHom

open TensorProduct

open Module TensorProduct LinearMap

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Projective R M] [Module.Finite R M]

/-- When `M` is a finite free module, the map `lTensorHomToHomLTensor` is an equivalence. Note
that `lTensorHomEquivHomLTensor` is not defined directly in terms of
`lTensorHomToHomLTensor`, but the equivalence between the two is given by
`lTensorHomEquivHomLTensor_toLinearMap` and `lTensorHomEquivHomLTensor_apply`. -/
/-
**lTensorHomEquivHomLTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lTensorHomEquivHomLTensor : P otimes[R] (M ->ₗ[R] Q) ≃ₗ[R] M ->ₗ[R] P otim
es[R] Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` is a finite free module, the map `lTensorHomToHomLTensor` is an equival
ence. Note
that `lTensorHomEquivHomLTensor` is not defined directly in terms of
`lTensorHomToHomLTensor`, but the equivalence between the two is given by
`lTensorHomEquivHomLTensor_toLinearMap` and `lTensorHomEquivHomLTensor_apply`.
-/
noncomputable def lTensorHomEquivHomLTensor : P ⊗[R] (M →ₗ[R] Q) ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q).symm ≪≫ₗ
      TensorProduct.leftComm R P _ Q ≪≫ₗ
    dualTensorHomEquiv R M _

/-- When `M` is a finite free module, the map `rTensorHomToHomRTensor` is an equivalence. Note
that `rTensorHomEquivHomRTensor` is not defined directly in terms of
`rTensorHomToHomRTensor`, but the equivalence between the two is given by
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`. -/
/-
**rTensorHomEquivHomRTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rTensorHomEquivHomRTensor : (M ->ₗ[R] P) otimes[R] Q ≃ₗ[R] M ->ₗ[R] P otim
es[R] Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` is a finite free module, the map `rTensorHomToHomRTensor` is an equival
ence. Note
that `rTensorHomEquivHomRTensor` is not defined directly in terms of
`rTensorHomToHomRTensor`, but the equivalence between the two is given by
`rTensorHomEquivHomRTensor_toLinearMap` and `rTensorHomEquivHomRTensor_apply`.
-/
noncomputable def rTensorHomEquivHomRTensor : (M →ₗ[R] P) ⊗[R] Q ≃ₗ[R] M →ₗ[R] P ⊗[R] Q :=
  congr (dualTensorHomEquiv R M P).symm (LinearEquiv.refl R Q) ≪≫ₗ TensorProduct.assoc R _ P Q ≪≫ₗ
    dualTensorHomEquiv R M _

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/-
**lTensorHomEquivHomLTensor_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lTensorHomEquivHomLTensor_toLinearMap : (lTensorHomEquivHomLTensor R M P Q
).toLinearMap = lTensorHomToHomLTensor (.id R) M P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.cancel_right`：cancel_right (hg : Surjective g) : f.comp g = f'
.comp g ↔ f = f'
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
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
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensorHomEquivHomLTensor_toLinearMap :
    (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor (.id R) M P Q := by
  let e := congr (LinearEquiv.refl R P) (dualTensorHomEquiv R M Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f q m
  simp [e, lTensorHomEquivHomLTensor]

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/-
**rTensorHomEquivHomRTensor_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rTensorHomEquivHomRTensor_toLinearMap : (rTensorHomEquivHomRTensor R M P Q
).toLinearMap = rTensorHomToHomRTensor (.id R) M P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.cancel_right`：cancel_right (hg : Surjective g) : f.comp g = f'
.comp g ↔ f = f'
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dualTensorHom_bijective`：dualTensorHom_bijective [Module.Finite R M] [Pr
ojective R M] : Function.Bijective (dualTensorHom R M N)
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensorHomEquivHomRTensor_toLinearMap :
    (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor (.id R) M P Q := by
  let e := congr (dualTensorHomEquiv R M P) (LinearEquiv.refl R Q)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f p q m
  simp [e, rTensorHomEquivHomRTensor, smul_tmul']

variable {R M N P Q}

@[simp]
/-
**lTensorHomEquivHomLTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lTensorHomEquivHomLTensor_apply (x : P otimes[R] (M ->ₗ[R] Q)) : lTensorHo
mEquivHomLTensor R M P Q x = lTensorHomToHomLTensor (.id R) M P Q x
参数：x : P otimes[R] (M ->ₗ[R] Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `lTensorHomEquivHomLTensor_toLinearMap`：lTensorHomEquivHomLTensor_toLinea
rMap : (lTensorHomEquivHomLTensor R M P Q).toLinearMap = lTensorHomToHomLTensor 
(.id R) M P Q
-/
theorem lTensorHomEquivHomLTensor_apply (x : P ⊗[R] (M →ₗ[R] Q)) :
    lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomLTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, lTensorHomEquivHomLTensor_toLinearMap]

@[simp]
/-
**rTensorHomEquivHomRTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rTensorHomEquivHomRTensor_apply (x : (M ->ₗ[R] P) otimes[R] Q) : rTensorHo
mEquivHomRTensor R M P Q x = rTensorHomToHomRTensor (.id R) M P Q x
参数：x : (M ->ₗ[R] P) otimes[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `rTensorHomEquivHomRTensor_toLinearMap`：rTensorHomEquivHomRTensor_toLinea
rMap : (rTensorHomEquivHomRTensor R M P Q).toLinearMap = rTensorHomToHomRTensor 
(.id R) M P Q
-/
theorem rTensorHomEquivHomRTensor_apply (x : (M →ₗ[R] P) ⊗[R] Q) :
    rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomRTensor (.id R) M P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, rTensorHomEquivHomRTensor_toLinearMap]

variable (R M N P Q) [Projective R N] [Module.Finite R N]

/-- When `M` and `N` are free `R` modules, the map `homTensorHomMap` is an equivalence. Note that
`homTensorHomEquiv` is not defined directly in terms of `homTensorHomMap`, but the equivalence
between the two is given by `homTensorHomEquiv_toLinearMap` and `homTensorHomEquiv_apply`.
-/
/-
**homTensorHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homTensorHomEquiv : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q) ≃ₗ[R] M otimes[R] 
N ->ₗ[R] P otimes[R] Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` and `N` are free `R` modules, the map `homTensorHomMap` is an equivalen
ce. Note that
`homTensorHomEquiv` is not defined directly in terms of `homTensorHomMap`, but t
he equivalence
between the two is given by `homTensorHomEquiv_toLinearMap` and `homTensorHomEqu
iv_apply`.
-/
noncomputable def homTensorHomEquiv : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q) ≃ₗ[R] M ⊗[R] N →ₗ[R] P ⊗[R] Q :=
  rTensorHomEquivHomRTensor R M P _ ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr (lTensorHomEquivHomLTensor R N _ Q) ≪≫ₗ
    lift.equiv _ M N _

attribute [-ext] AlgebraTensorModule.curry_injective in
@[simp]
/-
**homTensorHomEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：homTensorHomEquiv_toLinearMap : (homTensorHomEquiv R M N P Q).toLinearMap 
= homTensorHomMap (.id R) M N P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.compr₂ₛₗ.congr_simp`：∀ {R : Type u_2} [inst : CommSemiring R] 
{R₂ : Type u_14} {R₃ : Type u_15} {R₄ : Type u_16} {M : Type u_17}   {N : Type u
_18} {P : Type u_19…
· 使用定理 `rTensorHomEquivHomRTensor_apply`：rTensorHomEquivHomRTensor_apply (x : (M
 ->ₗ[R] P) otimes[R] Q) : rTensorHomEquivHomRTensor R M P Q x = rTensorHomToHomR
Tensor (.id R) M P Q …
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.lift.equiv_apply`：∀ {R : Type u_1} {R₂ : Type u_2} [inst :
 CommSemiring R] [inst_1 : CommSemiring R₂] (σ₁₂ : R →+* R₂) (M : Type u_7)   (N
 : Type u_8) (P₂ : T…
· 使用定理 `lTensorHomEquivHomLTensor_apply`：lTensorHomEquivHomLTensor_apply (x : P 
otimes[R] (M ->ₗ[R] Q)) : lTensorHomEquivHomLTensor R M P Q x = lTensorHomToHomL
Tensor (.id R) M P Q …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homTensorHomEquiv_toLinearMap :
    (homTensorHomEquiv R M N P Q).toLinearMap = homTensorHomMap (.id R) M N P Q := by
  ext m n
  simp only [homTensorHomEquiv, compr₂ₛₗ_apply, mk_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.trans_apply, lift.equiv_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, rTensorHomEquivHomRTensor_apply, lTensorHomEquivHomLTensor_apply,
    lTensorHomToHomLTensor_apply, rTensorHomToHomRTensor_apply, homTensorHomMap_apply,
    map_tmul]

variable {R M N P Q}

@[simp]
/-
**homTensorHomEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：homTensorHomEquiv_apply (x : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q)) : homTen
sorHomEquiv R M N P Q x = homTensorHomMap (.id R) M N P Q x
参数：x : (M ->ₗ[R] P) otimes[R] (N ->ₗ[R] Q)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_toLinearMap`：coe_toLinearMap : ⇑e.toLinearMap = e
· 使用定理 `homTensorHomEquiv_toLinearMap`：homTensorHomEquiv_toLinearMap : (homTenso
rHomEquiv R M N P Q).toLinearMap = homTensorHomMap (.id R) M N P Q
-/
theorem homTensorHomEquiv_apply (x : (M →ₗ[R] P) ⊗[R] (N →ₗ[R] Q)) :
    homTensorHomEquiv R M N P Q x = homTensorHomMap (.id R) M N P Q x := by
  rw [← LinearEquiv.coe_toLinearMap, homTensorHomEquiv_toLinearMap]

end CommSemiring

end HomTensorHom

namespace TensorProduct

open LinearMap Module

variable {R M N : Type*} {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

attribute [local ext] TensorProduct.ext

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- An inverse to `TensorProduct.dualDistrib` given bases.
-/
/-
**TensorProduct.dualDistribInvOfBasis** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) : Dual R (M otim
es[R] N) ->ₗ[R] Dual R M otimes[R] Dual R N
参数：b : Basis ι R M；c : Basis κ R N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
An inverse to `TensorProduct.dualDistrib` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      applyₗ (c j) ∘ₗ applyₗ (b i) ∘ₗ lcurry (.id R) M N R

@[simp]
/-
**TensorProduct.dualDistribInvOfBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
形式化陈述：dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual 
R (M otimes[R] N)) : dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i otimesₜ c j)
 • b.dualBasis i otimesₜ c.dualBasis j
参数：b : Basis ι R M；c : Basis κ R N；f : Dual R (M otimes[R] N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.applyₗ_apply_apply`：∀ {R : Type u_1} {M : Type u_4} {M₂ : Type
 u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id M₂] [inst_3 : _…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]
/-
**TensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse** 是 Mathlib 中的一个定
理，位于命名空间 `TensorProduct`。
形式化陈述：dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basi
s κ R N) : comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id
参数：b : Basis ι R M；c : Basis κ R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `TensorProduct.dualDistribInvOfBasis_apply`：dualDistribInvOfBasis_apply (
b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M otimes[R] N)) : dualDistribInv
OfBasis b c f = ∑ i, ∑ j, f (b …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.tensorProduct_repr_tmul_apply`：tensorProduct_repr_tmul_appl
y (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N) (i : ι) (j : κ) : (tensorP
roduct b c).repr (m otimesₜ n) (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.tensorProduct_apply`：tensorProduct_apply (b : Basis ι S M) 
(c : Basis κ R N) (i : ι) (j : κ) : tensorProduct b c (i, j) = b i otimesₜ c j
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
（共 41 条，此处仅展示前 30 条）
-/
theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, LinearMap.coe_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }
/-
**TensorProduct.dualDistrib_dualDistribInvOfBasis_right_inverse** 是 Mathlib 中的一个
定理，位于命名空间 `TensorProduct`。
形式化陈述：dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Bas
is κ R N) : comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id
参数：b : Basis ι R M；c : Basis κ R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.tensorProduct_apply`：tensorProduct_apply (b : Basis ι S M) 
(c : Basis κ R N) (i : ι) (j : κ) : tensorProduct b c (i, j) = b i otimesₜ c j
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `TensorProduct.dualDistribInvOfBasis_apply`：dualDistribInvOfBasis_apply (
b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M otimes[R] N)) : dualDistribInv
OfBasis b c f = ∑ i, ∑ j, f (b …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 32 条，此处仅展示前 30 条）
-/
theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps!]
/-
**TensorProduct.dualDistribEquivOfBasis** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
`。
形式化陈述：dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) : Dual R M oti
mes[R] Dual R N ≃ₗ[R] Dual R (M otimes[R] N)
参数：b : Basis ι R M；c : Basis κ R N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse`：dualDistri
b_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) : comp 
(dualDistrib R M N) (dualDistribInvOfBasis b c) = …
· 使用定理 `TensorProduct.dualDistrib_dualDistribInvOfBasis_right_inverse`：dualDistr
ib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) : com
p (dualDistribInvOfBasis b c) (dualDistrib R M N) =…

--- 原说明 ---
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases fo
r `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine LinearEquiv.ofLinearMap (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

variable (R M N)
variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
/-
**TensorProduct.dualDistribEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：dualDistribEquiv : Dual R M otimes[R] Dual R N ≃ₗ[R] Dual R (M otimes[R] N
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `
N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the
 natural
isomorphism `R ⊗ R ≃ R`.
-/
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

end TensorProduct

