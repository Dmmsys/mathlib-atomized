/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The `A`-module structure on `M ⊗[R] N`

When `M` is both an `R`-module and an `A`-module, and `Algebra R A`, then many of the morphisms
preserve the actions by `A`.

The `Module` instance itself is provided elsewhere as `TensorProduct.leftModule`. This file provides
more general versions of the definitions already in `LinearAlgebra/TensorProduct`.

In this file, we use the convention that `M`, `N`, `P`, `Q` are all `R`-modules, but only `M` and
`P` are simultaneously `A`-modules.

## Main definitions

* `TensorProduct.AlgebraTensorModule.curry`
* `TensorProduct.AlgebraTensorModule.uncurry`
* `TensorProduct.AlgebraTensorModule.lcurry`
* `TensorProduct.AlgebraTensorModule.lift`
* `TensorProduct.AlgebraTensorModule.lift.equiv`
* `TensorProduct.AlgebraTensorModule.mk`
* `TensorProduct.AlgebraTensorModule.map`
* `TensorProduct.AlgebraTensorModule.mapBilinear`
* `TensorProduct.AlgebraTensorModule.congr`
* `TensorProduct.AlgebraTensorModule.rid`
* `TensorProduct.AlgebraTensorModule.homTensorHomMap`
* `TensorProduct.AlgebraTensorModule.assoc`
* `TensorProduct.AlgebraTensorModule.leftComm`
* `TensorProduct.AlgebraTensorModule.rightComm`
* `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`
* `LinearMap.baseChange A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

@[expose] public section

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uS uA uB uM uN uP uQ uP' uQ'
variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

open LinearMap
open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M]
variable [IsScalarTower R A M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [Module A P]
variable [IsScalarTower R A P]
variable [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid P'] [Module R P'] [Module A P'] [Module B P']
variable [IsScalarTower R A P'] [IsScalarTower R B P'] [SMulCommClass A B P']
variable [AddCommMonoid Q'] [Module R Q']

/-
**TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor** 是 Mathlib 中的一个定理，位于命
名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：smul_eq_lsmul_rTensor (a : A) (x : M otimes[R] N) : a • x = (lsmul R R M a
).rTensor N x
参数：a : A；x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem smul_eq_lsmul_rTensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R R M a).rTensor N x :=
  rfl

/-- Heterobasic version of `TensorProduct.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
nonrec def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }

/-
**TensorProduct.AlgebraTensorModule.restrictScalars_curry** 是 Mathlib 中的一个定理，位于命
名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：restrictScalars_curry (f : M otimes[R] N ->ₗ[A] P) : restrictScalars R (cu
rry f) = TensorProduct.curry (f.restrictScalars R)
参数：f : M otimes[R] N ->ₗ[A] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem restrictScalars_curry (f : M ⊗[R] N →ₗ[A] P) :
    restrictScalars R (curry f) = TensorProduct.curry (f.restrictScalars R) :=
  rfl

/-- Just as `TensorProduct.ext` is marked `ext` instead of `TensorProduct.ext'`, this is
a better `ext` lemma than `TensorProduct.AlgebraTensorModule.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) :=
  fun _ _ h =>
  LinearMap.restrictScalars_injective R <|
    curry_injective <| (congr_arg (LinearMap.restrictScalars R) h :)

/-
**TensorProduct.AlgebraTensorModule.ext** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
.AlgebraTensorModule`。
形式化陈述：ext {g h : M otimes[R] N ->ₗ[A] P} (H : forall x y, g (x otimesₜ y) = h (x
 otimesₜ y)) : g = h
参数：H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
-/
theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H

/-- Heterobasic version of `TensorProduct.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        ∀ x : M ⊗[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R R _ c) x =
            (lsmul R R _ c).comp (lift (f.restrictScalars R)) x
        from
        LinearMap.ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }

@[simp]
/-
**TensorProduct.AlgebraTensorModule.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：lift_apply (f : M ->ₗ[A] N ->ₗ[R] P) (a : M otimes[R] N) : AlgebraTensorMo
dule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a
参数：f : M ->ₗ[A] N ->ₗ[R] P；a : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem lift_apply (f : M →ₗ[A] N →ₗ[R] P) (a : M ⊗[R] N) :
    AlgebraTensorModule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.lift_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct.AlgebraTensorModule`。
形式化陈述：lift_tmul (f : M ->ₗ[A] N ->ₗ[R] P) (x : M) (y : N) : lift f (x otimesₜ y)
 = f x y
参数：f : M ->ₗ[A] N ->ₗ[R] P；x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  rfl

variable (R A B M N P Q)

section
variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

/-- Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
/-
**TensorProduct.AlgebraTensorModule.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `TensorPro
duct.AlgebraTensorModule`。
形式化陈述：uncurry : (M ->ₗ[A] N ->ₗ[R] P) ->ₗ[B] M otimes[R] N ->ₗ[A] P where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A
] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N
 →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`.
-/
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[B] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]

/-- Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
/-
**TensorProduct.AlgebraTensorModule.lcurry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProd
uct.AlgebraTensorModule`。
形式化陈述：lcurry : (M otimes[R] N ->ₗ[A] P) ->ₗ[B] M ->ₗ[A] N ->ₗ[R] P where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`.
-/
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[B] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Heterobasic version of `TensorProduct.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
/-
**TensorProduct.AlgebraTensorModule.lift.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Tensor
Product.AlgebraTensorModule.lift`。
形式化陈述：(R : Type uR) →   (A : Type uA) →     (B : Type uB) →       (M : Type uM) 
→         (N : Type uN) →           (P : Type uP) →             [inst : CommSemi
ring R] →               [inst_1 : Semiring A] →                 [inst_2 : Semiri
ng B] →                   [inst_3 : Algebra R A] →                     [inst_4 :
 Algebra R B] →                       [inst_5 : AddCommMonoid M] →              
           [inst_6 : _root_.Module R M] →                           [inst_7 : _r
oot_.Module A M] →                             [inst_8 : IsScalarTower R A M] → 
                              [inst_9 : AddCommMonoid N] →                      
           [inst_10 : _root_.Module R N] →                                   [in
st_11 : AddCommMonoid P] →                                     [inst_12 : _root_
.Module R P] →                                       [inst_13 : _root_.Module A 
P] →                                         [inst_14 : IsScalarTower R A P] →  
                                         [inst_15 : _root_.Module B P] →        
                                     [inst_16 : IsScalarTower R B P] →          
                                     [inst_17 : SMulCommClass A B P] →          
                                       (M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] TensorProduct R
 M N →ₗ[A] P
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A
] N →[R] P`.
-/
def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinearMap (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

/-- Heterobasic version of `TensorProduct.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps! apply]
nonrec def mk (A M N : Type*) [Semiring A]
    [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M]
    [AddCommMonoid N] [Module R N] : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }

variable {R A B M N P Q}

/-- The heterobasic version of `mk` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProdu
ct.AlgebraTensorModule`。
形式化陈述：mk_eq : mk R R M N = TensorProduct.mk R M N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The heterobasic version of `mk` coincides with the regular version.
-/
lemma mk_eq : mk R R M N = TensorProduct.mk R M N := rfl

/-- Heterobasic version of `TensorProduct.map` -/
/-
**TensorProduct.AlgebraTensorModule.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
.AlgebraTensorModule`。
形式化陈述：map (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : M otimes[R] N ->ₗ[A] P otimes[R] Q
参数：f : M ->ₗ[A] P；g : N ->ₗ[R] Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.map`
-/
def map (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[A] P ⊗[R] Q :=
  lift <|
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f
/-
**TensorProduct.AlgebraTensorModule.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP} {Q
 : Type uQ} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Algebra R 
A] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule A M] [inst_6 : IsScalarTower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _r
oot_.Module R N]   [inst_9 : AddCommMonoid P] [inst_10 : _root_.Module R P] [ins
t_11 : _root_.Module A P] [inst_12 : IsScalarTower R A P]   [inst_13 : AddCommMo
noid Q] [inst_14 : _root_.Module R Q] (f : M →ₗ[A] P) (g : N →ₗ[R] Q) (m : M) (n
 : N),   (TensorProduct.AlgebraTensorModule.map f g) (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n
参数：f : M →ₗ[A] P；g : N →ₗ[R] Q；m : M；n : N；TensorProduct.AlgebraTensorModule.map
 f g；m ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem map_tmul (f : M →ₗ[A] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.map_id** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct.AlgebraTensorModule`。
形式化陈述：map_id : map (id : M ->ₗ[A] M) (id : N ->ₗ[R] N) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_id : map (id : M →ₗ[A] M) (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl
/-
**TensorProduct.AlgebraTensorModule.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：map_comp (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N -
>ₗ[R] Q) : map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁)
参数：f₂ : P ->ₗ[A] P'；f₁ : M ->ₗ[A] P；g₂ : Q ->ₗ[R] Q'；g₁ : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem map_comp (f₂ : P →ₗ[A] P') (f₁ : M →ₗ[A] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext fun _ _ => rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.map_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M
] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [inst_6 : IsScalar
Tower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R N],   TensorPr
oduct.AlgebraTensorModule.map 1 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.map_id`：map_id : map (id : M ->ₗ[A] M)
 (id : N ->ₗ[R] N) = .id
-/
protected theorem map_one : map (1 : M →ₗ[A] M) (1 : N →ₗ[R] N) = 1 := map_id
/-
**TensorProduct.AlgebraTensorModule.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M
] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [inst_6 : IsScalar
Tower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R N] (f₁ f₂ : M 
→ₗ[A] M)   (g₁ g₂ : N →ₗ[R] N),   TensorProduct.AlgebraTensorModule.map (f₁ * f₂
) (g₁ * g₂) =     TensorProduct.AlgebraTensorModule.map f₁ g₁ * TensorProduct.Al
gebraTensorModule.map f₂ g₂
参数：f₁ f₂ : M →ₗ[A] M；g₁ g₂ : N →ₗ[R] N；f₁ * f₂；g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.map_comp`：map_comp (f₂ : P ->ₗ[A] P') 
(f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q) : map (f₂.comp f₁) (g₂.co
mp g₁) = (map f₂ g₂).comp (map f…
-/
protected theorem map_mul (f₁ f₂ : M →ₗ[A] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ := map_comp _ _ _ _
/-
**TensorProduct.AlgebraTensorModule.map_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：map_add_left (f₁ f₂ : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map (f₁ + f₂) g = map
 f₁ g + map f₂ g
参数：f₁ f₂ : M ->ₗ[A] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_left (f₁ f₂ : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]
/-
**TensorProduct.AlgebraTensorModule.map_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct.AlgebraTensorModule`。
形式化陈述：map_add_right (f : M ->ₗ[A] P) (g₁ g₂ : N ->ₗ[R] Q) : map f (g₁ + g₂) = ma
p f g₁ + map f g₂
参数：f : M ->ₗ[A] P；g₁ g₂ : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_right (f : M →ₗ[A] P) (g₁ g₂ : N →ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]
/-
**TensorProduct.AlgebraTensorModule.map_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Te
nsorProduct.AlgebraTensorModule`。
形式化陈述：map_smul_right (r : R) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map f (r • g) =
 r • map f g
参数：r : R；f : M ->ₗ[A] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_right (r : R) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]
/-
**TensorProduct.AlgebraTensorModule.map_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct.AlgebraTensorModule`。
形式化陈述：map_smul_left (b : B) (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map (b • f) g = 
b • map f g
参数：b : B；f : M ->ₗ[A] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_left (b : B) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map (b • f) g = b • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

/-- The heterobasic version of `map` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct.AlgebraTensorModule`。
形式化陈述：map_eq (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : map f g = TensorProduct.map f g
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `map` coincides with the regular version.
-/
theorem map_eq (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map f g = TensorProduct.map f g := rfl

variable (A M) in
/-- Heterobasic version of `LinearMap.lTensor` -/
/-
**TensorProduct.AlgebraTensorModule.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorPro
duct.AlgebraTensorModule`。
形式化陈述：lTensor : (N ->ₗ[R] Q) ->ₗ[R] M otimes[R] N ->ₗ[A] M otimes[R] Q where toF
un f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `LinearMap.lTensor`
-/
def lTensor : (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[A] M ⊗[R] Q where
  toFun f := map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp]
/-
**TensorProduct.AlgebraTensorModule.coe_lTensor** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：coe_lTensor (f : N ->ₗ[R] Q) : (lTensor A M f : M otimes[R] N -> M otimes[
R] Q) = f.lTensor M
参数：f : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma coe_lTensor (f : N →ₗ[R] Q) :
    (lTensor A M f : M ⊗[R] N → M ⊗[R] Q) = f.lTensor M := rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.restrictScalars_lTensor** 是 Mathlib 中的一个引理，位
于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：restrictScalars_lTensor (f : N ->ₗ[R] Q) : (lTensor A M f).restrictScalars
 R = f.lTensor M
参数：f : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma restrictScalars_lTensor (f : N →ₗ[R] Q) :
    (lTensor A M f).restrictScalars R = f.lTensor M := rfl
/-
**TensorProduct.AlgebraTensorModule.lTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {Q : Type uQ} [i
nst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : A
ddCommMonoid M] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [ins
t_6 : IsScalarTower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R 
N] [inst_9 : AddCommMonoid Q]   [inst_10 : _root_.Module R Q] (f : N →ₗ[R] Q) (m
 : M) (n : N),   ((TensorProduct.AlgebraTensorModule.lTensor A M) f) (m ⊗ₜ[R] n)
 = m ⊗ₜ[R] f n
参数：f : N →ₗ[R] Q；m : M；n : N；(TensorProduct.AlgebraTensorModule.lTensor A M) f；m
 ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
@[simp] lemma lTensor_tmul (f : N →ₗ[R] Q) (m : M) (n : N) :
    lTensor A M f (m ⊗ₜ[R] n) = m ⊗ₜ f n :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.lTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M
] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [inst_6 : IsScalar
Tower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R N],   (TensorP
roduct.AlgebraTensorModule.lTensor A M) LinearMap.id = LinearMap.id
参数：TensorProduct.AlgebraTensorModule.lTensor A M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
@[simp] lemma lTensor_id : lTensor A M (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl
/-
**TensorProduct.AlgebraTensorModule.lTensor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：lTensor_comp (f₂ : Q ->ₗ[R] Q') (f₁ : N ->ₗ[R] Q) : lTensor A M (f₂.comp f
₁) = (lTensor A M f₂).comp (lTensor A M f₁)
参数：f₂ : Q ->ₗ[R] Q'；f₁ : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma lTensor_comp (f₂ : Q →ₗ[R] Q') (f₁ : N →ₗ[R] Q) :
    lTensor A M (f₂.comp f₁) = (lTensor A M f₂).comp (lTensor A M f₁) :=
  ext fun _ _ => rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.lTensor_one** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：lTensor_one : lTensor A M (1 : N ->ₗ[R] N) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.map_id`：map_id : map (id : M ->ₗ[A] M)
 (id : N ->ₗ[R] N) = .id
-/
lemma lTensor_one : lTensor A M (1 : N →ₗ[R] N) = 1 := map_id
/-
**TensorProduct.AlgebraTensorModule.lTensor_mul** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：lTensor_mul (f₁ f₂ : N ->ₗ[R] N) : lTensor A M (f₁ * f₂) = lTensor A M f₁ 
* lTensor A M f₂
参数：f₁ f₂ : N ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.AlgebraTensorModule.lTensor_comp`：lTensor_comp (f₂ : Q ->ₗ
[R] Q') (f₁ : N ->ₗ[R] Q) : lTensor A M (f₂.comp f₁) = (lTensor A M f₂).comp (lT
ensor A M f₁)
-/
lemma lTensor_mul (f₁ f₂ : N →ₗ[R] N) :
    lTensor A M (f₁ * f₂) = lTensor A M f₁ * lTensor A M f₂ := lTensor_comp _ _

variable (R N) in
/-- Heterobasic version of `LinearMap.rTensor` -/
/-
**TensorProduct.AlgebraTensorModule.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorPro
duct.AlgebraTensorModule`。
形式化陈述：rTensor : (M ->ₗ[A] P) ->ₗ[R] M otimes[R] N ->ₗ[A] P otimes[R] N where toF
un f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `LinearMap.rTensor`
-/
def rTensor : (M →ₗ[A] P) →ₗ[R] M ⊗[R] N →ₗ[A] P ⊗[R] N where
  toFun f := map f LinearMap.id
  map_add' f₁ f₂ := map_add_left f₁ f₂ _
  map_smul' _ _ := map_smul_left _ _ _

@[simp]
/-
**TensorProduct.AlgebraTensorModule.coe_rTensor** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：coe_rTensor (f : M ->ₗ[A] P) : (rTensor R N f : M otimes[R] N -> P otimes[
R] N) = f.rTensor N
参数：f : M ->ₗ[A] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma coe_rTensor (f : M →ₗ[A] P) :
    (rTensor R N f : M ⊗[R] N → P ⊗[R] N) = f.rTensor N := rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.restrictScalars_rTensor** 是 Mathlib 中的一个引理，位
于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：restrictScalars_rTensor (f : M ->ₗ[A] P) : (rTensor R N f).restrictScalars
 R = f.rTensor N
参数：f : M ->ₗ[A] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma restrictScalars_rTensor (f : M →ₗ[A] P) :
    (rTensor R N f).restrictScalars R = f.rTensor N := rfl
/-
**TensorProduct.AlgebraTensorModule.rTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [i
nst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : A
ddCommMonoid M] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [ins
t_6 : IsScalarTower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R 
N] [inst_9 : AddCommMonoid P]   [inst_10 : _root_.Module R P] [inst_11 : _root_.
Module A P] [inst_12 : IsScalarTower R A P] (f : M →ₗ[A] P) (m : M)   (n : N), (
(TensorProduct.AlgebraTensorModule.rTensor R N) f) (m ⊗ₜ[R] n) = f m ⊗ₜ[R] n
参数：f : M →ₗ[A] P；m : M；n : N；(TensorProduct.AlgebraTensorModule.rTensor R N) f；m
 ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
@[simp] lemma rTensor_tmul (f : M →ₗ[A] P) (m : M) (n : N) :
    rTensor R N f (m ⊗ₜ[R] n) = f m ⊗ₜ n :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.rTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} [inst : CommSemi
ring R] [inst_1 : Semiring A]   [inst_2 : Algebra R A] [inst_3 : AddCommMonoid M
] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module A M]   [inst_6 : IsScalar
Tower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R N],   (TensorP
roduct.AlgebraTensorModule.rTensor R N) LinearMap.id = LinearMap.id
参数：TensorProduct.AlgebraTensorModule.rTensor R N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
@[simp] lemma rTensor_id : rTensor R N (id : M →ₗ[A] M) = .id :=
  ext fun _ _ => rfl
/-
**TensorProduct.AlgebraTensorModule.rTensor_comp** 是 Mathlib 中的一个引理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：rTensor_comp (f₂ : P ->ₗ[A] P') (f₁ : M ->ₗ[A] P) : rTensor R N (f₂.comp f
₁) = (rTensor R N f₂).comp (rTensor R N f₁)
参数：f₂ : P ->ₗ[A] P'；f₁ : M ->ₗ[A] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma rTensor_comp (f₂ : P →ₗ[A] P') (f₁ : M →ₗ[A] P) :
    rTensor R N (f₂.comp f₁) = (rTensor R N f₂).comp (rTensor R N f₁) :=
  ext fun _ _ => rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.rTensor_one** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：rTensor_one : rTensor R N (1 : M ->ₗ[A] M) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.map_id`：map_id : map (id : M ->ₗ[A] M)
 (id : N ->ₗ[R] N) = .id
-/
lemma rTensor_one : rTensor R N (1 : M →ₗ[A] M) = 1 := map_id
/-
**TensorProduct.AlgebraTensorModule.rTensor_mul** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：rTensor_mul (f₁ f₂ : M ->ₗ[A] M) : rTensor R M (f₁ * f₂) = rTensor R M f₁ 
* rTensor R M f₂
参数：f₁ f₂ : M ->ₗ[A] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.AlgebraTensorModule.rTensor_comp`：rTensor_comp (f₂ : P ->ₗ
[A] P') (f₁ : M ->ₗ[A] P) : rTensor R N (f₂.comp f₁) = (rTensor R N f₂).comp (rT
ensor R N f₁)
-/
lemma rTensor_mul (f₁ f₂ : M →ₗ[A] M) :
    rTensor R M (f₁ * f₂) = rTensor R M f₁ * rTensor R M f₂ := rTensor_comp _ _

variable (R A B M N P Q)

/-- Heterobasic version of `TensorProduct.map_bilinear` -/
/-
**TensorProduct.AlgebraTensorModule.mapBilinear** 是 Mathlib 中的一个定义，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：mapBilinear : (M ->ₗ[A] P) ->ₗ[B] (N ->ₗ[R] Q) ->ₗ[R] (M otimes[R] N ->ₗ[A
] P otimes[R] Q)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.map_add_left`：map_add_left (f₁ f₂ : M 
->ₗ[A] P) (g : N ->ₗ[R] Q) : map (f₁ + f₂) g = map f₁ g + map f₂ g
· 使用定理 `TensorProduct.AlgebraTensorModule.map_smul_left`：map_smul_left (b : B) (
f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map (b • f) g = b • map f g
· 使用定理 `TensorProduct.AlgebraTensorModule.map_add_right`：map_add_right (f : M ->
ₗ[A] P) (g₁ g₂ : N ->ₗ[R] Q) : map f (g₁ + g₂) = map f g₁ + map f g₂
· 使用定理 `TensorProduct.AlgebraTensorModule.map_smul_right`：map_smul_right (r : R)
 (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : map f (r • g) = r • map f g

--- 原说明 ---
Heterobasic version of `TensorProduct.map_bilinear`
-/
def mapBilinear : (M →ₗ[A] P) →ₗ[B] (N →ₗ[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

variable {R A B M N P Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.mapBilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 
`TensorProduct.AlgebraTensorModule`。
形式化陈述：mapBilinear_apply (f : M ->ₗ[A] P) (g : N ->ₗ[R] Q) : mapBilinear R A B M 
N P Q f g = map f g
参数：f : M ->ₗ[A] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
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
theorem mapBilinear_apply (f : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    mapBilinear R A B M N P Q f g = map f g :=
  rfl

variable (R A B M N P Q)

/-- Heterobasic version of `TensorProduct.homTensorHomMap` -/
/-
**TensorProduct.AlgebraTensorModule.homTensorHomMap** 是 Mathlib 中的一个定义，位于命名空间 `T
ensorProduct.AlgebraTensorModule`。
形式化陈述：homTensorHomMap : ((M ->ₗ[A] P) otimes[R] (N ->ₗ[R] Q)) ->ₗ[B] (M otimes[R
] N ->ₗ[A] P otimes[R] Q)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.homTensorHomMap`
-/
def homTensorHomMap : ((M →ₗ[A] P) ⊗[R] (N →ₗ[R] Q)) →ₗ[B] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  lift <| mapBilinear R A B M N P Q

variable {R A B M N P Q}
/-
**TensorProduct.AlgebraTensorModule.homTensorHomMap_apply** 是 Mathlib 中的一个定理，位于命
名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM} {N : Type uN} {P
 : Type uP} {Q : Type uQ}   [inst : CommSemiring R] [inst_1 : Semiring A] [inst_
2 : Semiring B] [inst_3 : Algebra R A] [inst_4 : Algebra R B]   [inst_5 : AddCom
mMonoid M] [inst_6 : _root_.Module R M] [inst_7 : _root_.Module A M] [inst_8 : I
sScalarTower R A M]   [inst_9 : AddCommMonoid N] [inst_10 : _root_.Module R N] [
inst_11 : AddCommMonoid P] [inst_12 : _root_.Module R P]   [inst_13 : _root_.Mod
ule A P] [inst_14 : IsScalarTower R A P] [inst_15 : AddCommMonoid Q]   [inst_16 
: _root_.Module R Q] [inst_17 : _root_.Module B P] [inst_18 : IsScalarTower R B 
P]   [inst_19 : SMulCommClass A B P] (f : M →ₗ[A] P) (g : N →ₗ[R] Q),   (TensorP
roduct.AlgebraTensorModule.homTensorHomMap R A B M N P Q) (f ⊗ₜ[R] g) =     Tens
orProduct.AlgebraTensorModule.map f g
参数：f : M →ₗ[A] P；g : N →ₗ[R] Q；TensorProduct.AlgebraTensorModule.homTensorHomMap
 R A B M N P Q；f ⊗ₜ[R] g。
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
@[simp] theorem homTensorHomMap_apply (f : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    homTensorHomMap R A B M N P Q (f ⊗ₜ g) = map f g :=
  rfl

/-- Heterobasic version of `TensorProduct.congr` -/
/-
**TensorProduct.AlgebraTensorModule.congr** 是 Mathlib 中的一个定义，位于命名空间 `TensorProdu
ct.AlgebraTensorModule`。
形式化陈述：congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M otimes[R] N) ≃ₗ[A] (P otimes[R]
 Q)
参数：f : M ≃ₗ[A] P；g : N ≃ₗ[R] Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.congr`
-/
def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M ⊗[R] N) ≃ₗ[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp]
/-
**TensorProduct.AlgebraTensorModule.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：congr_refl : congr (.refl A M) (.refl R N) = .refl A _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.map_id`：map_id : map (id : M ->ₗ[A] M)
 (id : N ->ₗ[R] N) = .id
-/
theorem congr_refl : congr (.refl A M) (.refl R N) = .refl A _ :=
  LinearEquiv.toLinearMap_injective <| map_id
/-
**TensorProduct.AlgebraTensorModule.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：congr_trans (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ
[R] Q') : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂)
参数：f₁ : M ≃ₗ[A] P；f₂ : P ≃ₗ[A] P'；g₁ : N ≃ₗ[R] Q；g₂ : Q ≃ₗ[R] Q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.map_comp`：map_comp (f₂ : P ->ₗ[A] P') 
(f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q) : map (f₂.comp f₁) (g₂.co
mp g₁) = (map f₂ g₂).comp (map f…
-/
theorem congr_trans (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q') :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _
/-
**TensorProduct.AlgebraTensorModule.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：congr_symm (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : congr f.symm g.symm = (congr 
f g).symm
参数：f : M ≃ₗ[A] P；g : N ≃ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem congr_symm (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : congr f.symm g.symm = (congr f g).symm := rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.congr_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct.AlgebraTensorModule`。
形式化陈述：congr_one : congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.congr_refl`：congr_refl : congr (.refl 
A M) (.refl R N) = .refl A _
-/
theorem congr_one : congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1 := congr_refl
/-
**TensorProduct.AlgebraTensorModule.congr_mul** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct.AlgebraTensorModule`。
形式化陈述：congr_mul (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N) : congr (f₁ * f₂) (g₁ * 
g₂) = congr f₁ g₁ * congr f₂ g₂
参数：f₁ f₂ : M ≃ₗ[A] M；g₁ g₂ : N ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.congr_trans`：congr_trans (f₁ : M ≃ₗ[A]
 P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q') : congr (f₁.trans f₂) (
g₁.trans g₂) = (congr f₁ g₁).trans …
-/
theorem congr_mul (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N) :
    congr (f₁ * f₂) (g₁ * g₂) = congr f₁ g₁ * congr f₂ g₂ := congr_trans _ _ _ _
/-
**TensorProduct.AlgebraTensorModule.congr_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP} {Q
 : Type uQ} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Algebra R 
A] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule A M] [inst_6 : IsScalarTower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _r
oot_.Module R N]   [inst_9 : AddCommMonoid P] [inst_10 : _root_.Module R P] [ins
t_11 : _root_.Module A P] [inst_12 : IsScalarTower R A P]   [inst_13 : AddCommMo
noid Q] [inst_14 : _root_.Module R Q] (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n
 : N),   (TensorProduct.AlgebraTensorModule.congr f g) (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g
 n
参数：f : M ≃ₗ[A] P；g : N ≃ₗ[R] Q；m : M；n : N；TensorProduct.AlgebraTensorModule.con
gr f g；m ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem congr_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.congr_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `T
ensorProduct.AlgebraTensorModule`。
形式化陈述：∀ {R : Type uR} {A : Type uA} {M : Type uM} {N : Type uN} {P : Type uP} {Q
 : Type uQ} [inst : CommSemiring R]   [inst_1 : Semiring A] [inst_2 : Algebra R 
A] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule A M] [inst_6 : IsScalarTower R A M] [inst_7 : AddCommMonoid N] [inst_8 : _r
oot_.Module R N]   [inst_9 : AddCommMonoid P] [inst_10 : _root_.Module R P] [ins
t_11 : _root_.Module A P] [inst_12 : IsScalarTower R A P]   [inst_13 : AddCommMo
noid Q] [inst_14 : _root_.Module R Q] (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q
 : Q),   (TensorProduct.AlgebraTensorModule.congr f g).symm (p ⊗ₜ[R] q) = f.symm
 p ⊗ₜ[R] g.symm q
参数：f : M ≃ₗ[A] P；g : N ≃ₗ[R] Q；p : P；q : Q；TensorProduct.AlgebraTensorModule.con
gr f g；p ⊗ₜ[R] q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
@[simp] theorem congr_symm_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.congr_eq** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：congr_eq (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : congr f g = TensorProduct.congr
 f g
参数：f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem congr_eq (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    congr f g = TensorProduct.congr f g := rfl

variable (R A M)

/-- Heterobasic version of `TensorProduct.rid`. -/
/-
**TensorProduct.AlgebraTensorModule.rid** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
.AlgebraTensorModule`。
形式化陈述：(R : Type uR) →   (A : Type uA) →     (M : Type uM) →       [inst : CommSe
miring R] →         [inst_1 : Semiring A] →           [inst_2 : Algebra R A] →  
           [inst_3 : AddCommMonoid M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : _root_.Module A M] → [inst_6 : IsScalarTower R A 
M] → TensorProduct R M R ≃ₗ[A] M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.rid`.
-/
protected def rid : M ⊗[R] R ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

/-- The heterobasic version of `rid` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.rid_eq_rid** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：rid_eq_rid : AlgebraTensorModule.rid R R M = TensorProduct.rid R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `rid` coincides with the regular version.
-/
theorem rid_eq_rid : AlgebraTensorModule.rid R R M = TensorProduct.rid R M := rfl

variable {R M} in
@[simp]
/-
**TensorProduct.AlgebraTensorModule.rid_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：rid_tmul (r : R) (m : M) : AlgebraTensorModule.rid R A M (m otimesₜ r) = r
 • m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_tmul (r : R) (m : M) : AlgebraTensorModule.rid R A M (m ⊗ₜ r) = r • m := rfl

variable {M} in
@[simp]
/-
**TensorProduct.AlgebraTensorModule.rid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Te
nsorProduct.AlgebraTensorModule`。
形式化陈述：rid_symm_apply (m : M) : (AlgebraTensorModule.rid R A M).symm m = m otimes
ₜ 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rid_symm_apply (m : M) : (AlgebraTensorModule.rid R A M).symm m = m ⊗ₜ 1 := rfl

end

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module A P]
variable [AddCommMonoid P'] [Module A P']
variable [AddCommMonoid Q] [Module R Q]
variable (R A B M N P P' Q)

attribute [local ext high] TensorProduct.ext

section assoc
variable [Module R P] [IsScalarTower R A P]
variable [Algebra A B] [IsScalarTower A B M]

/-- Heterobasic version of `TensorProduct.assoc`:

`B`-linear equivalence between `(M ⊗[A] P) ⊗[R] Q` and `M ⊗[A] (P ⊗[R] Q)`.

Note this is especially useful with `A = R` (where it is a "more linear" version of
`TensorProduct.assoc`), or with `B = A`. -/
/-
**TensorProduct.AlgebraTensorModule.assoc** 是 Mathlib 中的一个定义，位于命名空间 `TensorProdu
ct.AlgebraTensorModule`。
形式化陈述：assoc : (M otimes[A] P) otimes[R] Q ≃ₗ[B] M otimes[A] (P otimes[R] Q)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `TensorProduct.assoc`:

`B`-linear equivalence between `(M ⊗[A] P) ⊗[R] Q` and `M ⊗[A] (P ⊗[R] Q)`.

Note this is especially useful with `A = R` (where it is a "more linear" version
 of
`TensorProduct.assoc`), or with `B = A`.
-/
def assoc : (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P ⊗[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

variable {M P N Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.assoc_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：assoc_tmul (m : M) (p : P) (q : Q) : assoc R A B M P Q ((m otimesₜ p) otim
esₜ q) = m otimesₜ (p otimesₜ q)
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
theorem assoc_tmul (m : M) (p : P) (q : Q) :
    assoc R A B M P Q ((m ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.assoc_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `T
ensorProduct.AlgebraTensorModule`。
形式化陈述：assoc_symm_tmul (m : M) (p : P) (q : Q) : (assoc R A B M P Q).symm (m otim
esₜ (p otimesₜ q)) = (m otimesₜ p) otimesₜ q
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem assoc_symm_tmul (m : M) (p : P) (q : Q) :
    (assoc R A B M P Q).symm (m ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

/-- The heterobasic version of `assoc` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.assoc_eq** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：assoc_eq : assoc R R R M P Q = TensorProduct.assoc R M P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `assoc` coincides with the regular version.
-/
theorem assoc_eq : assoc R R R M P Q = TensorProduct.assoc R M P Q := rfl
/-
**TensorProduct.AlgebraTensorModule.rTensor_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Te
nsorProduct.AlgebraTensorModule`。
形式化陈述：rTensor_tensor [Module R P'] [IsScalarTower R A P'] (g : P ->ₗ[A] P') : g.
rTensor (M otimes[R] N) = assoc R A A P' M N ∘ₗ map (g.rTensor M) id ∘ₗ (assoc R
 A A P M N).symm.toLinearMap
参数：g : P ->ₗ[A] P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `TensorProduct.AlgebraTensorModule.ext`：ext {g h : M otimes[R] N ->ₗ[A] P
} (H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem rTensor_tensor [Module R P'] [IsScalarTower R A P'] (g : P →ₗ[A] P') :
    g.rTensor (M ⊗[R] N) =
      assoc R A A P' M N ∘ₗ map (g.rTensor M) id ∘ₗ (assoc R A A P M N).symm.toLinearMap :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ ext fun _ _ ↦ rfl

end assoc

section cancelBaseChange
variable [Algebra A B] [IsScalarTower A B M]

/-- `B`-linear equivalence between `M ⊗[A] (A ⊗[R] N)` and `M ⊗[R] N`.
In particular useful with `B = A`. -/
/-
**TensorProduct.AlgebraTensorModule.cancelBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `
TensorProduct.AlgebraTensorModule`。
形式化陈述：cancelBaseChange : M otimes[A] (A otimes[R] N) ≃ₗ[B] M otimes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
`B`-linear equivalence between `M ⊗[A] (A ⊗[R] N)` and `M ⊗[R] N`.
In particular useful with `B = A`.
-/
def cancelBaseChange : M ⊗[A] (A ⊗[R] N) ≃ₗ[B] M ⊗[R] N :=
  letI g : (M ⊗[A] A) ⊗[R] N ≃ₗ[B] M ⊗[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

/-- Base change distributes over tensor product. -/
/-
**TensorProduct.AlgebraTensorModule.distribBaseChange** 是 Mathlib 中的一个定义，位于命名空间 
`TensorProduct.AlgebraTensorModule`。
形式化陈述：distribBaseChange : A otimes[R] (N otimes[R] Q) ≃ₗ[A] (A otimes[R] N) otim
es[A] (A otimes[R] Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Base change distributes over tensor product.
-/
def distribBaseChange : A ⊗[R] (N ⊗[R] Q) ≃ₗ[A] (A ⊗[R] N) ⊗[A] (A ⊗[R] Q) :=
  (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

variable {M P N Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul** 是 Mathlib 中的一个定理，位于命
名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：cancelBaseChange_tmul (m : M) (n : N) (a : A) : cancelBaseChange R A B M N
 (m otimesₜ (a otimesₜ n)) = (a • m) otimesₜ n
参数：m : M；n : N；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem cancelBaseChange_tmul (m : M) (n : N) (a : A) :
    cancelBaseChange R A B M N (m ⊗ₜ (a ⊗ₜ n)) = (a • m) ⊗ₜ n :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul** 是 Mathlib 中的一个定
理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：cancelBaseChange_symm_tmul (m : M) (n : N) : (cancelBaseChange R A B M N).
symm (m otimesₜ n) = m otimesₜ (1 otimesₜ n)
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem cancelBaseChange_symm_tmul (m : M) (n : N) :
    (cancelBaseChange R A B M N).symm (m ⊗ₜ n) = m ⊗ₜ (1 ⊗ₜ n) :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange** 是 Mathlib 中的
一个定理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：lTensor_comp_cancelBaseChange (f : N ->ₗ[R] Q) : lTensor _ _ f ∘ₗ cancelBa
seChange R A B M N = (cancelBaseChange R A B M Q).toLinearMap ∘ₗ lTensor _ _ (lT
ensor _ _ f)
参数：f : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensor_comp_cancelBaseChange (f : N →ₗ[R] Q) :
    lTensor _ _ f ∘ₗ cancelBaseChange R A B M N =
      (cancelBaseChange R A B M Q).toLinearMap ∘ₗ lTensor _ _ (lTensor _ _ f) := by
  ext; simp

@[simp]
/-
**TensorProduct.AlgebraTensorModule.distribBaseChange_tmul** 是 Mathlib 中的一个定理，位于
命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：distribBaseChange_tmul (n : N) (q : Q) (a : A) : distribBaseChange R A N Q
 (a otimesₜ (n otimesₜ q)) = (a otimesₜ n) otimesₜ (1 otimesₜ q)
参数：n : N；q : Q；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem distribBaseChange_tmul (n : N) (q : Q) (a : A) :
    distribBaseChange R A N Q (a ⊗ₜ (n ⊗ₜ q)) = (a ⊗ₜ n) ⊗ₜ (1 ⊗ₜ q) :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul** 是 Mathlib 中的一个
定理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：distribBaseChange_symm_tmul (n : N) (q : Q) (a b : A) : (distribBaseChange
 R A N Q).symm ((a otimesₜ n) otimesₜ (b otimesₜ q)) = (a * b) otimesₜ (n otimes
ₜ q)
参数：n : N；q : Q；a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_eq_smul_one_tmul`：tmul_eq_smul_one_tmul {S : Type*} [
Semiring S] [Module R S] [SMulCommClass R S S] (s : S) (m : M) : s otimesₜ[R] m 
= s • (1 otimesₜ[R] m)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem distribBaseChange_symm_tmul
    (n : N) (q : Q) (a b : A) :
    (distribBaseChange R A N Q).symm ((a ⊗ₜ n) ⊗ₜ (b ⊗ₜ q)) = (a * b) ⊗ₜ (n ⊗ₜ q) := by
  apply ((distribBaseChange R A N Q).eq_symm_apply.mpr ?_).symm
  rw [tmul_eq_smul_one_tmul b, ← smul_tmul, smul_tmul', mul_comm]
  simp
/-
**TensorProduct.AlgebraTensorModule.cancelBaseChange_self_eq_lid** 是 Mathlib 中的一
个引理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：cancelBaseChange_self_eq_lid : cancelBaseChange R A A A N = TensorProduct.
lid A (A otimes[R] N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma cancelBaseChange_self_eq_lid :
    cancelBaseChange R A A A N = TensorProduct.lid A (A ⊗[R] N) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x y hx hy =>
      simp only [tmul_add, map_add, lid_tmul, hx, hy]
  | add x y hx hy => simp [hx, hy]

end cancelBaseChange

section leftComm
variable [Module R P] [IsScalarTower R A P]

/-- Heterobasic version of `TensorProduct.leftComm` -/
/-
**TensorProduct.AlgebraTensorModule.leftComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorPr
oduct.AlgebraTensorModule`。
形式化陈述：leftComm : M otimes[A] (P otimes[R] Q) ≃ₗ[A] P otimes[A] (M otimes[R] Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Heterobasic version of `TensorProduct.leftComm`
-/
def leftComm : M ⊗[A] (P ⊗[R] Q) ≃ₗ[A] P ⊗[A] (M ⊗[R] Q) :=
  let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

variable {M N P Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.leftComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct.AlgebraTensorModule`。
形式化陈述：leftComm_tmul (m : M) (p : P) (q : Q) : leftComm R A M P Q (m otimesₜ (p o
timesₜ q)) = p otimesₜ (m otimesₜ q)
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem leftComm_tmul (m : M) (p : P) (q : Q) :
    leftComm R A M P Q (m ⊗ₜ (p ⊗ₜ q)) = p ⊗ₜ (m ⊗ₜ q) :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.leftComm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间
 `TensorProduct.AlgebraTensorModule`。
形式化陈述：leftComm_symm_tmul (m : M) (p : P) (q : Q) : (leftComm R A M P Q).symm (p 
otimesₜ (m otimesₜ q)) = m otimesₜ (p otimesₜ q)
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem leftComm_symm_tmul (m : M) (p : P) (q : Q) :
    (leftComm R A M P Q).symm (p ⊗ₜ (m ⊗ₜ q)) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

/-- The heterobasic version of `leftComm` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.leftComm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Tenso
rProduct.AlgebraTensorModule`。
形式化陈述：leftComm_eq : leftComm R R M P Q = TensorProduct.leftComm R M P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `leftComm` coincides with the regular version.
-/
theorem leftComm_eq : leftComm R R M P Q = TensorProduct.leftComm R M P Q := rfl

end leftComm

section rightComm

variable [CommSemiring S] [Module S M] [Module S P] [Algebra S B]
  [IsScalarTower S B M] [SMulCommClass R S M] [SMulCommClass S R M]

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- A tensor product analogue of `mul_right_comm`.

Suppose we have a diagram of algebras `R → B ← S`,
and a `B`-module `M`, `S`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ P)      ⎛ M ⎞ ⊗ˢ P
 ⊗ᴿ       ≅ᴮ  ⎜ ⊗ᴿ⎟
 Q            ⎝ Q ⎠
```
-/
/-
**TensorProduct.AlgebraTensorModule.rightComm** 是 Mathlib 中的一个定义，位于命名空间 `TensorP
roduct.AlgebraTensorModule`。
形式化陈述：rightComm : (M otimes[S] P) otimes[R] Q ≃ₗ[B] (M otimes[R] Q) otimes[S] P
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
A tensor product analogue of `mul_right_comm`.

Suppose we have a diagram of algebras `R → B ← S`,
and a `B`-module `M`, `S`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ P)      ⎛ M ⎞ ⊗ˢ P
 ⊗ᴿ       ≅ᴮ  ⎜ ⊗ᴿ⎟
 Q            ⎝ Q ⎠
```
-/
def rightComm : (M ⊗[S] P) ⊗[R] Q ≃ₗ[B] (M ⊗[R] Q) ⊗[S] P :=
  LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (by ext; simp) (by ext; simp)

variable {M N P Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.rightComm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Te
nsorProduct.AlgebraTensorModule`。
形式化陈述：rightComm_tmul (m : M) (p : P) (q : Q) : rightComm R S B M P Q ((m otimesₜ
 p) otimesₜ q) = (m otimesₜ q) otimesₜ p
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rightComm_tmul (m : M) (p : P) (q : Q) :
    rightComm R S B M P Q ((m ⊗ₜ p) ⊗ₜ q) = (m ⊗ₜ q) ⊗ₜ p :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.rightComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Te
nsorProduct.AlgebraTensorModule`。
形式化陈述：rightComm_symm : (rightComm R S B M P Q).symm = rightComm S R B M Q P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rightComm_symm :
    (rightComm R S B M P Q).symm = rightComm S R B M Q P :=
  rfl
/-
**TensorProduct.AlgebraTensorModule.rightComm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空
间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：rightComm_symm_tmul (m : M) (p : P) (q : Q) : (rightComm R S B M P Q).symm
 ((m otimesₜ q) otimesₜ p) = (m otimesₜ p) otimesₜ q
参数：m : M；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem rightComm_symm_tmul (m : M) (p : P) (q : Q) :
    (rightComm R S B M P Q).symm ((m ⊗ₜ q) ⊗ₜ p) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

/-- The heterobasic version of `leftComm` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.rightComm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Tens
orProduct.AlgebraTensorModule`。
形式化陈述：rightComm_eq [Module R P] : rightComm R R R M P Q = TensorProduct.rightCom
m R M P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `leftComm` coincides with the regular version.
-/
theorem rightComm_eq [Module R P] : rightComm R R R M P Q = TensorProduct.rightComm R M P Q := rfl

end rightComm

section tensorTensorTensorComm
variable [Module R P] [IsScalarTower R A P]

variable [Algebra A B] [IsScalarTower A B M]
variable [CommSemiring S] [Algebra R S] [Algebra S B] [Module S M] [Module S N]
variable [IsScalarTower R S M] [SMulCommClass A S M] [SMulCommClass S A M]
  [IsScalarTower S B M] [IsScalarTower R S N]

variable (S)

/-- Heterobasic version of `tensorTensorTensorComm`.

Suppose we have towers of algebras `R → S → B` and `R → A → B`, and
a `B`-module `M`, `S`-module `N`, `A`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ N)      ⎛ M ⎞ ⊗ˢ ⎛ N ⎞
 ⊗ᴬ       ≅ᴮ  ⎜ ⊗ᴬ⎟    ⎜ ⊗ᴿ⎟
(P ⊗ᴿ Q)      ⎝ P ⎠    ⎝ Q ⎠
```
-/
/-
**TensorProduct.AlgebraTensorModule.tensorTensorTensorComm** 是 Mathlib 中的一个定义，位于
命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorTensorTensorComm : (M otimes[S] N) otimes[A] (P otimes[R] Q) ≃ₗ[B] (
M otimes[A] P) otimes[S] (N otimes[R] Q)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
Heterobasic version of `tensorTensorTensorComm`.

Suppose we have towers of algebras `R → S → B` and `R → A → B`, and
a `B`-module `M`, `S`-module `N`, `A`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ N)      ⎛ M ⎞ ⊗ˢ ⎛ N ⎞
 ⊗ᴬ       ≅ᴮ  ⎜ ⊗ᴬ⎟    ⎜ ⊗ᴿ⎟
(P ⊗ᴿ Q)      ⎝ P ⎠    ⎝ Q ⎠
```
-/
def tensorTensorTensorComm :
    (M ⊗[S] N) ⊗[A] (P ⊗[R] Q) ≃ₗ[B] (M ⊗[A] P) ⊗[S] (N ⊗[R] Q) :=
  (assoc R A B (M ⊗[S] N) P Q).symm
    ≪≫ₗ congr (rightComm A S B M N P) (.refl R Q)
    ≪≫ₗ assoc R _ _ (M ⊗[A] P) N Q

variable {M N P Q}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul** 是 Mathlib 中的一个
定理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) : tensorTensor
TensorComm R S A B M N P Q ((m otimesₜ n) otimesₜ (p otimesₜ q)) = (m otimesₜ p)
 otimesₜ (n otimesₜ q)
参数：m : M；n : N；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R S A B M N P Q ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_symm** 是 Mathlib 中的一个
定理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorTensorTensorComm_symm : (tensorTensorTensorComm R S A B M N P Q).sym
m = tensorTensorTensorComm R A S B M P N Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R S A B M N P Q).symm = tensorTensorTensorComm R A S B M P N Q := rfl
/-
**TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_symm_tmul** 是 Mathlib
 中的一个定理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorTensorTensorComm_symm_tmul (m : M) (n : N) (p : P) (q : Q) : (tensor
TensorTensorComm R S A B M N P Q).symm ((m otimesₜ p) otimesₜ (n otimesₜ q)) = (
m otimesₜ n) otimesₜ (p otimesₜ q)
参数：m : M；n : N；p : P；q : Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
theorem tensorTensorTensorComm_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorComm R S A B M N P Q).symm ((m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q)) = (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) :=
  rfl

/-- The heterobasic version of `tensorTensorTensorComm` coincides with the regular version. -/
/-
**TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq** 是 Mathlib 中的一个定理
，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorTensorTensorComm_eq : tensorTensorTensorComm R R R R M N P Q = Tenso
rProduct.tensorTensorTensorComm R M N P Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…

--- 原说明 ---
The heterobasic version of `tensorTensorTensorComm` coincides with the regular v
ersion.
-/
theorem tensorTensorTensorComm_eq :
    tensorTensorTensorComm R R R R M N P Q = TensorProduct.tensorTensorTensorComm R M N P Q := rfl

end tensorTensorTensorComm

section

universe u₁ u₂ u₃ u₄

attribute [local instance] ULift.algebra' in
/-- `ULift` commutes with tensor products. -/
/-
**TensorProduct.AlgebraTensorModule.uliftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Tensor
Product.AlgebraTensorModule`。
形式化陈述：uliftEquiv : ULift.{u₁} (M otimes[R] N) ≃ₗ[A] ULift.{u₂} M otimes[ULift.{u
₃} R] ULift.{u₄} N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift` commutes with tensor products.
-/
def uliftEquiv : ULift.{u₁} (M ⊗[R] N) ≃ₗ[A] ULift.{u₂} M ⊗[ULift.{u₃} R] ULift.{u₄} N :=
  ULift.moduleEquiv ≪≫ₗ
    AlgebraTensorModule.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    (equivOfCompatibleSMul _ _ _ _ _)

variable {M N}

@[simp]
/-
**TensorProduct.AlgebraTensorModule.down_uliftEquiv_symm_tmul** 是 Mathlib 中的一个引理
，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：down_uliftEquiv_symm_tmul (m : ULift M) (n : ULift N) : ((uliftEquiv R A M
 N).symm (m otimesₜ n)).down = m.down otimesₜ n.down
参数：m : ULift M；n : ULift N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma down_uliftEquiv_symm_tmul (m : ULift M) (n : ULift N) :
    ((uliftEquiv R A M N).symm (m ⊗ₜ n)).down = m.down ⊗ₜ n.down :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.uliftEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct.AlgebraTensorModule`。
形式化陈述：uliftEquiv_tmul (m : M) (n : N) : uliftEquiv R A M N ⟨m otimesₜ n⟩ = ⟨m⟩ o
timesₜ ⟨n⟩
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma uliftEquiv_tmul (m : M) (n : N) : uliftEquiv R A M N ⟨m ⊗ₜ n⟩ = ⟨m⟩ ⊗ₜ ⟨n⟩ :=
  rfl

end

end CommSemiring

end AlgebraTensorModule

end TensorProduct

namespace LinearMap

open TensorProduct

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/


section Semiring

variable {R A B M N P : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]
variable (r : R) (f g : M →ₗ[R] N)

variable (A) in
/-- `baseChange A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`.

This "base change" operation is also known as "extension of scalars". -/
/-
**LinearMap.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：baseChange (f : M ->ₗ[R] N) : A otimes[R] M ->ₗ[A] A otimes[R] N
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
`baseChange A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R
] N`.

This "base change" operation is also known as "extension of scalars".
-/
def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f

@[simp]
/-
**LinearMap.baseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_tmul (a : A) (x : M) : f.baseChange A (a otimesₜ x) = a otimesₜ
 f x
参数：a : A；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem baseChange_tmul (a : A) (x : M) : f.baseChange A (a ⊗ₜ x) = a ⊗ₜ f x :=
  rfl
/-
**LinearMap.baseChange_eq_ltensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_eq_ltensor : (f.baseChange A : A otimes M -> A otimes N) = f.lT
ensor A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem baseChange_eq_ltensor : (f.baseChange A : A ⊗ M → A ⊗ N) = f.lTensor A :=
  rfl

@[simp]
/-
**LinearMap.baseChange_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `LinearMap.lTensor_add`：lTensor_add (f g : N ->ₗ[R] P) : (f + g).lTensor 
M = f.lTensor M + g.lTensor M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]

@[simp]
/-
**LinearMap.baseChange_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_zero : baseChange A (0 : M ->ₗ[R] N) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_zero : baseChange A (0 : M →ₗ[R] N) = 0 := by
  ext
  simp

@[simp]
/-
**LinearMap.baseChange_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_smul : (r • f).baseChange A = r • f.baseChange A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp

@[simp]
/-
**LinearMap.baseChange_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_id : (.id : M ->ₗ[R] M).baseChange A = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_id : (.id : M →ₗ[R] M).baseChange A = .id := by
  ext; simp
/-
**LinearMap.baseChange_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_comp (g : N ->ₗ[R] P) : (g ∘ₗ f).baseChange A = g.baseChange A 
∘ₗ f.baseChange A
参数：g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_comp (g : N →ₗ[R] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A := by
  ext; simp

open AlgebraTensorModule in
/-
**LinearMap.baseChange_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_baseChange {A B : Type*} [CommSemiring A] [Algebra R A] [Semiri
ng B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] (f : M ->ₗ[R] N) : ((f.b
aseChange A).baseChange B) = (cancelBaseChange R A B B N).symm ∘ₗ (f.baseChange 
B) ∘ₗ (cancelBaseChange R A B B M)
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_baseChange {A B : Type*} [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (f : M →ₗ[R] N) :
    ((f.baseChange A).baseChange B) =
    (cancelBaseChange R A B B N).symm ∘ₗ
      (f.baseChange B) ∘ₗ (cancelBaseChange R A B B M) := by
  ext; simp

variable (R M) in
@[simp]
/-
**LinearMap.baseChange_one** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_one : (1 : Module.End R M).baseChange A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.baseChange_id`：baseChange_id : (.id : M ->ₗ[R] M).baseChange A
 = .id
-/
lemma baseChange_one : (1 : Module.End R M).baseChange A = 1 := baseChange_id
/-
**LinearMap.baseChange_mul** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_mul (f g : Module.End R M) : (f * g).baseChange A = f.baseChang
e A * g.baseChange A
参数：f g : Module.End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_mul (f g : Module.End R M) :
    (f * g).baseChange A = f.baseChange A * g.baseChange A := by
  ext; simp

variable (R A M N)

/-- `baseChange` as a linear map.

When `M = N`, this is true more strongly as `Module.End.baseChangeHom`. -/
@[simps]
/-
**LinearMap.baseChangeHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：baseChangeHom : (M ->ₗ[R] N) ->ₗ[R] A otimes[R] M ->ₗ[A] A otimes[R] N whe
re toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.baseChange_add`：baseChange_add : (f + g).baseChange A = f.base
Change A + g.baseChange A
· 使用定理 `LinearMap.baseChange_smul`：baseChange_smul : (r • f).baseChange A = r • 
f.baseChange A

--- 原说明 ---
`baseChange` as a linear map.

When `M = N`, this is true more strongly as `Module.End.baseChangeHom`.
-/
def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul

/-- `baseChange` as an `AlgHom`. -/
@[simps!]
/-
**LinearMap._root_.Module.End.baseChangeHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`baseChange` as an `AlgHom`.
-/
def _root_.Module.End.baseChangeHom : Module.End R M →ₐ[R] Module.End A (A ⊗[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul
/-
**LinearMap.baseChange_pow** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_pow (f : Module.End R M) (n : Nat) : (f ^ n).baseChange A = f.b
aseChange A ^ n
参数：f : Module.End R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
lemma baseChange_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n

/-- `baseChange A e` for `e : M ≃ₗ[R] N` is the `A`-linear map `A ⊗[R] M ≃ₗ[A] A ⊗[R] N`. -/
/-
**LinearMap._root_.LinearEquiv.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`baseChange A e` for `e : M ≃ₗ[R] N` is the `A`-linear map `A ⊗[R] M ≃ₗ[A] A ⊗[R
] N`.
-/
def _root_.LinearEquiv.baseChange (e : M ≃ₗ[R] N) : A ⊗[R] M ≃ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.congr (.refl _ _) e

@[simp]
/-
**LinearMap._root_.LinearEquiv.coe_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.coe_baseChange (f : M ≃ₗ[R] N) :
    f.baseChange R A M N = f.toLinearMap.baseChange A :=
   rfl
/-
**LinearMap._root_.LinearEquiv.baseChange_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearEquiv.baseChange_tmul {e : M ≃ₗ[R] N} (a : A) (m : M) :
    e.baseChange R A M N (a ⊗ₜ m) = a ⊗ₜ e m :=
  rfl
/-
**LinearMap._root_.LinearEquiv.baseChange_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearEquiv.baseChange_symm_tmul {e : M ≃ₗ[R] N} (a : A) (n : N) :
    (e.baseChange R A).symm (a ⊗ₜ n) = a ⊗ₜ e.symm n :=
  rfl

@[simp]
/-
**LinearMap._root_.LinearEquiv.baseChange_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.baseChange_one :
    (1 : M ≃ₗ[R] M).baseChange R A M M = 1 := by
  ext x
  simp [← LinearEquiv.coe_toLinearMap]
/-
**LinearMap._root_.LinearEquiv.baseChange_trans** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.baseChange_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (e.trans f).baseChange R A M P = (e.baseChange R A M N).trans (f.baseChange R A N P) := by
  ext x
  simp only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, LinearEquiv.trans_apply,
    LinearEquiv.coe_trans, baseChange_eq_ltensor, lTensor_comp_apply]
/-
**LinearMap._root_.LinearEquiv.baseChange_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.baseChange_mul (e : M ≃ₗ[R] M) (f : M ≃ₗ[R] M) :
    (e * f).baseChange R A M M = (e.baseChange R A M M) * (f.baseChange R A M M) := by
  simp [LinearEquiv.mul_eq_trans, LinearEquiv.baseChange_trans]
/-
**LinearMap._root_.LinearEquiv.baseChange_symm** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.baseChange_symm (e : M ≃ₗ[R] N) :
    e.symm.baseChange R A N M = (e.baseChange R A M N).symm := by
  ext x
  rw [LinearEquiv.eq_symm_apply]
  simp [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange,
    baseChange_eq_ltensor, ← lTensor_comp_apply]
/-
**LinearMap._root_.LinearEquiv.baseChange_inv** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.baseChange_inv (e : M ≃ₗ[R] M) :
    (e⁻¹).baseChange R A M M = (e.baseChange R A M M)⁻¹ :=
  LinearEquiv.baseChange_symm R A M M e
/-
**LinearMap._root_.LinearEquiv.baseChange_pow** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.baseChange_pow (f : M ≃ₗ[R] M) (n : ℕ) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp [pow_succ, LinearEquiv.baseChange_mul, h]
/-
**LinearMap._root_.LinearEquiv.baseChange_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.baseChange_zpow (f : M ≃ₗ[R] M) (n : ℤ) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp only [zpow_add_one, LinearEquiv.baseChange_mul, h]
  | pred n h =>
    simp only [zpow_sub_one, LinearEquiv.baseChange_mul, h, LinearEquiv.baseChange_inv]

variable {R A M N} in
/-
**LinearMap.rTensor_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_baseChange (φ : A ->ₐ[R] B) (t : A otimes[R] M) (f : M ->ₗ[R] N) :
 (φ.toLinearMap.rTensor N) (f.baseChange A t) = (f.baseChange B) (φ.toLinearMap.
rTensor M t)
参数：φ : A ->ₐ[R] B；t : A otimes[R] M；f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensor_baseChange (φ : A →ₐ[R] B) (t : A ⊗[R] M) (f : M →ₗ[R] N) :
    (φ.toLinearMap.rTensor N) (f.baseChange A t) =
      (f.baseChange B) (φ.toLinearMap.rTensor M t) := by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M →ₗ[R] N)

@[simp]
/-
**LinearMap.baseChange_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  simp [tmul_sub]

@[simp]
/-
**LinearMap.baseChange_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：baseChange_neg : (-f).baseChange A = -f.baseChange A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `TensorProduct.tmul_neg`：tmul_neg (m : M) (p : P) : m otimesₜ (-p) = -m o
timesₜ[R] p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  simp [tmul_neg]

end Ring

end LinearMap

namespace Submodule

open TensorProduct

variable {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (p q : Submodule R M)

/-- If `A` is an `R`-algebra, any `R`-submodule `p` of an `R`-module `M` may be pushed forward to
an `A`-submodule of `A ⊗ M`.

This "base change" operation is also known as "extension of scalars". -/
/-
**Submodule.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：baseChange : Submodule A (A otimes[R] M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
If `A` is an `R`-algebra, any `R`-submodule `p` of an `R`-module `M` may be push
ed forward to
an `A`-submodule of `A ⊗ M`.

This "base change" operation is also known as "extension of scalars".
-/
def baseChange : Submodule A (A ⊗[R] M) :=
  LinearMap.range (p.subtype.baseChange A)

variable {A p} in
/-
**Submodule.tmul_mem_baseChange_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m in p) : a otimesₜ[R] m 
in p.baseChange A
参数：a : A；hm : m in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m ∈ p) :
    a ⊗ₜ[R] m ∈ p.baseChange A :=
  ⟨a ⊗ₜ[R] ⟨m, hm⟩, rfl⟩
/-
**Submodule.baseChange_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：baseChange_eq_span : p.baseChange A = span A (p.map (TensorProduct.mk R A 
M 1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.baseChange.eq_1`：∀ {R : Type u_1} {M : Type u_2} (A : Type u_3
) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3
 : AddCommMonoi…
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_top_of_span_eq_top`：span_eq_top_of_span_eq_top (s : Se
t M) (hs : span R s = ⊤) : span S s = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `LinearMap.baseChange_tmul`：baseChange_tmul (a : A) (x : M) : f.baseChang
e A (a otimesₜ x) = a otimesₜ f x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma baseChange_eq_span : p.baseChange A = span A (p.map (TensorProduct.mk R A M 1)) := by
  refine le_antisymm ?_ ?_
  · rw [baseChange, LinearMap.range_le_iff_comap, eq_top_iff,
      ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..), span_le]
    refine fun _ ⟨a, m, h⟩ ↦ ?_
    rw [← h, SetLike.mem_coe, mem_comap, LinearMap.baseChange_tmul, ← mul_one a, ← smul_eq_mul,
      ← smul_tmul']
    exact smul_mem _ a (subset_span ⟨m, m.2, rfl⟩)
  · refine span_le.2 fun _ ⟨m, hm, h⟩ ↦ h ▸ ⟨1 ⊗ₜ[R] ⟨m, hm⟩, rfl⟩

@[simp]
/-
**Submodule.baseChange_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：baseChange_bot : (⊥ : Submodule R M).baseChange A = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.baseChange_eq_span`：baseChange_eq_span : p.baseChange A = span
 A (p.map (TensorProduct.mk R A M 1))
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_bot : (⊥ : Submodule R M).baseChange A = ⊥ := by simp [baseChange_eq_span]

@[simp]
/-
**Submodule.baseChange_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：baseChange_top : (⊤ : Submodule R M).baseChange A = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_eq_top_of_span_eq_top`：span_eq_top_of_span_eq_top (s : Se
t M) (hs : span R s = ⊤) : span S s = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `Submodule.tmul_mem_baseChange_of_mem`：tmul_mem_baseChange_of_mem (a : A)
 {m : M} (hm : m in p) : a otimesₜ[R] m in p.baseChange A
· 使用定理 `trivial`：True
-/
lemma baseChange_top : (⊤ : Submodule R M).baseChange A = ⊤ := by
  rw [eq_top_iff, ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..)]
  exact span_le.2 fun _ ⟨a, m, h⟩ ↦ h ▸ tmul_mem_baseChange_of_mem _ trivial

variable {p q} in
/-
**Submodule.baseChange_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：baseChange_mono (h : p <= q) : p.baseChange A <= q.baseChange A
参数：h : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.baseChange.eq_1`：∀ {R : Type u_1} {M : Type u_2} (A : Type u_3
) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3
 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.baseChange.eq_1`：∀ {R : Type u_1} (A : Type u_2) {M : Type u_4
} {N : Type u_5} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Algeb
ra R A] [inst_3…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subtype_comp_inclusion`：subtype_comp_inclusion (p q : Submodul
e R M) (h : p <= q) : q.subtype.comp (inclusion h) = p.subtype
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.map_comp`：map_comp (f₂ : P ->ₗ[A] P') 
(f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q) : map (f₂.comp f₁) (g₂.co
mp g₁) = (map f₂ g₂).comp (map f…
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…
-/
theorem baseChange_mono (h : p ≤ q) : p.baseChange A ≤ q.baseChange A := by
  rw [baseChange, LinearMap.baseChange, ← subtype_comp_inclusion p q h,
    ← LinearMap.id_comp LinearMap.id, AlgebraTensorModule.map_comp]
  apply LinearMap.range_comp_le_range

@[simp]
/-
**Submodule.baseChange_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：baseChange_span (s : Set M) : (span R s).baseChange A = span A (TensorProd
uct.mk R A M 1 '' s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.baseChange_eq_span`：baseChange_eq_span : p.baseChange A = span
 A (p.map (TensorProduct.mk R A M 1))
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma baseChange_span (s : Set M) :
    (span R s).baseChange A = span A (TensorProduct.mk R A M 1 '' s) := by
  rw [baseChange_eq_span, map_span, span_span_of_tower]

/-- Given an `R`-submodule `p` of `M`, and `R`-algebra `A`, we obtain an `A`-submodule of
`A ⊗[R] M` by `p.baseChange A`. This is then the surjective `A`-linear map
`A ⊗[R] M → p.baseChange A`. -/
/-
**Submodule.toBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toBaseChange : A otimes[R] p ->ₗ[A] p.baseChange A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Given an `R`-submodule `p` of `M`, and `R`-algebra `A`, we obtain an `A`-submodu
le of
`A ⊗[R] M` by `p.baseChange A`. This is then the surjective `A`-linear map
`A ⊗[R] M → p.baseChange A`.
-/
def toBaseChange : A ⊗[R] p →ₗ[A] p.baseChange A :=
  LinearMap.rangeRestrict _
/-
**Submodule.coe_toBaseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} (A : Type u_3) [inst : CommSemiring R] [in
st_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : AddCommMonoid M] [inst_4 :
 _root_.Module R M] (p : Submodule R M) (a : A) (x : ↥p),   ↑((Submodule.toBaseC
hange A p) (a ⊗ₜ[R] x)) = a ⊗ₜ[R] ↑x
参数：A : Type u_3；p : Submodule R M；a : A；x : ↥p；(Submodule.toBaseChange A p) (a ⊗
ₜ[R] x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma coe_toBaseChange_tmul (a : A) (x : p) :
    (p.toBaseChange A (a ⊗ₜ x) : A ⊗[R] M) = a ⊗ₜ (x : M) := rfl
/-
**Submodule.toBaseChange_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toBaseChange_surjective : Function.Surjective (p.toBaseChange A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.surjective_rangeRestrict`：surjective_rangeRestrict : Surjectiv
e f.rangeRestrict
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma toBaseChange_surjective : Function.Surjective (p.toBaseChange A) :=
  LinearMap.surjective_rangeRestrict _

/-- This version enables better pattern matching via the tactic `obtain`. -/
/-
**Submodule.toBaseChange_surjective'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toBaseChange_surjective' {y : A otimes[R] M} (hy : y in p.baseChange A) : 
exists x : A otimes[R] p, p.toBaseChange A x = y
参数：hy : y in p.baseChange A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Submodule.toBaseChange_surjective`：toBaseChange_surjective : Function.Su
rjective (p.toBaseChange A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This version enables better pattern matching via the tactic `obtain`.
-/
lemma toBaseChange_surjective' {y : A ⊗[R] M} (hy : y ∈ p.baseChange A) :
    ∃ x : A ⊗[R] p, p.toBaseChange A x = y := by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

end Submodule

namespace TensorProduct.AlgebraTensorModule

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]

/-
**TensorProduct.AlgebraTensorModule.baseChange_comp_cancelBaseChange_symm_self**
 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：baseChange_comp_cancelBaseChange_symm_self (f : (A otimes[R] M) ->ₗ[A] N) 
: f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm = (TensorProduct.lid A N).
symm ∘ₗ f
参数：f : (A otimes[R] M) ->ₗ[A] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.AlgebraTensorModule.cancelBaseChange_self_eq_lid`：cancelBa
seChange_self_eq_lid : cancelBaseChange R A A A N = TensorProduct.lid A (A otime
s[R] N)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma baseChange_comp_cancelBaseChange_symm_self (f : (A ⊗[R] M) →ₗ[A] N) :
    f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm = (TensorProduct.lid A N).symm ∘ₗ f := by
  rw [cancelBaseChange_self_eq_lid]
  ext x
  simp
/-
**TensorProduct.AlgebraTensorModule.ker_baseChange_comp_cancelBaseChange_symm** 
是 Mathlib 中的一个引理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：ker_baseChange_comp_cancelBaseChange_symm (f : (A otimes[R] M) ->ₗ[A] N) :
 (f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm).ker = f.ker
参数：f : (A otimes[R] M) ->ₗ[A] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TensorProduct.AlgebraTensorModule.baseChange_comp_cancelBaseChange_symm_
self`：baseChange_comp_cancelBaseChange_symm_self (f : (A otimes[R] M) ->ₗ[A] N) 
: f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm = (TensorPro…
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
-/
lemma ker_baseChange_comp_cancelBaseChange_symm (f : (A ⊗[R] M) →ₗ[A] N) :
    (f.baseChange A ∘ₗ (cancelBaseChange R A A A M).symm).ker = f.ker := by
  rw [baseChange_comp_cancelBaseChange_symm_self, LinearMap.ker_comp,
    LinearEquiv.ker, Submodule.comap_bot]

end TensorProduct.AlgebraTensorModule

