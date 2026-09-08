/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Monoid algebras commute with base change

In this file we show that monoid algebras are stable under pushout.
-/

@[expose] public noncomputable section

open Algebra TensorProduct

namespace MonoidAlgebra
variable {R M N S A B : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [IsScalarTower R S A]
  [CommMonoid M] [CommMonoid N]

-- Note: Cannot be additivised automatically because of the use of `Multiplicative`
-- in `AddMonoidAlgebra.liftNCAlgHom` and `of`
/-- Implementation detail. -/
/-
**MonoidAlgebra._root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun** 是 Mathlib 
中的一个定义，位于命名空间 `MonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail.
-/
noncomputable def _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun [AddCommMonoid M] :
    AddMonoidAlgebra (A ⊗[R] B) M →ₐ[S] A ⊗[R] AddMonoidAlgebra B M :=
  AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ ↦ .all ..

/-- Implementation detail. -/
@[to_additive existing (dont_translate := R)]
/-
**MonoidAlgebra.rTensorEquivAlgEquiv.invFun** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlg
ebra.rTensorEquivAlgEquiv`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {S : Type u_4} →       {A : Type u
_5} →         {B : Type u_6} →           [inst : CommSemiring R] →             [
inst_1 : CommSemiring S] →               [inst_2 : CommSemiring A] →            
     [inst_3 : CommSemiring B] →                   [inst_4 : Algebra R S] →     
                [inst_5 : Algebra R A] →                       [inst_6 : Algebra
 R B] →                         [inst_7 : Algebra S A] →                        
   [inst_8 : IsScalarTower R S A] →                             [inst_9 : CommMo
noid M] →                               MonoidAlgebra (TensorProduct R A B) M →ₐ
[S] TensorProduct R A (MonoidAlgebra B M)
参数：TensorProduct R A B；MonoidAlgebra B M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail.
-/
def rTensorEquivAlgEquiv.invFun : (A ⊗[R] B)[M] →ₐ[S] A ⊗[R] B[M] :=
  MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ ↦ .all ..

omit [CommMonoid M] in
variable (R A B) [AddCommMonoid M] in
/-
**MonoidAlgebra._root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul** 是 Mat
hlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun (S := S) (.single m (a ⊗ₜ[R] b)) =
       a ⊗ₜ .single m b := by
  simp [AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun]

@[to_additive existing (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Mono
idAlgebra.rTensorEquivAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {S : Type u_4} {A : Type u_5} {B : Type u_
6} [inst : CommSemiring R]   [inst_1 : CommSemiring S] [inst_2 : CommSemiring A]
 [inst_3 : CommSemiring B] [inst_4 : Algebra R S]   [inst_5 : Algebra R A] [inst
_6 : Algebra R B] [inst_7 : Algebra S A] [inst_8 : IsScalarTower R S A]   [inst_
9 : CommMonoid M] (a : A) (m : M) (b : B),   MonoidAlgebra.rTensorEquivAlgEquiv.
invFun (MonoidAlgebra.single m (a ⊗ₜ[R] b)) = a ⊗ₜ[R] MonoidAlgebra.single m b
参数：a : A；m : M；b : B；MonoidAlgebra.single m (a ⊗ₜ[R] b)。
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
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.singleOneAlgHom_apply`：∀ {R : Type u_1} {A : Type u_4} {M 
: Type u_7} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]
   [inst_3 : Monoid M] (a…
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `MonoidAlgebra.single_mul_single`：single_mul_single (m₁ m₂ : M) (r₁ r₂ : 
R) : single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    rTensorEquivAlgEquiv.invFun (S := S) (single m (a ⊗ₜ[R] b)) = a ⊗ₜ single m b := by
  simp [rTensorEquivAlgEquiv.invFun]

variable (R S A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R S A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
/-
**MonoidAlgebra.rTensorEquivAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：rTensorEquivAlgEquiv : A otimes[R] B[M] ≃ₐ[S] (A otimes[R] B)[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def rTensorEquivAlgEquiv : A ⊗[R] B[M] ≃ₐ[S] (A ⊗[R] B)[M] := by
  refine .restrictScalars S <| .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A ⊗[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapAlgHom _ Algebra.TensorProduct.includeRight) fun p n ↦ .all ..)
      rTensorEquivAlgEquiv.invFun ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext
    simp
  · ext : 1
    apply AlgHom.toLinearMap_injective
    ext
    simp

@[to_additive (dont_translate := R A B) (attr := simp)]
/-
**MonoidAlgebra.rTensorEquiv_tmulAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：rTensorEquiv_tmulAlgEquiv (a : A) (p : B[M]) : rTensorEquivAlgEquiv R S A 
B (a otimesₜ p) = a • mapAlgHom M Algebra.TensorProduct.includeRight p
参数：a : A；p : B[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rTensorEquiv_tmulAlgEquiv (a : A) (p : B[M]) :
    rTensorEquivAlgEquiv R S A B (a ⊗ₜ p) =
      a • mapAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [rTensorEquivAlgEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]
/-
**MonoidAlgebra.rTensorEquiv_symm_singleAlgEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Mono
idAlgebra`。
形式化陈述：rTensorEquiv_symm_singleAlgEquiv (m : M) (a : A) (b : B) : (rTensorEquivAl
gEquiv R S A B).symm (single m (a otimesₜ b)) = a otimesₜ single m b
参数：m : M；a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul`：∀ {R : Type u_1} {M : Ty
pe u_2} {S : Type u_4} {A : Type u_5} {B : Type u_6} [inst : CommSemiring R]   [
inst_1 : CommSemiring S] [inst_2 : C…
-/
lemma rTensorEquiv_symm_singleAlgEquiv (m : M) (a : A) (b : B) :
    (rTensorEquivAlgEquiv R S A B).symm (single m (a ⊗ₜ b)) = a ⊗ₜ single m b :=
  rTensorEquivAlgEquiv.invFun_tmul ..

variable (R A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
/-
**MonoidAlgebra.lTensorAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：lTensorAlgEquiv : A[M] otimes[R] B ≃ₐ[R] (A otimes[R] B)[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def lTensorAlgEquiv : A[M] ⊗[R] B ≃ₐ[R] (A ⊗[R] B)[M] :=
  (Algebra.TensorProduct.comm ..).trans <| (rTensorEquivAlgEquiv _ _ _ _).trans <|
    mapAlgEquiv _ _ <| Algebra.TensorProduct.comm ..

@[to_additive (dont_translate := R A B) (attr := simp)]
/-
**MonoidAlgebra.lTensorAlgEquiv_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：lTensorAlgEquiv_symm_single (m : M) (a : A) (b : B) : (lTensorAlgEquiv R A
 B).symm (single m (a otimesₜ b)) = single m a otimesₜ b
参数：m : M；a : A；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `MonoidAlgebra.mapAlgEquiv_apply`：∀ (R : Type u_1) {A : Type u_4} {B : Ty
pe u_5} (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用引理 `MonoidAlgebra.rTensorEquiv_symm_singleAlgEquiv`：rTensorEquiv_symm_single
AlgEquiv (m : M) (a : A) (b : B) : (rTensorEquivAlgEquiv R S A B).symm (single m
 (a otimesₜ b)) = a otimesₜ single m…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lTensorAlgEquiv_symm_single (m : M) (a : A) (b : B) :
    (lTensorAlgEquiv R A B).symm (single m (a ⊗ₜ b)) = single m a ⊗ₜ b := by
  simp [lTensorAlgEquiv]

variable (R A) in
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/
@[to_additive (dont_translate := R A)
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/]
/-
**MonoidAlgebra.scalarTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：scalarTensorEquiv : A otimes[R] R[M] ≃ₐ[A] A[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def scalarTensorEquiv : A ⊗[R] R[M] ≃ₐ[A] A[M] :=
  (rTensorEquivAlgEquiv ..).trans <| mapAlgEquiv A M <| Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (attr := simp)]
/-
**MonoidAlgebra.scalarTensorEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：scalarTensorEquiv_tmul (a : A) (p : R[M]) : scalarTensorEquiv R A (a otime
sₜ p) = a • mapAlgHom M (Algebra.ofId ..) p
参数：a : A；p : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MonoidAlgebra.rTensorEquiv_tmulAlgEquiv`：rTensorEquiv_tmulAlgEquiv (a : 
A) (p : B[M]) : rTensorEquivAlgEquiv R S A B (a otimesₜ p) = a • mapAlgHom M Alg
ebra.TensorProduct.includeRig…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MonoidAlgebra.mapAlgEquiv_apply`：∀ (R : Type u_1) {A : Type u_4} {B : Ty
pe u_5} (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用引理 `MonoidAlgebra.coeff_mapRingHom`：coeff_mapRingHom (f : R ->+* S) (x : R[M
]) (m : M) : (mapRingHom M f x).coeff m = f (x.coeff m)
· 使用引理 `MonoidAlgebra.coeff_mapAlgHom`：coeff_mapAlgHom (f : A ->ₐ[R] B) (x : A[M
]) (m : M) : (mapAlgHom M f x).coeff m = f (x.coeff m)
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scalarTensorEquiv_tmul (a : A) (p : R[M]) :
    scalarTensorEquiv R A (a ⊗ₜ p) = a • mapAlgHom M (Algebra.ofId ..) p := by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (attr := simp)]
/-
**MonoidAlgebra.scalarTensorEquiv_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidA
lgebra`。
形式化陈述：scalarTensorEquiv_symm_single (m : M) (a : A) : (scalarTensorEquiv R A).sy
mm (single m a) = a otimesₜ single m 1
参数：m : M；a : A。
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `MonoidAlgebra.mapAlgEquiv_apply`：∀ (R : Type u_1) {A : Type u_4} {B : Ty
pe u_5} (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用引理 `MonoidAlgebra.mapRingHom_single`：mapRingHom_single (f : R ->+* S) (a : M
) (b : R) : mapRingHom M f (single a b) = single a (f b)
· 使用引理 `MonoidAlgebra.rTensorEquiv_symm_singleAlgEquiv`：rTensorEquiv_symm_single
AlgEquiv (m : M) (a : A) (b : B) : (rTensorEquivAlgEquiv R S A B).symm (single m
 (a otimesₜ b)) = a otimesₜ single m…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scalarTensorEquiv_symm_single (m : M) (a : A) :
    (scalarTensorEquiv R A).symm (single m a) = a ⊗ₜ single m 1 := by simp [scalarTensorEquiv]

open scoped AlgebraMonoidAlgebra

variable [Algebra S B] [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B]

@[to_additive (dont_translate := R S B)]
/-
**MonoidAlgebra.instIsPushout** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instIsPushout [IsPushout R S A B] : IsPushout R S A[M] B[M] where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.isScalarTower_monoidAlgebra`：isScalarTower_monoidAlgebra [
CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] : IsScalarTowe
r R S[M] T[M]
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MonoidAlgebra.induction_linear`：induction_linear {motive : R[M] -> Prop}
 (x : R[M]) (zero : motive 0) (add : forall x y : R[M], motive x -> motive y -> 
motive (x + y)) (sin…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `MonoidAlgebra.mapAlgEquiv_apply`：∀ (R : Type u_1) {A : Type u_4} {B : Ty
pe u_5} (M : Type u_7) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MonoidAlgebra.rTensorEquiv_tmulAlgEquiv`：rTensorEquiv_tmulAlgEquiv (a : 
A) (p : B[M]) : rTensorEquivAlgEquiv R S A B (a otimesₜ p) = a • mapAlgHom M Alg
ebra.TensorProduct.includeRig…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 37 条，此处仅展示前 30 条）
-/
instance instIsPushout [IsPushout R S A B] : IsPushout R S A[M] B[M] where
  out := .of_equiv ((rTensorEquivAlgEquiv R S S A (M := M)).trans <|
      mapAlgEquiv S M <| IsPushout.equiv R S A B).toLinearEquiv fun x ↦ by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.instIsPushout'** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instIsPushout' [IsPushout R A S B] : IsPushout R A[M] S B[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用引理 `MonoidAlgebra.isScalarTower_monoidAlgebra`：isScalarTower_monoidAlgebra [
CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T] : IsScalarTowe
r R S[M] T[M]
-/
instance instIsPushout' [IsPushout R A S B] : IsPushout R A[M] S B[M] :=
  have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

omit [CommMonoid M] [CommMonoid N]

-- TODO: Generalise to different base rings, strengthen to an `AlgEquiv`
variable (R) in
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/
@[to_additive (dont_translate := R) (attr := simps! apply_coeff)
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/]
/-
**MonoidAlgebra.tensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：tensorEquiv : R[M] otimes[R] R[N] ≃ₗ[R] R[M × N]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def tensorEquiv : R[M] ⊗[R] R[N] ≃ₗ[R] R[M × N] :=
  TensorProduct.congr (coeffLinearEquiv _) (coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' .. ≪≫ₗ (coeffLinearEquiv _).symm

@[to_additive (dont_translate := R) (attr := simp)]
/-
**MonoidAlgebra.tensorEquiv_single_tmul_single** 是 Mathlib 中的一个引理，位于命名空间 `Monoid
Algebra`。
形式化陈述：tensorEquiv_single_tmul_single (m : M) (r₁ : R) (n : N) (r₂ : R) : tensorE
quiv R (single m r₁ otimesₜ single n r₂) = single (m, n) (r₁ * r₂)
参数：m : M；r₁ : R；n : N；r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeff_tensorEquiv_apply`：∀ (R : Type u_1) {M : Type u_2} {
N : Type u_3} [inst : CommSemiring R]   (x : TensorProduct R (MonoidAlgebra R M)
 (MonoidAlgebra R N)),   ((…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `finsuppTensorFinsupp'_single_tmul_single`：∀ (R : Type u_1) (ι : Type u_5
) (κ : Type u_6) [inst : CommSemiring R] (a : ι) (b : κ) (r₁ r₂ : R),   (finsupp
TensorFinsupp' R ι κ) ((fun₀ |…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorEquiv_single_tmul_single (m : M) (r₁ : R) (n : N) (r₂ : R) :
    tensorEquiv R (single m r₁ ⊗ₜ single n r₂) = single (m, n) (r₁ * r₂) := by ext; simp

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.tensorEquiv_symm_single_eq_single_one_tmul** 是 Mathlib 中的一个引理，位于
命名空间 `MonoidAlgebra`。
形式化陈述：tensorEquiv_symm_single_eq_single_one_tmul (mn : M × N) (r : R) : (tensorE
quiv R).symm (single mn r) = single mn.1 1 otimesₜ single mn.2 r
参数：mn : M × N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_single_one_tmul`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorEquiv_symm_single_eq_single_one_tmul (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 1 ⊗ₜ single mn.2 r := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.tensorEquiv_symm_single_eq_tmul_single_one** 是 Mathlib 中的一个引理，位于
命名空间 `MonoidAlgebra`。
形式化陈述：tensorEquiv_symm_single_eq_tmul_single_one (mn : M × N) (r : R) : (tensorE
quiv R).symm (single mn r) = single mn.1 r otimesₜ single mn.2 1
参数：mn : M × N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `finsuppTensorFinsupp'_symm_single_eq_tmul_single_one`：∀ (R : Type u_1) (
ι : Type u_5) (κ : Type u_6) [inst : CommSemiring R] (i : ι × κ) (r : R),   ((fi
nsuppTensorFinsupp' R ι κ).symm fun₀ | i =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorEquiv_symm_single_eq_tmul_single_one (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 r ⊗ₜ single mn.2 1 := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

end MonoidAlgebra

end

